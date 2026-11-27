module

import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Lib.Cohomology.TorsionTheories
public import Lib.PadicComparison.Descent.AlmostDescent
public import Lib.PadicComparison.HodgeTate.GenericFibre
import Lib.Cohomology.LerayHirsch
import Lib.PadicComparison.Completion
import Lib.PadicComparison.Descent.TestCovers
public import Lib.PadicComparison.Primitive.PeriodCoefficients
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Lib.Cohomology.ProperBaseChange.Theorem
import Lib.Cohomology.Etale.DenseSubfunctors

section
/-!
# The perfect projective line glued from two perfect discs has the cohomology of a point

The perfect projective line on p-adic tests S is a model on which classes on ℙ¹ are computed. Its
two discs are represented in the tilt S^♭ by O^♭[ℚ≥0], and its torus by O^♭[ℚ].

* `New.Variety.PerfectLine.gluing`: the gluing map ℤ[torus ⊔ point] → ℤ[two discs]; it is injective
  (a monomorphism). Its cokernel plays the role of the perfect line with the point ∞ killed.
* `New.Variety.PerfectLine.oneSub_comp_gluing`: the operators 1 − (T^s ↦ χ(s) T^s) commute with the
  gluing map.
* `New.Variety.PerfectLine.isCohomEquiv_tensorCoeff_gluing`,
  `New.Variety.PerfectLine.isCohomEquiv_gluing_generic`: over each test c the gluing map induces
  bijections on cohomology. This holds for coefficients G(S^♭), where G is built from an O^♭-module
  N and is assumed acyclic on perfect rings. It also holds for S[1/p].
* `New.Variety.PerfectLine.subsingleton_H_cokernel_gluing`: then M ⊗ cokernel has no cohomology, for
  every M with flat values.

Idea: all cohomology is in degree 0, where the map is the splitting of a Laurent polynomial into two
parts according to the sign of the exponent. `New.Period.OFlat` is O^♭, the tilt of the ring of
integers O_C of ℂ_p.

Notions from other files:
* `New.Variety.PadicTest`: A p-adic test: a non-empty family of cells (`New.Variety.IsCell`) with a
  ring map from O_C to their product.
* `New.Variety.freeAb`: The functor sending a set-valued functor Y to Z[Y], whose value at A is the
  free abelian group on Y(A). ℤ[Y] has flat base change (`HasFlatBaseChange`) when tensoring by a
  flat module M commutes with its cohomology with module coefficients.

## Relation to the literature

Known; see `Lib.Cohomology.ProjectiveLine.ConstantLineFormula` for sources.
-/

@[expose] public section

noncomputable section

namespace New.Variety

open CategoryTheory Function AddMonoidAlgebra Period MonoidalCategory PadicTest NNRat
open CommAlgCat hiding of

/-- The objectwise tensor product of two functors with flat values has flat values. -/
instance {C : Type 1} [Category C] {F A : AbFunctor C} [HasFlatValues F] [HasFlatValues A] :
    HasFlatValues (abTensor F A) := by
  refine ⟨fun c ↦ ?_⟩
  -- The field `HasFlatValues.flat` is not an instance, so the two facts are stated here.
  have h_flat_F : Module.Flat ℤ (F.obj c) := HasFlatValues.flat c
  have h_flat_A : Module.Flat ℤ (A.obj c) := HasFlatValues.flat c
  exact .instTensorProduct

namespace PerfectLine

variable {p : ℕ} [ThePrime p]
  (χ : Multiplicative ℚ →* OFlat) {S : Type} [AddCommMonoid S]
  (f : S →+ ℚ) (g : ℚ≥0 →+ ℚ) {b b' : CommAlg OFlat} (a : ULift.{1} Bool)
  (X : PadicTest ⥤ Type 1 := onePointFunctor PadicTest)

/-! ### The discs, the torus and the gluing map -/

/-- For an additive commutative monoid S, the monoid algebra O^♭[S], as a commutative
O^♭-algebra. -/
abbrev monoidAlg (S : Type) [AddCommMonoid S] : CommAlgCat OFlat := CommAlgCat.of OFlat OFlat[S]

/-- For a character χ of ℚ with values in O^♭ and an additive map f: S → ℚ, the O^♭-algebra
endomorphism T^s ↦ χ(f(s)) T^s of O^♭[S]. -/
def charTwist : monoidAlg S ⟶ monoidAlg S :=
  ofHom (lift OFlat OFlat[S] S
    ((algebraMap OFlat OFlat[S]).toMonoidHom.comp (χ.comp f.toMultiplicative) * of OFlat S))

/-- For an additive map g: ℚ≥0 → ℚ, the map of monoid algebras O^♭[ℚ≥0] → O^♭[ℚ] over O^♭
sending T^a to T^{g(a)}. -/
abbrev discToTorus : monoidAlg ℚ≥0 ⟶ monoidAlg ℚ := ofHom (mapDomainAlgHom OFlat OFlat g)

/-- Evaluation at T = 0: the O^♭-algebra map from O^♭[ℚ_{≥0}] to b sending T^0 to 1 and T^a to 0
for a > 0. -/
abbrev evalZero (b : CommAlgCat OFlat) : monoidAlg ℚ≥0 ⟶ b :=
  ofHom (lift OFlat b ℚ≥0 ⟨⟨fun s ↦ if s = 1 then 1 else 0, ite_eq_left rfl⟩, by aesop⟩)

variable (B : ULift.{1} Bool → CommAlg OFlat)
  (ψ : CommAlg OFlat ⥤ CommAlg OFlat := 𝟭 (CommAlg OFlat))

/-- The family of two `O^♭`-algebras: the ring `O^♭[ℚ]` of the perfect torus at the index `true`,
and the ring `O^♭` of a point at the index `false`. -/
def pointOrTorus : ULift.{1} Bool → CommAlg OFlat
  | ⟨true⟩ => monoidAlg ℚ
  | ⟨false⟩ => CommAlgCat.of OFlat OFlat

lemma pointOrTorus_true : pointOrTorus ⟨true⟩ = monoidAlg ℚ := rfl

/-- For O^♭-algebras B_i indexed by Bool and an endofunctor ψ of O^♭-algebras (default the
identity), the functor S ↦ ⊔_i Hom(ψ(B_i), S^♭) on p-adic tests. -/
abbrev tiltPointsSum : PadicTest ⥤ Type 1 := sigma fun a ↦ tilt ⋙ reprBy (ψ (B a))

/-- Two affine lines with all roots of the coordinate: for an endofunctor ψ of O^♭-algebras (default
the identity), the disjoint union of two copies of the functor of points of ψ(O^♭[ℚ_{≥0}]) in the
tilts of p-adic tests. -/
abbrev twoDiscs : PadicTest ⥤ Type 1 := tiltPointsSum (fun _ ↦ monoidAlg ℚ≥0) ψ

/-- The map ℤ[torus ⊔ point] → ℤ[two discs] sending a point t of the torus to t⁻¹ in the disc
`false` minus t in the disc `true`, and the point to the origin of the disc `false`. -/
abbrev gluing : freeAb (tiltPointsSum pointOrTorus ψ) ⟶ freeAb (twoDiscs ψ) :=
  freeAb.desc
    (fun
      | _, ⟨⟨true⟩, t⟩ =>
        .of ⟨⟨false⟩, ⟨ψ.map (discToTorus (-coeHom)) ≫ t.down⟩⟩ -
          .of ⟨⟨true⟩, ⟨ψ.map (discToTorus coeHom) ≫ t.down⟩⟩
      | _, ⟨⟨false⟩, t⟩ =>
        FreeAddCommGroup.of ⟨⟨false⟩, ⟨ψ.map (evalZero (pointOrTorus { down := false })) ≫ t.down⟩⟩)
    (by bound)

private def ofTorus {ψ : CommAlg OFlat ⥤ CommAlg OFlat} {A : PadicTest}
    (t : ψ (monoidAlg ℚ) ⟶ tilt A) : (freeAb (tiltPointsSum pointOrTorus ψ)).obj A :=
  FreeAddCommGroup.of ⟨⟨true⟩, ⟨t⟩⟩

private def ofPoint {ψ : CommAlg OFlat ⥤ CommAlg OFlat} {A : PadicTest}
    (t : ψ (CommAlgCat.of OFlat OFlat) ⟶ tilt A) :
    (freeAb (tiltPointsSum pointOrTorus ψ)).obj A :=
  FreeAddCommGroup.of ⟨⟨false⟩, ⟨t⟩⟩

private def ofDisc {ψ : CommAlg OFlat ⥤ CommAlg OFlat} {A : PadicTest}
    (b : ULift.{1} Bool) (t : ψ (monoidAlg ℚ≥0) ⟶ tilt A) : (freeAb (twoDiscs ψ)).obj A :=
  FreeAddCommGroup.of ⟨b, ⟨t⟩⟩

private lemma gluing_ofTorus (ψ : CommAlg OFlat ⥤ CommAlg OFlat) (A : PadicTest)
    (t : ψ (monoidAlg ℚ) ⟶ tilt A) :
    (gluing ψ).app A (ofTorus t) =
      ofDisc ⟨false⟩ (ψ.map (discToTorus (-coeHom)) ≫ t) -
        ofDisc ⟨true⟩ (ψ.map (discToTorus coeHom) ≫ t) :=
  freeAb.desc_of (Y := tiltPointsSum pointOrTorus ψ) _ _ A ⟨⟨true⟩, ⟨t⟩⟩

private lemma gluing_ofPoint (ψ : CommAlg OFlat ⥤ CommAlg OFlat) (A : PadicTest)
    (t : ψ (CommAlgCat.of OFlat OFlat) ⟶ tilt A) :
    (gluing ψ).app A (ofPoint t) =
      ofDisc ⟨false⟩ (ψ.map (evalZero (CommAlgCat.of OFlat OFlat)) ≫ t) :=
  freeAb.desc_of (Y := tiltPointsSum pointOrTorus ψ) _ _ A ⟨⟨false⟩, ⟨t⟩⟩

@[simp]
lemma evalZero_comp (g : b ⟶ b') : evalZero b ≫ g = evalZero b' := by aesop

variable {B : ULift.{1} Bool → CommAlg OFlat} (Δ : ∀ b : ULift.{1, 0} Bool, B b ⟶ B b)
  {N : ModuleCat OFlat}

/-! ### Origins, the operator 1 − Δ, and injectivity of the gluing map -/

/-- For a set-valued functor X on p-adic tests (by default the point), the morphism
ℤ[X] → ℤ[two discs] sending every point to the origin T = 0 of the disc with index a. -/
abbrev origin : freeAb X ⟶ freeAb twoDiscs :=
  freeAb.desc (fun _ _ ↦ FreeAddCommGroup.of ⟨a, ⟨evalZero _⟩⟩) fun _ _ _ _ ↦ by
    congr
    simp

/-- The map ℤ[Hom(B_true, S^♭) ⊔ Hom(B_false, S^♭)] → ℤ[Hom(B_true, S^♭)] that keeps the points
of the first part and sends those of the second to 0. -/
abbrev projFirst : freeAb (tiltPointsSum B) ⟶ freeAb (tilt ⋙ reprBy (B ⟨true⟩)) :=
  freeAb.desc (fun | _, ⟨⟨true⟩, t⟩ => FreeAddCommGroup.of t | _, ⟨⟨false⟩, _⟩ => 0) (by bound)

/-- The projection kills a generator of the false summand. -/
lemma projFirst_false (c : PadicTest)
    (t : (tilt ⋙ reprBy (B ⟨false⟩)).obj c) :
    ((projFirst (B := B)).app c).hom (.of (⟨⟨false⟩, t⟩ : (tiltPointsSum B).obj c)) = 0 :=
  freeAb.desc_of ..

/-- The projection preserves a generator of the true summand. -/
lemma projFirst_true (c : PadicTest)
    (t : (tilt ⋙ reprBy (B ⟨true⟩)).obj c) :
    ((projFirst (B := B)).app c).hom (.of (⟨⟨true⟩, t⟩ : (tiltPointsSum B).obj c)) = .of t :=
  freeAb.desc_of ..

/-- For endomorphisms Δ_b of the O^♭-algebras B_b, the endomorphism 1 − Δ of the functor S ↦
ℤ[⊔_b Hom(B_b, S^♭)], sending [x] to [x] − [x∘Δ_b]. -/
abbrev oneSub : freeAb (tiltPointsSum B) ⟶ freeAb (tiltPointsSum B) :=
  freeAb.desc (fun _ x ↦ .of x - .of ⟨x.1, ⟨Δ x.1 ≫ x.2.down⟩⟩) (by bound)

@[simp]
lemma charTwist_comp_evalZero : charTwist χ g ≫ evalZero b = evalZero b := by
  ext
  simp_all [charTwist]

/-- For an additive map `g : ℚ≥0 → ℚ`, twisting `O^♭[ℚ≥0]` by `χ ∘ g` and then sending `T^a` to
`T^{g(a)}` is the same as first sending `T^a` to `T^{g(a)}` and then twisting `O^♭[ℚ]` by `χ`. -/
@[reassoc]
lemma charTwist_comp_discToTorus :
    charTwist χ g ≫ discToTorus g = discToTorus g ≫ charTwist χ (AddMonoidHom.id ℚ) := by
  ext
  simp [charTwist]

/-- The endomorphism `T^s ↦ χ(s) T^s` of the ring of the torus, and the identity of the ring of
the point. -/
def pointOrTorusTwist : ∀ i : ULift.{1} Bool, pointOrTorus i ⟶ pointOrTorus i
  | ⟨true⟩ => charTwist χ (AddMonoidHom.id ℚ)
  | ⟨false⟩ => 𝟙 (pointOrTorus ⟨false⟩)

/-- The endomorphism `T^s ↦ χ(s) T^s` of the ring of the disc `true`, and `T^s ↦ χ(-s) T^s` of
the ring of the disc `false`. -/
def discTwist : ULift.{1} Bool → (monoidAlg ℚ≥0 ⟶ monoidAlg ℚ≥0)
  | ⟨true⟩ => charTwist χ coeHom
  | ⟨false⟩ => charTwist χ (-coeHom)

/-- The twist of either disc fixes the evaluation at `T = 0`. -/
lemma discTwist_comp_evalZero : discTwist χ a ≫ evalZero b = evalZero b := by
  rcases a with ⟨_ | _⟩ <;> simp only [discTwist, charTwist_comp_evalZero]

private lemma oneSub_ofPoint (A : PadicTest) (t : CommAlgCat.of OFlat OFlat ⟶ tilt A) :
    (oneSub (pointOrTorusTwist χ)).app A (ofPoint (ψ := 𝟭 _) t) =
      ofPoint (ψ := 𝟭 _) t - ofPoint (ψ := 𝟭 _) t :=
  (freeAb.desc_of (Y := tiltPointsSum pointOrTorus) _ _ A ⟨⟨false⟩, ⟨t⟩⟩).trans (by
    change ofPoint (ψ := 𝟭 _) t - ofPoint (ψ := 𝟭 _) (𝟙 _ ≫ t) = _
    rw [Category.id_comp])

private lemma oneSub_ofDisc (A : PadicTest) (b : ULift.{1} Bool) (t : monoidAlg ℚ≥0 ⟶ tilt A) :
    (oneSub (discTwist χ)).app A (ofDisc (ψ := 𝟭 _) b t) =
      ofDisc (ψ := 𝟭 _) b t - ofDisc (ψ := 𝟭 _) b (discTwist χ b ≫ t) :=
  freeAb.desc_of (Y := twoDiscs) _ _ A ⟨b, ⟨t⟩⟩

/-- The gluing map commutes with the operators `1 - Δ`, where `Δ` is the twist by `χ` on the
torus and on the two discs, and the identity on the point. -/
lemma oneSub_comp_gluing :
    oneSub (pointOrTorusTwist χ) ≫ gluing = gluing ≫ oneSub (discTwist χ) := by
  -- Check on generators: `charTwist` fixes evaluation at `0` (the point) and is compatible with the
  -- inclusions of the rings of the two discs in the ring of the torus.
  apply freeAb.hom_ext
  rintro A ⟨⟨_ | _⟩, ⟨t⟩⟩
  · let t' : CommAlgCat.of OFlat OFlat ⟶ tilt A := t
    change gluing.app A ((oneSub (pointOrTorusTwist χ)).app A (ofPoint (ψ := 𝟭 _) t')) =
      (oneSub (discTwist χ)).app A (gluing.app A (ofPoint (ψ := 𝟭 _) t'))
    simp [gluing_ofPoint, oneSub_ofPoint, oneSub_ofDisc, discTwist_comp_evalZero]
  · -- On a point of the torus both sides are the same four terms, grouped in two ways.
    let t' : monoidAlg ℚ ⟶ tilt A := t
    change gluing.app A ((oneSub (pointOrTorusTwist χ)).app A (ofTorus (ψ := 𝟭 _) t')) =
      (oneSub (discTwist χ)).app A (gluing.app A (ofTorus (ψ := 𝟭 _) t'))
    have h_torus : (oneSub (pointOrTorusTwist χ)).app A (ofTorus (ψ := 𝟭 _) t') =
        ofTorus (ψ := 𝟭 _) t' - ofTorus (ψ := 𝟭 _) (charTwist χ (AddMonoidHom.id ℚ) ≫ t') :=
      freeAb.desc_of (Y := tiltPointsSum pointOrTorus) _ _ A ⟨⟨true⟩, ⟨t'⟩⟩
    simp [gluing_ofTorus, h_torus, oneSub_ofDisc, discTwist,
      charTwist_comp_discToTorus_assoc]
    exact sub_sub_sub_comm ..

/-- The gluing map is a monomorphism: on each test it has a retraction. -/
instance : Mono gluing := by
  -- Two maps out of the ring of the torus that agree on `T ^ |s|` agree on `T ^ s`: the exponents
  -- where they agree form a subgroup.
  have h_epi : Epi (discToTorus coeHom) := by
    refine ⟨fun x y h_comp ↦ hom_ext (algHom_ext' (MonoidHom.ext fun s ↦ ?_) (by ext))⟩
    refine mabs_mem_iff (H := MonoidHom.eqLocus ..).mp ?_
    change x (single s.nnabs (1 : OFlat)) = y (single s.nnabs (1 : OFlat))
    simpa using congrArg (fun φ ↦ φ (single s.nnabs (1 : OFlat))) h_comp
  -- On each test `gluing` has a retraction: a point of the disc `false` goes to the point `∗`; a
  -- point of the disc `true` goes to `∗ - t` if it comes from a point `t` of the torus (unique by
  -- `h_epi`), and to `∗` otherwise.
  refine (NatTrans.mono_iff_mono_app _).mpr fun c ↦ ?_
  let r : (freeAb twoDiscs).obj c ⟶ (freeAb (tiltPointsSum pointOrTorus)).obj c :=
    AddCommGrpCat.ofHom (FreeAddCommGroup.lift fun x ↦
      ofPoint (ψ := 𝟭 _) structureMap -
        cond x.1.down (extend (fun s : monoidAlg ℚ ⟶ tilt c ↦ discToTorus coeHom ≫ s)
          (fun s ↦ ofTorus (ψ := 𝟭 _) s) 0 x.2.down) 0)
  have hr (b : ULift.{1} Bool) (t : monoidAlg ℚ≥0 ⟶ tilt c) :
      r (ofDisc (ψ := 𝟭 _) b t) = ofPoint (ψ := 𝟭 _) structureMap -
        cond b.down (extend (fun s : monoidAlg ℚ ⟶ tilt c ↦ discToTorus coeHom ≫ s)
          (fun s ↦ ofTorus (ψ := 𝟭 _) s) 0 t) 0 :=
    FreeAddCommGroup.lift_apply_of _ _
  refine SplitMono.mono ⟨r, AddCommGrpCat.hom_ext (FreeAddCommGroup.lift_ext _ _ fun x ↦ ?_)⟩
  rcases x with ⟨⟨_ | _⟩, ⟨t⟩⟩
  · -- Over the point, a point is an algebra map out of `O^♭`, so it is the structure map.
    let t' : CommAlgCat.of OFlat OFlat ⟶ tilt c := t
    have ht : t' = structureMap := by ext
    change r (gluing.app c (ofPoint (ψ := 𝟭 _) t')) = ofPoint (ψ := 𝟭 _) t'
    simp [gluing_ofPoint, hr, ht]
  · let t' : monoidAlg ℚ ⟶ tilt c := t
    change r (gluing.app c (ofTorus (ψ := 𝟭 _) t')) = ofTorus (ψ := 𝟭 _) t'
    simp [gluing_ofTorus, hr, Injective.extend_apply h_epi.left_cancellation]

open Abelian.Ext TensorProduct LinearEquiv H Comparison

/-- For a test `c` and a perfect `O^♭`-algebra `b`, the algebra `c^♭ ⊗ b` is a perfect ring. -/
lemma perfectRing_tensorLeft_tilt (c : PadicTest) (b : CommAlg OFlat) (hb : PerfectRing b p) :
    PerfectRing ((tensorLeft (tilt c)) b) p :=
  perfectRing_tensor natCast_eq_zero_of_algebra_oFlat ⟨tilt c, c.isPerfectTorsionFree_tilt.1⟩
    ⟨b, hb⟩

/-- If the coefficient functor `G = – ⊗ N` is acyclic on perfect `O^♭`-algebras (for b perfect,
Hom(b, –^♭) has cohomology G(b) in degree 0 and none above), then `ℤ[⊔_b Hom(ψ(B_b), –^♭)]` has no
cohomology in positive degree with coefficients in `S ↦ G(S^♭)`, for `O^♭`-algebras `B_b` indexed by
`Bool` and an endofunctor `ψ` with the `ψ(B_b)` perfect. -/
lemma subsingleton_H_freeAb_tiltPointsSum
    (h_acyclic : IsAcyclicOnPerfect (moduleCoeff (tensorCoeff N)))
    (B : ULift.{1} Bool → CommAlg OFlat) (ψ : CommAlg OFlat ⥤ CommAlg OFlat)
    (h_perf : ∀ b : ULift.{1} Bool, PerfectRing (ψ (B b)) p) (n : ℕ) :
    Subsingleton (H (freeAb (tiltPointsSum B ψ)) (tilt ⋙ moduleCoeff (tensorCoeff N)) (n + 1)) := by
  -- Each part has no cohomology in positive degree, and cohomology turns the disjoint union into a
  -- product.
  have h_part (b : ULift.{1} Bool) (m : ℕ) :
      Subsingleton (H (freeAb (tilt ⋙ reprBy (ψ (B b))))
        (tilt ⋙ moduleCoeff (tensorCoeff N)) (m + 1)) :=
    (isBijective_reprBy_iff.1 (h_acyclic (ψ (B b)))).2 m
  exact (sigma_bijective ..).injective.subsingleton

/-- For `O^♭`-algebras `B_b` indexed by `Bool` and an endofunctor `ψ` of `O^♭`-algebras such that
the `ψ(B_b)` are perfect rings, the functor `ℤ[⊔_b Hom(ψ(B_b), –^♭)]` has flat base change. -/
lemma hasFlatBaseChange_freeAb_tiltPointsSum (B : ULift.{1} Bool → CommAlg OFlat)
    (ψ : CommAlg OFlat ⥤ CommAlg OFlat) (h_perf : ∀ b : ULift.{1} Bool, PerfectRing (ψ (B b)) p) :
    HasFlatBaseChange (freeAb (tiltPointsSum B ψ)) := by
  -- `M ⊗ –` commutes with the finite product, and each part is representable by a perfect
  -- algebra, so it has flat base change.
  intro S T M instS instT instAlg instM instSM instTM instTower instFlat Φ n
  let e : M ⊗[S] H (freeAb (tiltPointsSum B ψ)) (moduleCoeff Φ) n ≃ₗ[S]
      ∀ b : ULift.{1} Bool, M ⊗[S] H (freeAb (tilt ⋙ reprBy (ψ (B b)))) (moduleCoeff Φ) n :=
    (ofBijective (.pi fun _ ↦ mapₗ ..) (sigma_bijective ..)).lTensor M ≪≫ₗ piRight ..
  refine (bijective_iff_of_comm_sq (fun x ↦ ?_) e.bijective (sigma_bijective ..)).2
    (.piMap fun _ ↦ hasFlatBaseChange_of_iso_reprBy homTiltIso.symm ..)
  induction x with
  | tmul m y => simp [e, mapₗ, map_push, funext_iff]
  | add x y hx hy => simp_all [funext_iff]

/-- The projection of a pair `(y₀, y₁)` of elements of `O^♭[ℚ≥0]` to `y₀` (for `false`) or to
`y₁` (for `true`). -/
private def pairProj (b : Bool) :
    ModuleCat.of OFlat (monoidAlg ℚ≥0 × monoidAlg ℚ≥0) ⟶ ModuleCat.of OFlat (monoidAlg ℚ≥0) :=
  ModuleCat.ofHom (cond b (.snd ..) (.fst ..))

/-- The `O^♭`-linear maps that describe the gluing map in degree `0`. A pair `(y₀, y₁)` of
elements of `O^♭[ℚ≥0]` goes to the value `y₀(0)` in the ring `O^♭` of the point, and to
`y₀(T⁻¹) - y₁(T)` in the ring `O^♭[ℚ]` of the torus. -/
private def glueLinear : ∀ b : ULift.{1} Bool,
    ModuleCat.of OFlat (monoidAlg ℚ≥0 × monoidAlg ℚ≥0) ⟶
      (asModules (𝟭 (CommAlg OFlat))) (pointOrTorus b)
  | ⟨false⟩ => pairProj false ≫ (asModules (𝟭 (CommAlg OFlat))).map (evalZero _)
  | ⟨true⟩ =>
    pairProj false ≫ (asModules (𝟭 (CommAlg OFlat))).map (discToTorus (-coeHom)) -
      pairProj true ≫ (asModules (𝟭 (CommAlg OFlat))).map (discToTorus coeHom)

/-- The map `(y₀, y₁) ↦ (y₀(0), y₀(T⁻¹) - y₁(T))` from pairs of elements of `O^♭[ℚ≥0]` to pairs
in `O^♭ × O^♭[ℚ]` is bijective. -/
private lemma bijective_glueLinear :
    Bijective fun x : monoidAlg ℚ≥0 × monoidAlg ℚ≥0 ↦
      (glueLinear ⟨false⟩ x, glueLinear ⟨true⟩ x) := by
  -- The inverse sends `(a, w)` to `(a + w₋, a - w₊)`, where `w₊` and `w₋(T⁻¹)` are the parts of
  -- `w` of exponent `≥ 0` and `< 0`.
  have {B : Type} [CommRing B] [Algebra OFlat B] :
      ZeroHomClass (OFlat[ℚ≥0] →ₐ[OFlat] B) OFlat[ℚ≥0] B :=
    RingHomClass.toAddMonoidHomClass.toZeroHomClass
  let split : (ℚ →₀ OFlat) →ₗ[OFlat] OFlat[ℚ≥0] × OFlat[ℚ≥0] :=
    Finsupp.linearCombination OFlat fun t : ℚ ↦
      if 0 ≤ t then (0, -single t.toNNRat 1) else (single (-t).toNNRat 1, 0)
  let glueInv : OFlat × OFlat[ℚ] →ₗ[OFlat] OFlat[ℚ≥0] × OFlat[ℚ≥0] :=
    .coprod (Algebra.linearMap OFlat _) (split ∘ₗ (coeffLinearEquiv OFlat).toLinearMap)
  refine (ofLinearMap (.prod (glueLinear ⟨false⟩).hom (glueLinear ⟨true⟩).hom) glueInv
    ?glue_comp_inv ?inv_comp_glue : (OFlat[ℚ≥0] × OFlat[ℚ≥0]) ≃ₗ[OFlat] OFlat × OFlat[ℚ]).bijective
  · -- The gluing maps after the inverse are the identity of `O^♭ × O^♭[ℚ]`: check it on `1` and on
    -- the monomials `T^t`, whose image under the inverse depends on the sign of `t`.
    dsimp +zetaDelta [glueLinear, pairProj, pointOrTorus, Bool.cond_false]
    ext : 3
    · simp
    · simp
    · simp
      split_ifs with h_nonneg
      · simp_all [Rat.coe_toNNRat, ← single_neg]
      · simp_all [le_of_lt, Rat.coe_toNNRat]
  · -- The inverse after the gluing maps is the identity of `O^♭[ℚ≥0] × O^♭[ℚ≥0]`: check it on the
    -- monomials of each factor; for `T^a` in the first factor the case `a = 0` is done separately.
    dsimp +zetaDelta [glueLinear, pairProj, pointOrTorus, Bool.cond_true]
    ext : 3
    · simp
      split_ifs with h_zero
      · simp_all [← one_def, Prod.ext_iff]
      · simp_all
    · simp

lemma perfectRing_monoidAlg_nnrat : PerfectRing (monoidAlg ℚ≥0) p := by
  simp [perfectRing_monoidAlgebra]

lemma perfectRing_pointOrTorus (b : ULift.{1} Bool) : PerfectRing (pointOrTorus b) p := by
  rcases b with ⟨_ | _⟩
  · exact instPerfectRingOFlat
  · exact perfectRing_monoidAlgebra ℚ

/-- For a test `c`, the target `ℤ[two discs]` of the gluing map formed with the algebras `c^♭ ⊗ B`
has flat base change. -/
lemma hasFlatBaseChange_freeAb_twoDiscs (c : PadicTest) :
    HasFlatBaseChange (freeAb (twoDiscs (tensorLeft (tilt c)))) :=
  hasFlatBaseChange_freeAb_tiltPointsSum _ _ fun _ ↦
    perfectRing_tensorLeft_tilt c _ perfectRing_monoidAlg_nnrat

/-- For a test `c`, the source `ℤ[torus ⊔ point]` of the gluing map formed with the algebras
`c^♭ ⊗ B` has flat base change. -/
lemma hasFlatBaseChange_freeAb_tiltPointsSum_pointOrTorus (c : PadicTest) :
    HasFlatBaseChange (freeAb (tiltPointsSum pointOrTorus (tensorLeft (tilt c)))) :=
  hasFlatBaseChange_freeAb_tiltPointsSum _ _ fun b ↦
    perfectRing_tensorLeft_tilt c _ (perfectRing_pointOrTorus b)

/-- Let `G` be the coefficient functor `b ↦ b ⊗ N` on `O^♭`-algebras, and assume it is acyclic on
perfect algebras: for every perfect `O^♭`-algebra b, the functor S ↦ Hom(b, S^♭) on p-adic tests has
cohomology `G(b)` in degree 0 with coefficients S ↦ G(S^♭). Then for every p-adic test `c`, the
gluing map ℤ[torus ⊔ point] → ℤ[two discs] is an equivalence for the coefficients S ↦ G(S^♭), that
is, it induces bijections on all Extⁿ. Here the discs are the points of c^♭ ⊗ O^♭[ℚ≥0] in tilts, and
the map sends t to t⁻¹ in disc `false` minus t in disc `true`, and the point to the origin of disc
`false`. -/
lemma isCohomEquiv_tensorCoeff_gluing (c : PadicTest)
    (h_acyclic : IsAcyclicOnPerfect (moduleCoeff (tensorCoeff N))) :
    IsCohomEquiv (tilt ⋙ moduleCoeff (tensorCoeff N)) (gluing (tensorLeft (tilt c))) := by
  -- Source and target are sums of two functors `Hom(ψc (A b), –^♭)` with `ψc (A b)` perfect, so
  -- their cohomology is `∏ b, G (ψc (A b))`, in degree `0`. Both products are identified with
  -- `U Y = (c^♭ ⊗ Y) ⊗ N` for `Y` the module of pairs of elements of `monoidAlg ℚ≥0`, compatibly
  -- with `gluing`.
  let G : AbFunctor (CommAlg OFlat) := moduleCoeff (tensorCoeff N)
  let ψc : CommAlg OFlat ⥤ CommAlg OFlat := tensorLeft (tilt c)
  let L : CommAlg OFlat ⥤ ModuleCat OFlat := asModules (𝟭 (CommAlg OFlat))
  let U : AbFunctor (ModuleCat OFlat) :=
    tensorWith (S := OFlat) OFlat (tilt c) ⋙ moduleCoeff (tensorRight N)
  -- The section of `G` attached to `x : U Y` by linear maps `f b` from `Y` to the rings `A b`.
  let sectionOfMaps {Y : ModuleCat OFlat} (A : ULift.{1} Bool → CommAlg OFlat)
      (f : ∀ b, Y ⟶ L (A b)) (x : U Y) : freeAb (tiltPointsSum A ψc) ⟶ tilt ⋙ G :=
    freeAb.desc (fun _ t ↦ G.map t.snd.down (U.map (f t.fst) x))
      (by solve_by_elim [G.map_comp_apply])
  -- In degree `0`: `U` keeps finite products, so `U Y` is the product of the
  -- `U (A b) = G (ψc (A b))`, and these are the sections of the parts.
  have h_sections {Y : ModuleCat OFlat} (A : ULift.{1} Bool → CommAlg OFlat)
      (hA : ∀ b, PerfectRing (A b) p) (f : ∀ b, Y ⟶ L (A b))
      (hf : Bijective fun x ↦ (f ⟨false⟩ x, f ⟨true⟩ x)) :
      Bijective (mk₀ ∘ sectionOfMaps A f) := by
    have h_perf (b : ULift.{1} Bool) : PerfectRing (ψc (A b)) p :=
      perfectRing_tensorLeft_tilt c (A b) (hA b)
    have h_zero (b : ULift.{1} Bool) :
        Bijective ((Comparison.restrict tilt G).homOfValue (𝟙 (tilt ⋙ reprBy (ψc (A b))))) :=
      (isBijective_reprBy_iff.1 (h_acyclic (ψc (A b)))).1
    have h_prod : Bijective fun (x : U Y) b ↦ U.map (f b) x := by
      have h_pair : Bijective fun x : U Y ↦ (U.map (f ⟨false⟩) x, U.map (f ⟨true⟩) x) :=
        hf.map_prod (U ⋙ forget _)
      refine (bijective_iff_existsUnique _).2 fun y ↦ ?_
      simpa [funext_iff] using h_pair.existsUnique (y ⟨false⟩, y ⟨true⟩)
    refine (bijective_iff_of_comm_sq (fun _ ↦ ?_) (.comp (.piMap h_zero) h_prod)
      (sigma_bijective ..)).2 (.piMap fun _ ↦ mk₀_bijective ..)
    ext
    simpa [H.map] using congrArg _ freeAb.hom_ext
  have h_perf_discs (_ : ULift.{1} Bool) : PerfectRing (monoidAlg ℚ≥0) p :=
    perfectRing_monoidAlg_nnrat
  rintro (_ | n)
  · -- In degree `0`, pulling the section `sectionOfMaps _ (fun b ↦ pairProj b.down) x` back along
    -- `gluing` gives `sectionOfMaps pointOrTorus glueLinear x`.
    have h_pullback :
        ⇑(H.map (tilt ⋙ G) (gluing ψc) 0) ∘ mk₀ ∘
            sectionOfMaps (fun _ ↦ monoidAlg ℚ≥0) (fun b ↦ pairProj b.down) =
          mk₀ ∘ sectionOfMaps pointOrTorus glueLinear := by
      -- `G (ψc b)` and `U (L b)` are the same module `(c^♭ ⊗ b) ⊗ N`, with the same maps.
      have h_GU {b b' : CommAlg OFlat} (g : b ⟶ b') : G.map (ψc.map g) = U.map (L.map g) := rfl
      ext x
      simp [H.map]
      congr
      apply freeAb.hom_ext
      rintro A ⟨⟨_ | _⟩, ⟨t⟩⟩
      · let t' : ψc (CommAlgCat.of OFlat OFlat) ⟶ tilt A := t
        have h_disc (s : ψc (monoidAlg ℚ≥0) ⟶ tilt A) :
            (sectionOfMaps _ (fun b ↦ pairProj b.down) x).app A (ofDisc ⟨false⟩ s) =
              G.map s (U.map (pairProj false) x) :=
          freeAb.desc_of (Y := twoDiscs ψc) _ _ A ⟨⟨false⟩, ⟨s⟩⟩
        have h_point :
            (sectionOfMaps pointOrTorus glueLinear x).app A (ofPoint t') =
              G.map t' (U.map (glueLinear ⟨false⟩) x) :=
          freeAb.desc_of (Y := tiltPointsSum pointOrTorus ψc) _ _ A ⟨⟨false⟩, ⟨t'⟩⟩
        change (sectionOfMaps _ (fun b ↦ pairProj b.down) x).app A
          ((gluing ψc).app A (ofPoint t')) =
          (sectionOfMaps pointOrTorus glueLinear x).app A (ofPoint t')
        rw [gluing_ofPoint, h_disc, h_point, G.map_comp, h_GU]
        change G.map t' (U.map (L.map (evalZero (CommAlgCat.of OFlat OFlat)))
            (U.map (pairProj false) x)) =
          G.map t' (U.map (pairProj false ≫ L.map (evalZero (CommAlgCat.of OFlat OFlat))) x)
        rw [U.map_comp]
        rfl
      · let t' : ψc (monoidAlg ℚ) ⟶ tilt A := t
        have h_disc (b : ULift.{1} Bool) (s : ψc (monoidAlg ℚ≥0) ⟶ tilt A) :
            (sectionOfMaps _ (fun b ↦ pairProj b.down) x).app A (ofDisc b s) =
              G.map s (U.map (pairProj b.down) x) :=
          freeAb.desc_of (Y := twoDiscs ψc) _ _ A ⟨b, ⟨s⟩⟩
        have h_torus :
            (sectionOfMaps pointOrTorus glueLinear x).app A (ofTorus t') =
              G.map t' (U.map (glueLinear ⟨true⟩) x) :=
          freeAb.desc_of (Y := tiltPointsSum pointOrTorus ψc) _ _ A ⟨⟨true⟩, ⟨t'⟩⟩
        change (sectionOfMaps _ (fun b ↦ pairProj b.down) x).app A
          ((gluing ψc).app A (ofTorus t')) =
          (sectionOfMaps pointOrTorus glueLinear x).app A (ofTorus t')
        rw [gluing_ofTorus, map_sub, h_disc, h_disc, h_torus, G.map_comp, G.map_comp, h_GU, h_GU]
        change G.map t' (U.map (L.map (discToTorus (-coeHom))) (U.map (pairProj false) x)) -
            G.map t' (U.map (L.map (discToTorus coeHom)) (U.map (pairProj true) x)) =
          G.map t' (U.map (pairProj false ≫ L.map (discToTorus (-coeHom)) -
            pairProj true ≫ L.map (discToTorus coeHom)) x)
        rw [U.map_sub, U.map_comp, U.map_comp]
        exact (map_sub (G.map t').hom _ _).symm
    refine ((h_sections _ h_perf_discs (fun b ↦ pairProj b.down) bijective_id).of_comp_iff _).1 ?_
    rw [h_pullback]
    exact h_sections pointOrTorus perfectRing_pointOrTorus glueLinear bijective_glueLinear
  · -- In positive degree both groups vanish.
    have h_vanish (A : ULift.{1} Bool → CommAlg OFlat) (hA : ∀ b, PerfectRing (A b) p) :
        Subsingleton (H (freeAb (tiltPointsSum A ψc)) (tilt ⋙ G) (n + 1)) :=
      subsingleton_H_freeAb_tiltPointsSum h_acyclic A ψc
        (fun b ↦ perfectRing_tensorLeft_tilt c (A b) (hA b)) n
    exact ⟨fun x y _ ↦ (h_vanish _ h_perf_discs).elim x y,
      fun y ↦ ⟨0, (h_vanish _ perfectRing_pointOrTorus).elim _ y⟩⟩

/-- For every test `c`, the gluing map formed with the algebras `c^♭ ⊗ B` induces bijections on
cohomology with coefficients in `genericCoeff`, the coefficients S ↦ S[1/p]. -/
lemma isCohomEquiv_gluing_generic (c : PadicTest) :
    IsCohomEquiv genericCoeff (gluing (tensorLeft (tilt c))) := by
  -- `isCohomEquiv_tensorCoeff_gluing` gives the claim for the coefficients `S ↦ S^♭ ⊗ N ⊗ 𝔪`, where
  -- `N = O^♭ ⊗_{A_inf} O_C` is killed by `p^♭` and `𝔪` is the maximal ideal of `O^♭`.
  -- `CoeffCompBijective.periodAlg_of_almostCoeff` lifts it to `ℂ_p ⊗ (O_C ⊗ W(S^♭))^`, which is
  -- `genericCoeff` by `exists_periodAlg_iso_genericAlg`.
  let α : freeAb (tiltPointsSum pointOrTorus (tensorLeft (tilt c))) ⟶
      𝟭 PadicTest ⋙ freeAb (twoDiscs (tensorLeft (tilt c))) :=
    gluing (tensorLeft (tilt c))
  have h_tilt : CoeffCompBijective (𝟙 (𝟭 _ ⋙ tilt)) α (almostCoeff (OFlat ⊗[Ainf] OC)) :=
    (coeffCompBijective_id_iff_restrict (.refl _)).2 (isCohomEquiv_tensorCoeff_gluing c
      (isAcyclicOnPerfect_almostCoeff isPeriodRingPair_OC.pFlat_smul_eq_zero)).bij
  have h_lift :
      CoeffCompBijective (𝟙 (𝟭 _ ⋙ tilt)) α (asModules (periodAlg OC) ⋙ tensorWith ℂ_[p] ℂ_[p]) :=
    .periodAlg_of_almostCoeff (hasFlatBaseChange_freeAb_twoDiscs c) isPeriodRingPair_OC
      (fun _ ↦ by apply hasFlatBaseChange_freeAb_tiltPointsSum_pointOrTorus c)
      isPerfectTorsionFree_tilt isPerfectTorsionFree_tilt h_tilt
  obtain ⟨θ, -⟩ := exists_periodAlg_iso_genericAlg (p := p)
  -- `by exact` delays elaborating `θ` until the expected type is known.
  exact ((coeffCompBijective_id_iff_restrict (by exact θ)).1 h_lift).eqv

open Algebra.TensorProduct Functor in
/-- The perfect projective line has the cohomology of a point. For an endofunctor ψ of
`O^♭`-algebras, `gluing ψ` is the map ℤ[torus ⊔ point] → ℤ[two discs] of functors on p-adic tests,
where the discs are the points of ψ(O^♭[ℚ≥0]) in tilts; it sends t in the torus to t⁻¹ in the disc
`false` minus t in the disc `true`, and the point to the origin of the disc `false`, so its cokernel
for ψ = id is the perfect line with a point collapsed. Suppose that for every p-adic test `c` the
gluing with ψ = c^♭ ⊗ − induces bijections Extⁿ(ℤ[two discs], F) → Extⁿ(ℤ[torus ⊔ point], F) for all
n; then for every `S` whose values are flat ℤ-modules, every Extⁿ(S ⊗ coker gluing, F) is zero. -/
lemma subsingleton_H_cokernel_gluing {F : AbFunctor PadicTest}
    (h_rep : ∀ c : PadicTest, IsCohomEquiv F (gluing (tensorLeft (tilt c))))
    (S : AbFunctor PadicTest) [HasFlatValues S] :
    ∀ n : ℕ, Subsingleton (H (abTensor S (Limits.cokernel (gluing (𝟭 (CommAlg OFlat))))) F n) := by
  -- It suffices that `S ⊗ gluing` be an equivalence, and by dévissage `S` may be taken to be
  -- `ℤ[⊔ h_{c j}]`, with `h_c = reprBy c` the functor represented by `c`. Then
  -- `h_{c j} × Hom(B, –^♭) = Hom((c j)^♭ ⊗ B, –^♭)` turns `S ⊗ gluing` into the sum of the maps in
  -- the hypothesis.
  suffices h_eqv : IsCohomEquiv F ((abTensor S).map gluing) from
    (isCohomEquiv_iff_subsingleton (.map ⟨ShortComplex.exact_cokernel gluing⟩ (abTensor S))).1 h_eqv
  -- Dévissage of the comparison along `– ⊗ gluing`.
  have h_devissage := (Comparison.id F).devissage (abTensor.flip _) (abTensor.flip.map gluing)
  refine Comparison.IsBijective.eqv (h_devissage.allBijective_of_allBijective_sigma_reprBy
    (fun ι c n ↦ ?_) S)
  let ψ (j : ι) : CommAlg OFlat ⥤ CommAlg OFlat := tensorLeft (tilt (c j))
  -- A map out of `(c j)^♭ ⊗ B b` is sent to its two restrictions; `tilt` is fully faithful.
  let u (B : ULift.{1} Bool → CommAlg OFlat) :
      (sigma fun j ↦ tiltPointsSum B (ψ j)) ⟶ (sigma fun j ↦ reprBy (c j)) ⊗ tiltPointsSum B :=
    { app _ := ↾fun ⟨j, b, t⟩ ↦
        (⟨j, ⟨tilt.preimage (tensorInl ≫ t.down)⟩⟩, ⟨b, ⟨tensorInr ≫ t.down⟩⟩)
      naturality d d' f := by
        ext ⟨j, b, t⟩
        have h_restrict : tilt.preimage ((tensorInl ≫ t.down) ≫ tilt.map f) =
            tilt.preimage (tensorInl ≫ t.down) ≫ f := by
          rw [Functor.preimage_comp, Functor.preimage_map]
        exact Prod.ext (Sigma.ext rfl (heq_of_eq (congrArg ULift.up h_restrict))) rfl }
  have hu_bijective (B : ULift.{1} Bool → CommAlg OFlat) (d : PadicTest) : Bijective (u B d) := by
    -- The inverse sends a pair of maps to the induced map on the tensor product.
    let uInv : ((sigma fun j ↦ reprBy (c j)) ⊗ tiltPointsSum B).obj d →
        (sigma fun j ↦ tiltPointsSum B (ψ j)).obj d :=
      fun (⟨j, ⟨f⟩⟩, ⟨b, ⟨t⟩⟩) ↦ ⟨j, b, ⟨ofHom (productMap (tilt.map f).hom t.hom)⟩⟩
    refine bijective_iff_has_inverse.mpr ⟨uInv, fun ⟨j, b, ⟨t⟩⟩ ↦ ?_, fun ⟨⟨j, ⟨f⟩⟩, b, ⟨t⟩⟩ ↦ ?_⟩
    · -- An algebra map out of `(c j)^♭ ⊗ B b` is determined by its two restrictions.
      have h_product :
          productMap (t.hom.comp includeLeft) (t.hom.comp includeRight) = t.hom :=
        Algebra.TensorProduct.ext (productMap_left ..) (productMap_right ..)
      exact Sigma.ext rfl <| heq_of_eq <| Sigma.ext rfl <| heq_of_eq <| congrArg ULift.up <| by
        change ofHom (productMap (tilt.map (tilt.preimage (tensorInl ≫ t))).hom
          (tensorInr ≫ t).hom) = t
        rw [Functor.map_preimage]
        exact CommAlgCat.hom_ext h_product
    · refine Prod.ext (Sigma.ext rfl <| heq_of_eq <| congrArg ULift.up ?_)
          (Sigma.ext rfl <| heq_of_eq <| congrArg ULift.up ?_)
      · change tilt.preimage (tensorInl ≫ ofHom (productMap (tilt.map f).hom t.hom)) = f
        exact (congrArg tilt.preimage (CommAlgCat.hom_ext (productMap_left ..))).trans
          (Functor.preimage_map f)
      · change tensorInr ≫ ofHom (productMap (tilt.map f).hom t.hom) = t
        exact CommAlgCat.hom_ext (productMap_right ..)
  -- So the cohomology of `ℤ[⊔ h_{c j}] ⊗ ℤ[⊔ Hom(B b, –^♭)]` is the product over `j` of that of
  -- the `ℤ[⊔ Hom((c j)^♭ ⊗ B b, –^♭)]`.
  let v (B : ULift.{1} Bool → CommAlg OFlat) :
      freeAb (sigma fun j ↦ tiltPointsSum B (ψ j)) ⟶
        abTensor (freeAb (sigma fun j ↦ reprBy (c j))) (freeAb (tiltPointsSum B)) :=
    freeAb.map (u B) ≫ freeAb.prod _ _
  have hv_bijective (B : ULift.{1} Bool → CommAlg OFlat) : Bijective fun x j ↦
      map F (freeAb.map (sigma.ι (fun j ↦ tiltPointsSum B (ψ j)) j)) n (map F (v B) n x) :=
    have hv_eqv : IsCohomEquiv F (v B) :=
      (IsCohomEquiv.of_bijective (hu_bijective B)).comp_iff.2 (.of_isIso _)
    (sigma_bijective ..).comp (hv_eqv n)
  -- The square commutes already on generators of the sources, since the maps `discToTorus` and
  -- `evalZero` do not change the restriction to `(c j)^♭`.
  have h_square (j : ι) :
      gluing (ψ j) ≫ freeAb.map (sigma.ι (fun k ↦ twoDiscs (ψ k)) j) ≫ v (fun _ ↦ monoidAlg ℚ≥0) =
        freeAb.map (sigma.ι (fun k ↦ tiltPointsSum pointOrTorus (ψ k)) j) ≫ v pointOrTorus ≫
          (abTensor (freeAb (sigma fun k ↦ reprBy (c k)))).map gluing := by
    let lhsMap : freeAb (twoDiscs (ψ j)) ⟶
        abTensor (freeAb (sigma fun k ↦ reprBy (c k))) (freeAb twoDiscs) :=
      freeAb.map (sigma.ι (fun k ↦ twoDiscs (ψ k)) j) ≫ v (fun _ ↦ monoidAlg ℚ≥0)
    let rhsMap : freeAb (tiltPointsSum pointOrTorus (ψ j)) ⟶
        abTensor (freeAb (sigma fun k ↦ reprBy (c k))) (freeAb (tiltPointsSum pointOrTorus)) :=
      freeAb.map (sigma.ι (fun k ↦ tiltPointsSum pointOrTorus (ψ k)) j) ≫ v pointOrTorus
    have h_lhs (A : PadicTest) (b : ULift.{1} Bool) (t : ψ j (monoidAlg ℚ≥0) ⟶ tilt A) :
        lhsMap.app A (ofDisc b t) =
          (FreeAddCommGroup.of ⟨j, ⟨tilt.preimage (tensorInl ≫ t)⟩⟩ :
              (freeAb (sigma fun k ↦ reprBy (c k))).obj A) ⊗ₜ[ℤ]
            ofDisc (ψ := 𝟭 _) b (tensorInr ≫ t) := by
      change (freeAb.prod _ _).app A (FreeAddCommGroup.of
        ((u (fun _ ↦ monoidAlg ℚ≥0)).app A
          ((sigma.ι (fun k ↦ twoDiscs (ψ k)) j).app A ⟨b, ⟨t⟩⟩))) = _
      exact freeAb.desc_of ..
    have h_rhs_point (A : PadicTest) (t : ψ j (CommAlgCat.of OFlat OFlat) ⟶ tilt A) :
        ((abTensor (freeAb (sigma fun k ↦ reprBy (c k)))).map gluing).app A
            (rhsMap.app A (ofPoint t)) =
          (FreeAddCommGroup.of ⟨j, ⟨tilt.preimage (tensorInl ≫ t)⟩⟩ :
              (freeAb (sigma fun k ↦ reprBy (c k))).obj A) ⊗ₜ[ℤ]
            gluing.app A (ofPoint (ψ := 𝟭 _) (tensorInr ≫ t)) := by
      have h_prod : rhsMap.app A (ofPoint t) =
          (FreeAddCommGroup.of ⟨j, ⟨tilt.preimage (tensorInl ≫ t)⟩⟩ :
              (freeAb (sigma fun k ↦ reprBy (c k))).obj A) ⊗ₜ[ℤ]
            ofPoint (ψ := 𝟭 _) (tensorInr ≫ t) := by
        change (freeAb.prod _ _).app A (FreeAddCommGroup.of
          ((u pointOrTorus).app A
            ((sigma.ι (fun k ↦ tiltPointsSum pointOrTorus (ψ k)) j).app A
              ⟨⟨false⟩, ⟨t⟩⟩))) = _
        exact freeAb.desc_of ..
      exact congrArg (((abTensor (freeAb (sigma fun k ↦ reprBy (c k)))).map gluing).app A) h_prod
    have h_rhs_torus (A : PadicTest) (t : ψ j (monoidAlg ℚ) ⟶ tilt A) :
        ((abTensor (freeAb (sigma fun k ↦ reprBy (c k)))).map gluing).app A
            (rhsMap.app A (ofTorus t)) =
          (FreeAddCommGroup.of ⟨j, ⟨tilt.preimage (tensorInl ≫ t)⟩⟩ :
              (freeAb (sigma fun k ↦ reprBy (c k))).obj A) ⊗ₜ[ℤ]
            gluing.app A (ofTorus (ψ := 𝟭 _) (tensorInr ≫ t)) := by
      have h_prod : rhsMap.app A (ofTorus t) =
          (FreeAddCommGroup.of ⟨j, ⟨tilt.preimage (tensorInl ≫ t)⟩⟩ :
              (freeAb (sigma fun k ↦ reprBy (c k))).obj A) ⊗ₜ[ℤ]
            ofTorus (ψ := 𝟭 _) (tensorInr ≫ t) := by
        change (freeAb.prod _ _).app A (FreeAddCommGroup.of
          ((u pointOrTorus).app A
            ((sigma.ι (fun k ↦ tiltPointsSum pointOrTorus (ψ k)) j).app A
              ⟨⟨true⟩, ⟨t⟩⟩))) = _
        exact freeAb.desc_of ..
      exact congrArg (((abTensor (freeAb (sigma fun k ↦ reprBy (c k)))).map gluing).app A) h_prod
    have h_inl {X Y : CommAlg OFlat} (f : X ⟶ Y) :
        tensorInl ≫ (ψ j).map f = tensorInl :=
      CommAlgCat.hom_ext (Algebra.TensorProduct.map_comp_includeLeft (AlgHom.id _ _) f.hom)
    have h_inr {X Y : CommAlg OFlat} (f : X ⟶ Y) :
        tensorInr ≫ (ψ j).map f = f ≫ tensorInr :=
      CommAlgCat.hom_ext (Algebra.TensorProduct.map_comp_includeRight (AlgHom.id _ _) f.hom)
    apply freeAb.hom_ext
    rintro A ⟨⟨_ | _⟩, ⟨t⟩⟩
    · let t' : ψ j (CommAlgCat.of OFlat OFlat) ⟶ tilt A := t
      change lhsMap.app A ((gluing (ψ j)).app A (ofPoint t')) =
        ((abTensor (freeAb (sigma fun k ↦ reprBy (c k)))).map gluing).app A
          (rhsMap.app A (ofPoint t'))
      rw [gluing_ofPoint, h_lhs, h_rhs_point, gluing_ofPoint]
      rw [← Category.assoc, h_inl, ← Category.assoc, h_inr, Category.assoc]
      rfl
    · let t' : ψ j (monoidAlg ℚ) ⟶ tilt A := t
      change lhsMap.app A ((gluing (ψ j)).app A (ofTorus t')) =
        ((abTensor (freeAb (sigma fun k ↦ reprBy (c k)))).map gluing).app A
          (rhsMap.app A (ofTorus t'))
      have h_term (g : monoidAlg ℚ≥0 ⟶ monoidAlg ℚ) (b : ULift.{1} Bool) :
          (FreeAddCommGroup.of ⟨j, ⟨tilt.preimage (tensorInl ≫ ((ψ j).map g ≫ t'))⟩⟩ :
              (freeAb (sigma fun k ↦ reprBy (c k))).obj A) ⊗ₜ[ℤ]
            ofDisc (ψ := 𝟭 _) b (tensorInr ≫ ((ψ j).map g ≫ t')) =
          (FreeAddCommGroup.of ⟨j, ⟨tilt.preimage (tensorInl ≫ t')⟩⟩ :
              (freeAb (sigma fun k ↦ reprBy (c k))).obj A) ⊗ₜ[ℤ]
            ofDisc (ψ := 𝟭 _) b ((𝟭 (CommAlg OFlat)).map g ≫ (tensorInr ≫ t')) := by
        rw [← Category.assoc, h_inl, ← Category.assoc, h_inr, Category.assoc]
        rfl
      rw [gluing_ofTorus, _root_.map_sub, h_lhs, h_lhs, h_rhs_torus, gluing_ofTorus, tmul_sub]
      exact congrArg₂ (· - ·) (h_term _ _) (h_term _ _)
  refine (bijective_iff_of_comm_sq (fun x ↦ ?_) (hv_bijective _) (hv_bijective _)).2
    (.piMap fun j ↦ h_rep (c j) n)
  ext j
  simpa [← H.map_comp] using congrArg (fun φ ↦ map F φ n x) (h_square j)

end PerfectLine

end New.Variety

end
end
end

/-!
# Leray–Hirsch bases and the projective line formula for the tilted theory

The first part works over the tests `New.Variety.TestOver A` with coefficients killed by `ℓ`. Here
`A` is an absolutely integrally closed local domain in which the prime `ℓ` is invertible (the
instance `New.Variety.InvertsPrime A ℓ`). The projective line formula
(`New.Variety.TorsionCoeff.HasLineFormula`) says that the classes 1 and η identify Ext(S,
F) ⊕ Ext(S, F) with Ext(S, F) taken over the category of points of ℙ¹; here η is
`New.Variety.TorsionCoeff.cupClass`, the product with `New.Variety.etaClass` at the tautological
point of ℙ¹.

## Main definitions and results

* `New.Variety.isLerayHirschBasis_of_forall_isField`: bijectivity passes from the fields under a
  test to the test, given `New.Variety.IsDetectedAtPoints` (zero sets of classes are open;
  invariance under field extension).
* `New.Variety.exists_isLerayHirschBasis_of_isCohomDense`: a basis exists on the special fibre
  `New.Variety.IdealFamily.ofMaximalIdeal`.
* `New.Variety.isDetectedAtPoints_projLine`: the locally constant `ℤ/ℓ`-valued functions on pairs
  (test over `A`, point of ℙ¹) satisfy `New.Variety.IsDetectedAtPoints`.
* `New.Variety.exists_isTodaCancellation`: from a square `δ' ≫ i = i ≫ δ` with `i` a monomorphism,
  the product η of the classes of two short exact sequences is cancelled
  (`New.Variety.IsTodaCancellation`): after an exact functor that makes the cokernel of `i` acyclic,
  the product with a class ω is onto, and the pull-back of η m along `j` determines the pull-back of
  m along `ε`.
* `New.Variety.isLerayHirschBasis_lineBasis_of_injective`: two conditions on the product with η that
  give the formula at S.
* `New.Variety.hasLineFormula_tiltTheory`: the formula, from the cover of the perfect ℙ¹ by two
  discs.

Notions from other files:
* `New.Variety.TestOver`: The category of tests over A: the full subcategory of commutative
  A-algebras whose underlying rings are test rings.
* `New.Variety.lerayHirsch`: For classes θ_i in Ext^{d_i}(ΦG, F), the Leray–Hirsch map w ↦ Σ
  θ_i∘Φ(w_i) from finitely supported families in total Ext(S, G) to total Ext(ΦS, F);
  `New.Variety.IsLerayHirschBasis` says that it is bijective.
* `New.Variety.H`: The group Ext^n(N,F) in the category of functors from C to abelian groups.
* `New.Variety.projLine`: The projective line as a functor on rings: B goes to the set of points
  (1 + uv : v) with u, v in B, that is, pairs (u, v) modulo `New.Variety.projLineSetoid`.
* `New.Variety.freeAb`: The functor sending a set-valued functor Y to ℤ[Y], whose value at A is the
  free abelian group on Y(A).

## Relation to the literature

Known result: Künneth formula over a field for mod-ℓ étale cohomology, in Leray–Hirsch form. It is
proved here only over the special fibre of an absolutely integrally closed local domain. It states
that a basis of the cohomology over the residue field that contains a given non-zero class stays a
basis over every test ring of the special fibre. Source: SGA 4 XVII 5.4.3; Milne, Étale Cohomology
VI.8.

See also `Lib.Cohomology.ProjectiveLine.ConstantLineFormula`.
-/

@[expose] public section

/-! ## Leray–Hirsch bases over the special fibre and at points of tests -/

namespace New.Variety

open CategoryTheory IsLocalRing TotalH ObjectProperty Finsupp CommAlgCat Ideal NatIso
open Function hiding comp

variable {D : Type 1} [Category D] {ℓ : ℕ} {A : Type} [CommRing A] {g : D ⥤ TestOver A}

/-- For a local ring A, the compatible family of ideals on tests over A that assigns to a test B the
ideal of B generated by the image of the maximal ideal of A. Compatible means: for a map B → B', the
ideal at B' is generated by the image of the ideal at B. -/
noncomputable def IdealFamily.ofMaximalIdeal [IsLocalRing A] :
    IdealFamily (ringOf (𝟭 (TestOver A))) where
  ideal c := (maximalIdeal A).map (algebraMap A c.obj)
  map_eq f := (Ideal.map_map _ _).trans (congrArg (maximalIdeal A).map f.hom.hom'.comp_algebraMap)

/-- For a coefficient `F` that satisfies `New.Variety.IsDetectedAtPoints`, the set of primes `P` of
a test `c` at whose residue field a class `x` vanishes is open. -/
lemma IsDetectedAtPoints.isOpen_setOf_map_eq_zero {F : AbFunctor D}
    (h_detect : IsDetectedAtPoints g F) (c : TestOver A) (n : ℕ)
    (x : H (freeAb.obj (g ⋙ reprFunctor.obj (Opposite.op c))) F n) :
    IsOpen {P : PrimeSpectrum c.obj |
      H.map F (freeAb.map (g.whiskerLeft (reprMap (residueTest c P).hom))) n x = 0} :=
  (h_detect.isOpen_zero_set_and_eq_zero c n x).1

/-- For a coefficient `F` that satisfies `New.Variety.IsDetectedAtPoints`, a class `x` over a test
`c` that vanishes at the residue field of every prime of `c` is zero. -/
lemma IsDetectedAtPoints.eq_zero_of_setOf_map_eq_zero_eq_univ {F : AbFunctor D}
    (h_detect : IsDetectedAtPoints g F) (c : TestOver A) (n : ℕ)
    (x : H (freeAb.obj (g ⋙ reprFunctor.obj (Opposite.op c))) F n)
    (h_univ : {P : PrimeSpectrum c.obj |
      H.map F (freeAb.map (g.whiskerLeft (reprMap (residueTest c P).hom))) n x = 0} = Set.univ) :
    x = 0 :=
  (h_detect.isOpen_zero_set_and_eq_zero c n x).2 h_univ

/-- The Yoneda isomorphism `sectionEquiv` is natural: for `φ : e ⟶ e'`, pulling the class of a
section `t ∈ G(e)` back along `ℤ[h_e'] → ℤ[h_e]` gives the class of the image of `t` in `G(e')`. -/
lemma TotalH.comp_homClass_sectionEquiv (G : AbFunctor D) {e e' : D} (φ : e ⟶ e') (t : G e) :
    comp (homClass (freeAb.map (reprMap φ))) (sectionEquiv G e t) =
      sectionEquiv G e' (G.map φ t) := by
  -- Both sides are classes of maps out of `ℤ[h_e']`, which send the identity of `e'` to `φ t`.
  have h_hom : freeAb.map (reprMap φ) ≫ (homReprEquiv e G).symm t =
      (homReprEquiv e' G).symm (G.map φ t) :=
    (homReprEquiv e' G).eq_symm_apply.2
      ((add_zero _).trans (congrArg (fun ψ : e ⟶ e' ↦ G.map ψ t) (Category.comp_id φ)))
  exact (homClass_comp _).symm.trans (congrArg homClass h_hom)

/-- Bijectivity of the Leray–Hirsch map passes from the fields under a test to the test. Here `g` is
a functor from `D` to tests over `A` (`InvertsPrime A ℓ`: `A` is local and absolutely integrally
closed, with `ℓ` invertible in it), and `F`, a functor from `D` to abelian groups, satisfies
`New.Variety.IsDetectedAtPoints`: at the primes of a test, the zero set of a class is open, and a
class that vanishes at every prime is zero. With `L` the functor of locally constant `ℤ/ℓ`-valued
functions on the spectrum, `θ i ∈ Ext^{d i}(L ∘ g, F)` for `i : I`, and `ℤ[h_k]` the free abelian
functor on `h_k = Hom(k, −)` (`reprBy k`) on tests over `A`: if the Leray–Hirsch map
`New.Variety.lerayHirsch` of the family `θ` is bijective at `ℤ[h_k]` for every test `k` that is a
field and receives a map from `c`, then it is bijective at `ℤ[h_c]`. -/
lemma isLerayHirschBasis_of_forall_isField [InvertsPrime A ℓ] {F : AbFunctor D} {I : Type*}
    {d : I → ℕ} (h_detect : IsDetectedAtPoints g F)
    {θ : (i : I) → H ((restrictAlong g).obj (locConstAlong (𝟭 (TestOver A)))) F (d i)}
    {c : TestOver A}
    (h_field : ∀ k : TestOver A, (c ⟶ k) → IsField k.obj →
      IsLerayHirschBasis θ (freeAb (reprBy k))) :
    IsLerayHirschBasis θ (freeAb (reprBy c)) := by
  classical
  -- At each prime `P` of `c` a class `y` has unique coefficients `coef P` in `ZMod ℓ`. By
  -- `IsDetectedAtPoints` they are locally constant in `P`, so they form a preimage of `y`, the only
  -- one. `s e` reads families of locally constant functions as classes (Yoneda), and `E P` is the
  -- Leray–Hirsch bijection at the residue field, where these functions are constants.
  let L (e : TestOver A) : Type 1 := ULift.{1} (LocallyConstant (PrimeSpectrum e.obj) (ZMod ℓ))
  let s (e : TestOver A) :
      (I →₀ L e) ≃+ (I →₀ TotalH (freeAb (reprBy e)) (locConstAlong (𝟭 (TestOver A)))) :=
    mapRange.addEquiv (sectionEquiv (locConstAlong (𝟭 (TestOver A))) e)
  let const (P : PrimeSpectrum c.obj) : (I →₀ ZMod ℓ) → (I →₀ L (residueTest c P).right) :=
    mapRange (fun a : ZMod ℓ ↦ ⟨.const _ a⟩) rfl
  have h_const (P : PrimeSpectrum c.obj) : Bijective (const P) :=
    mapRange_bijective _ rfl (bijective_const_of_isDomain (B := .of P.asIdeal.ResidueField))
  have h_residue (P : PrimeSpectrum c.obj) :
      Bijective (lerayHirsch θ (freeAb (reprBy (residueTest c P).right))) :=
    h_field _ (residueTest c P).hom (Field.toIsField P.asIdeal.ResidueField)
  let E (P : PrimeSpectrum c.obj) :
      (I →₀ ZMod ℓ) ≃ TotalH (restrictAlong g (freeAb (reprBy (residueTest c P).right))) F :=
    .ofBijective (lerayHirsch θ _ ∘ s (residueTest c P).right ∘ const P)
      ((h_residue P).comp ((s _).bijective.comp (h_const P)))
  let r (P : PrimeSpectrum c.obj) : freeAb (reprBy (residueTest c P).right) ⟶ freeAb (reprBy c) :=
    freeAb.map (reprMap (residueTest c P).hom)
  let ev (P : PrimeSpectrum c.obj) (m : I →₀ L c) : I →₀ ZMod ℓ :=
    mapRange (fun t : L c ↦ t.down P) rfl m
  -- Restriction `r P` to the residue field at `P` evaluates the coefficients at `P`.
  have restrict_lh (m : I →₀ L c) (P : PrimeSpectrum c.obj) :
      pullbackAlong ((restrictAlong g).map (r P)) (lerayHirsch θ _ (s c m)) = E P (ev P m) := by
    -- `m i` restricted to the residue field at `P` is the constant function `m i P`.
    have h_value (i : I) : (locConstAlong (𝟭 (TestOver A))).map (residueTest c P).hom (m i) =
        const P (ev P m) i :=
      congrArg ULift.up (LocallyConstant.ext fun Q ↦
        congrArg (m i).down (P.residueField_comap.le ⟨Q, rfl⟩))
    have h_family : (s c m).mapRange (comp (homClass (r P))) (map_zero _) =
        s (residueTest c P).right (const P (ev P m)) := by
      refine ext fun i ↦ ?_
      change comp (homClass (r P)) (sectionEquiv (locConstAlong (𝟭 (TestOver A))) c (m i)) =
        sectionEquiv (locConstAlong (𝟭 (TestOver A))) (residueTest c P).right (const P (ev P m) i)
      rw [← h_value i]
      exact comp_homClass_sectionEquiv (locConstAlong (𝟭 (TestOver A))) (residueTest c P).hom (m i)
    rw [← lerayHirsch_mapRange_comp θ (map_homClass (f := r P)) (s c m), h_family]
    rfl
  refine ((s c).bijective_comp _).mp ((bijective_iff_existsUnique _).mpr fun y ↦ ?_)
  let coef (P : PrimeSpectrum c.obj) : I →₀ ZMod ℓ :=
    (E P).symm (pullbackAlong ((restrictAlong g).map (r P)) y)
  -- `m` has the coefficients of `y` at `P` iff the difference vanishes at `P` in every degree.
  have coef_iff (m : I →₀ L c) (P : PrimeSpectrum c.obj) : coef P = ev P m ↔
      ∀ n : ℕ, H.map F ((restrictAlong g).map (r P)) n ((y - lerayHirsch θ _ (s c m)) n) = 0 := by
    rw [Equiv.symm_apply_eq, ← restrict_lh, ← sub_eq_zero, ← map_sub, pullbackAlong_eq_map]
    exact DFinsupp.ext_iff
  -- Near `P`, compare with the constant functions `coef P`: finitely many degrees matter, and
  -- the zero set of each is open.
  have hloc : IsLocallyConstant coef := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun P ↦ ?_
    let m : I →₀ L c := mapRange (fun a ↦ ⟨.const _ a⟩) rfl (coef P)
    have ev_m (Q : PrimeSpectrum c.obj) : ev Q m = coef P := ext fun _ ↦ rfl
    -- the difference `z` has finitely many non-zero degrees, and each vanishes near `P`
    let z : TotalH (restrictAlong g (freeAb (reprBy c))) F := y - lerayHirsch θ _ (s c m)
    have h_near (n : ℕ) :
        ∀ᶠ Q in nhds P, H.map F ((restrictAlong g).map (r Q)) n (z n) = 0 :=
      (h_detect.isOpen_setOf_map_eq_zero c n (z n)).mem_nhds ((coef_iff m P).mp (ev_m P).symm n)
    filter_upwards [(DFinsupp.finite_support z).eventually_all.mpr fun n _ ↦ h_near n] with Q hQ
    refine ((coef_iff m Q).mpr fun n ↦ ?_).trans (ev_m Q)
    by_cases h_zero : z n = 0
    · rw [h_zero, map_zero]
    · exact hQ n h_zero
  -- The spectrum is compact, so `coef` takes finitely many values and has finite total support.
  let t : Finset I := hloc.range_finite.toFinset.sup support
  have h_coef_zero (i : I) (hi : i ∉ t) (P : PrimeSpectrum c.obj) : coef P i = 0 := by
    by_contra h_ne
    exact hi (Finset.mem_sup.mpr
      ⟨coef P, hloc.range_finite.mem_toFinset.mpr ⟨P, rfl⟩, Finsupp.mem_support_iff.mpr h_ne⟩)
  let m : I →₀ L c := .onFinset t (fun i ↦ ⟨⟨fun P ↦ coef P i, hloc.comp fun w ↦ w i⟩⟩) fun i ↦
    not_imp_comm.mp fun hi ↦ congrArg ULift.up (LocallyConstant.ext (h_coef_zero i hi))
  refine ⟨m, (sub_eq_zero.mp (DFinsupp.ext fun n ↦ ?_)).symm, fun m' hm' ↦ ?_⟩
  · -- `y - lerayHirsch θ _ (s c m)` vanishes at every prime, hence is zero
    exact h_detect.eq_zero_of_setOf_map_eq_zero_eq_univ c n _
      (top_unique fun P _ ↦ (coef_iff m P).mp (ext fun _ ↦ rfl) n)
  · ext i P
    have h_coef : coef P = ev P m' := (coef_iff m' P).mpr fun n ↦ by simp [← hm']
    exact (DFunLike.congr_fun h_coef i).symm

-- Keeps definitional checks from unfolding the group structure of the Ext groups.
seal addCommGroupH in
/-- A Leray–Hirsch basis over the special fibre. Here `A` is an absolutely integrally closed local
domain in which `ℓ` is invertible (the instance `New.Variety.InvertsPrime A ℓ`), and `g` is a
functor from `D` to tests over `A`. Let `M` be an `ℓ`-torsion coefficient along `g`
(`New.Variety.TorsionCoeff`). It satisfies `New.Variety.IsDetectedAtPoints`: classes in
Extⁿ(ℤ[Hom(c, g –)], M) are detected by their restrictions to the residue fields of c. Also, the
locus of tests where the maximal ideal 𝔪_A of `A` generates the zero ideal is dense
(`New.Variety.IsCohomDense`). Let `L` be the functor of locally constant `ℤ/ℓ`-valued functions. A
homogeneous class of Ext(L ∘ g, M) is a pair (degree, class), and `j` is one of them. Then there is
a set `b` of such classes with two properties: (a) `j ∈ b` if the value of `j` at the constant
function 1 is not zero; (b) the Leray–Hirsch map of `b` is bijective at ℤ[h_c], the free abelian
functor on h_c = Hom(c, −) (`reprBy c`), for every test `c` in which 𝔪_A generates the zero ideal;
this is what `⟨⟩ ∈ IdealFamily.ofMaximalIdeal.botLocus c` says. -/
lemma exists_isLerayHirschBasis_of_isCohomDense [InvertsPrime A ℓ] (M : TorsionCoeff g)
    (h_detect : IsDetectedAtPoints g M.functor)
    (h_dense : IsCohomDense M.functor (IdealFamily.ofMaximalIdeal.botLocus.whisker g))
    (j : (n : ℕ) × H ((restrictAlong g).obj (locConstAlong (𝟭 (TestOver A)))) M.functor n) :
    ∃ b : Set (Σ n : ℕ, H (restrictAlong g (locConstAlong (𝟭 (TestOver A)))) M.functor n),
      -- (a)
      (pullbackAlong oneLocConst j.snd.toTotalH ≠ 0 → j ∈ b) ∧
      -- (b)
      ∀ c : TestOver A,
        ⟨⟩ ∈ IdealFamily.ofMaximalIdeal.botLocus c →
        IsLerayHirschBasis (fun i : b ↦ i.val.snd) (freeAb (reprBy c)) := by
  -- The values `u i = i(1)` of homogeneous classes span the cohomology of the point, a vector
  -- space over `ZMod ℓ`. Let `b` index a basis among them, containing `j` if `u j ≠ 0`.
  let module_zmod {N : AbFunctor D} : Module (ZMod ℓ) (TotalH N M.functor) :=
    AddCommGroup.zmodModule M.nsmul_totalH_eq_zero
  let u (i : Σ n : ℕ, H (locConstAlong g) M.functor n) :
    TotalH (freeAb (onePointFunctor D)) M.functor :=
    pullbackAlong oneLocConst i.snd.toTotalH
  -- `{j} ∩ u.support` is empty if `u j = 0`, and `{j}` with `u j ≠ 0` otherwise.
  have hj : LinearIndepOn (ZMod ℓ) u ({j} ∩ u.support) := by
    by_cases h_uj : u j = 0
    · simp [h_uj]
    · rw [Set.singleton_inter_of_mem (Function.mem_support.2 h_uj)]
      exact .singleton h_uj
  obtain ⟨b, -, h_jb, h_span, h_indep⟩ := exists_linearIndepOn_extension hj (Set.subset_univ _)
  -- Every class of the point is pulled back along `oneLocConst`
  -- (`TorsionCoeff.pullbackAlong_oneLocConst_surjective`), so the `u i` span.
  have h_basis : Bijective (linearCombination (ZMod ℓ) fun i : b ↦ u i) := by
    refine ⟨h_indep, M.pullbackAlong_oneLocConst_surjective.forall.2 fun x ↦ ?_⟩
    refine (range_linearCombination _).ge ?_
    rw [← b.image_eq_range u]
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n x => exact h_span ⟨⟨n, x⟩, Set.mem_univ _, rfl⟩
    | add x y hx hy => simpa using add_mem hx hy
  -- A test kills the maximal ideal iff it receives a map, then unique, from the residue field `k₀`.
  -- So `reprBy k₀` is the dense locus, and `reprBy k₀ ⟶ onePointFunctor` is an equivalence for
  -- `M.functor`.
  let k₀ : TestOver A := ⟨of A (ResidueField A), isTest_of_preValuationRing⟩
  let f {c : TestOver A} (hc : ⟨⟩ ∈ IdealFamily.ofMaximalIdeal.botLocus c) : k₀ ⟶ c :=
    ⟨ofHom (Quotient.liftₐ (maximalIdeal A) (Algebra.ofId A c.obj)
      ((map_eq_bot_iff_le_ker _).1 hc))⟩
  -- both are maps of `A`-algebras out of the quotient `A ⧸ 𝔪_A`
  have h_unique {c : TestOver A} (α β : k₀ ⟶ c) : α = β :=
    ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (Quotient.algHom_ext _ (by ext)))
  have hk₀ : IsCohomEquiv M.functor (freeAb.map (toUnit (g ⋙ reprBy k₀))) := by
    -- at each object the map from the preimage of the locus is bijective: one-to-one since maps
    -- out of `k₀` are unique, and onto since `f hc` lies over each point of the locus
    refine h_dense.isCohomEquiv_of_fromPreimage (.of_bijective fun a ↦
      ⟨fun φ φ' _ ↦ Subtype.ext (ULift.down_injective (h_unique _ _)), ?_⟩)
    rintro ⟨_, hc⟩
    exact ⟨⟨⟨f hc⟩, hc⟩, rfl⟩
  -- By `isLerayHirschBasis_of_forall_isField` it suffices to treat a field `k` under `c`; then
  -- `reprBy k ⟶ reprBy k₀ ⟶ onePointFunctor` is an equivalence for `M.functor`.
  refine ⟨b, fun h_ne ↦ h_jb ⟨Set.mem_singleton j, h_ne⟩,
    fun c hc ↦ isLerayHirschBasis_of_forall_isField h_detect fun k φ hk ↦ ?_⟩
  let ψ : k₀ ⟶ k := f (IdealFamily.ofMaximalIdeal.botLocus.map φ hc)
  -- `α` is the map `ℤ[h_k ∘ g] → ℤ[h_k₀ ∘ g] → ℤ[pt]`
  let α : freeAb (g ⋙ reprBy k) ⟶ freeAb (onePointFunctor D) :=
    freeAb.map (g.whiskerLeft (reprMap ψ)) ≫ freeAb.map (toUnit (g ⋙ reprBy k₀))
  have hpt : IsCohomEquiv M.functor α :=
    (h_detect.isCohomEquiv_map_of_isField k₀ k ψ (Field.toIsField _) hk).comp_iff.2 hk₀
  -- The locally constant functions on a point are the constants.
  have h_domain : IsDomain (testIncl.obj ((TestOver.toTest A).obj ((𝟭 (TestOver A)).obj k))) :=
    hk.isDomain
  let e : ZMod ℓ ≃+ TotalH (freeAb (reprBy k)) (locConstAlong (𝟭 (TestOver A))) :=
    .trans ⟨.ofBijective _ bijective_const_of_isDomain, fun _ _ ↦ rfl⟩
      (sectionEquiv (locConstAlong (𝟭 (TestOver A))) k)
  -- `e 1`, restricted along `g`, is the class of the map `ℤ[h_k ∘ g] → L ∘ g` that sends every
  -- generator to the constant function `1`.
  have h_one : TotalH.map (restrictAlong g) (e 1) = homClass (α ≫ oneLocConst) :=
    -- the two maps out of `ℤ[h_k ∘ g]` agree on generators
    map_homClass.trans (congrArg homClass (freeAb.hom_ext (Y := g ⋙ reprBy k)))
  have h_one_apply
      (x : TotalH ((restrictAlong g).obj (locConstAlong (𝟭 (TestOver A)))) M.functor) :
      comp (TotalH.map (restrictAlong g) (e 1)) x = pullbackAlong (α ≫ oneLocConst) x := by
    rw [h_one]
    rfl
  -- Both sides of the square are sums over `i ∈ b`; the summands agree, since both are additive
  -- in the coefficient `a`, which leaves `a = 1`, where `h_one` applies.
  have h_summand (i : b) (a : ZMod ℓ) :
      comp (TotalH.map (restrictAlong g) (e a)) i.val.snd.toTotalH =
        pullbackAlong α (a • u i.val) := by
    rw [← a.natCast_zmod_val]
    simp only [← nsmul_one, map_nsmul, AddMonoidHom.smul_apply, h_one_apply, smul_assoc, one_smul,
      pullbackAlong_pullbackAlong, u]
    -- the two sides now differ only in the instance of scalar multiplication by `ℕ`
    rfl
  -- Under these two bijections the Leray–Hirsch map is the linear combination of the `u i`.
  refine (Comparison.bijective_iff_of_comm_sq (fun w ↦ ?_) (mapRange.addEquiv e).bijective
      hpt.bijective_pullbackAlong).1 h_basis
  -- Both sides are sums over the support of `w`, with the summands of `h_summand`.
  have h_sum : (w.sum fun (i : b) (a : ZMod ℓ) ↦
        comp (TotalH.map (restrictAlong g) (e a)) i.val.snd.toTotalH) =
      w.sum fun (i : b) (a : ZMod ℓ) ↦ pullbackAlong α (a • u i.val) :=
    sum_congr fun i _ ↦ h_summand i (w i)
  -- `using!`: the restriction of `ℤ[h_k]` along `g` is `ℤ[h_k ∘ g]` by definition.
  simpa [lerayHirsch, sum_mapRange_index, linearCombination, map_finsuppSum]
    using! h_sum

/-! ## Tests over A: covering points and the projective line -/

/-- Every A-algebra B is covered by one test: there are a test c over A and an A-algebra map
B → c through which every A-algebra map from B to a test factors. Here the functor is the
inclusion `ι` of tests over A into commutative A-algebras. -/
instance TestOver.hasCoveringPoints : HasCoveringPoints (ι _ : TestOver A ⥤ CommAlg A) := by
  refine ⟨fun B _ _ ↦ ?_⟩
  -- `c` is the envelope `E B`, a test ring, made an `A`-algebra through `η : B → E B`.
  obtain ⟨E, η, hE, hfac⟩ := Envelope.exists_natTrans_isTest_and_factors
    ![(forget₂ _ CommRingCat) B]
  let := ((η (.of B)).hom.comp (algebraMap A B)).toAlgebra
  let c : TestOver A := ⟨of A (E (.of B)), hE _⟩
  let y : B ⟶ c.obj := ofHom ⟨(η (.of B)).hom, fun _ ↦ rfl⟩
  refine ⟨c, ⟨y⟩, fun c' φ ↦ ?_⟩
  -- A point `φ` of `B` in a test factors as `η ≫ ψ`, and `ψ` is a map of `A`-algebras.
  obtain ⟨ψ, hψ⟩ := hfac 0 ⟨_, c'.property⟩ ((forget₂ ..).map φ.down)
  exact ⟨⟨⟨CommAlg.homOfRingHom ψ.hom fun a ↦ congr($hψ _).trans (φ.down.hom'.commutes' a)⟩⟩,
    congr(⟨ofHom ⟨$(hψ).hom', _⟩⟩)⟩

/-- A power ℙ¹^J of the projective line, as a functor on A-algebras, is affinely covered along the
inclusion `ι` of tests over A (`New.Variety.IsAffinelyCovered`): it is separated, and the affine
space with coordinates u_i, v_i (i ∈ J) carries a point whose images cover the points over every
test. -/
lemma isAffinelyCovered_projLinePow {J : Type} :
    IsAffinelyCovered (ι _ : TestOver A ⥤ CommAlg A)
      (forget₂ (CommAlg A) CommRingCat ⋙ projLinePow J) := by
  -- The product of lines is separated by `isProperOver_projLinePow`, and it is covered by the
  -- affine space of all families of pairs `(u, v)`, each giving the point `(1 + uv : v)`.
  refine ⟨⟨fun R x y ↦ ?_⟩, of A (MvPolynomial (J ⊕ J) A),
    fun i ↦ ⟨⟦(.X (.inl i), .X (.inr i))⟧⟩, fun c x ↦ ?_⟩
  · exact ((isProperOver_projLinePow J).diagonal_closed _ x y).imp fun I hI R' φ ↦ hI _ _
  · -- send the variables to the entries of pairs `(u, v)` chosen to represent the points `x i`
    let ψ : MvPolynomial (J ⊕ J) A →ₐ[A] c.obj :=
      MvPolynomial.aeval (Sum.elim (fun i ↦ (x i).down.out.1) fun i ↦ (x i).down.out.2)
    have hψ (i : J) : ⟦(ψ (.X (.inl i)), ψ (.X (.inr i)))⟧ = (x i).down := by simp [ψ]
    exact ⟨⟨ofHom ψ⟩, funext fun i ↦ ULift.down_injective (hψ i)⟩

/-- If `A` is an absolutely integrally closed local ring in which the prime `ℓ` is invertible
(`InvertsPrime A ℓ`), the locally constant `ℤ/ℓ`-valued functions on pairs (test over `A`, point
of the projective line) satisfy `New.Variety.IsDetectedAtPoints`: zero sets of classes are open,
a class that vanishes at every prime is zero, and maps of fields induce bijections. -/
lemma isDetectedAtPoints_projLine [InvertsPrime A ℓ] :
    IsDetectedAtPoints (testOfPoint A projLine) (locConstAlong (testOfPoint A projLine)) := by
  -- The line is the product of lines indexed by `Unit`, which is proper over ℤ through `p`.
  obtain ⟨p, h_prod⟩ : ∃ p : projLinePow Unit ⟶ reprBy (CommRingCat.of ℤ), IsProperOver p :=
    ⟨_, isProperOver_projLinePow Unit⟩
  let iso : projLinePow Unit ≅ projLine := ofComponents fun R ↦ (Equiv.funUnique Unit _).toIso
  -- Properness passes along the isomorphism, seen as a pull-back square over the identity.
  have h_square : IsPullback iso.inv iso.inv (𝟙 (projLinePow Unit)) (𝟙 (projLinePow Unit)) :=
    .of_vert_isIso ⟨rfl⟩
  have h_line : IsProperOver (iso.inv ≫ p) :=
    h_prod.of_isPullback (hW := h_prod) (h_pb := h_square) (hY := h_prod) (ψ := 𝟙 _) rfl
  -- Proper base change for the zero family of ideals, whose zero locus is everything, and the
  -- identity map of coefficients.
  let I : IdealFamily
      (elementsProj (MonoidalCategory.tensorObj projLine (reprBy (CommRingCat.of A)))) :=
    ⟨⊥, by simp⟩
  have h_dense : IsCohomDense (locConstAlong (testOfPoint A projLine)) I.pullToTests.botLocus :=
    .of_top_le fun _ _ _ ↦ rfl
  exact I.isDetectedAtPoints_of_proper h_line (𝟙 _) (fun _ _ ↦ bijective_id) h_dense

end New.Variety

/-!
## Squares, a criterion for the line formula, and the tilted theory

`New.Variety.TotalH` is total Ext with Yoneda product `New.Variety.TotalH.comp` in diagrammatic
order; `New.Variety.TorsionCoeff.mulClass` is the product with a class valued in the Tate module,
and `New.Variety.sliceEquiv` passes from S ⊗ ℤ[X] to S over the category of points of X.
-/

section TiltedLineFormula

namespace New.Variety

open CategoryTheory Limits Abelian TotalH PerfectLine projLine Finsupp
open ShortComplex (exact_cokernel ShortExact)
open Function hiding comp comp_id comp_assoc

variable {C : Type 1} [Category.{0} C] {W' W Z₀ : AbFunctor C} {S T : ShortComplex (AbFunctor C)}

/-- Let `B → W → I → B` (maps `a`, `b`, `c`) and `I → P → K → I` (maps `d`, `e`, `f`) be two
triangles of additive groups that meet at `I`. The hypothesis `h_first` says that the first is exact
at `W`, `I` and `B`, and `h_second` that the second is exact at `P`, `K` and `I`. If the path
`d ∘ b` from `W` to `P` is bijective, then so is the path `c ∘ f` from `K` to `B`. -/
lemma TotalH.bijective_of_two_triangles {K P I W B : Type*} [AddGroup K] [AddGroup P]
    [AddGroup I] [AddGroup W] [AddGroup B] {a : B → W} {b : W →+ I} {c : I →+ B} {d : I →+ P}
    {e : P → K} {f : K →+ I} (h_first : Exact a b ∧ Exact b c ∧ Exact c a)
    (h_second : Exact d e ∧ Exact e f ∧ Exact f d) (h_bij : Bijective (d.comp b)) :
    Bijective (c.comp f) := by
  obtain ⟨hab, hbc, hca⟩ := h_first
  obtain ⟨hde, hef, hfd⟩ := h_second
  obtain ⟨h_inj, h_surj⟩ := h_bij
  -- As `d ∘ b` is onto, `d` is onto, so `e = 0` and `f` is injective; as `d ∘ b` is injective,
  -- `a = 0` and `c` is onto.
  have h_e_zero : ∀ p, e p = 0 :=
    h_surj.forall.2 fun w ↦ hde.apply_apply_eq_zero (b w)
  have h_zero_of_db (w : W) (hw : d (b w) = 0) : w = 0 := (injective_iff_map_eq_zero _).1 h_inj w hw
  constructor
  · -- If `c (f x) = 0` then `f x = b w` with `d (b w) = d (f x) = 0`; so `w = 0` and `f x = 0`.
    refine (injective_iff_map_eq_zero (c.comp f)).2 fun x hx ↦ ?_
    obtain ⟨w, hw⟩ : ∃ w : W, b w = f x := (hbc (f x)).1 hx
    obtain rfl : w = 0 := h_zero_of_db w (by rw [hw, hfd.apply_apply_eq_zero x])
    obtain ⟨p, rfl⟩ := (hef x).1 (by rw [← hw, map_zero])
    exact h_e_zero p
  · -- Write `y = c r` and correct `r` by some `b w` so that it lies in the kernel of `d`.
    intro y
    obtain ⟨r, rfl⟩ : ∃ r : I, c r = y :=
      (hca y).1 (h_zero_of_db (a y) (by rw [hab.apply_apply_eq_zero y, map_zero]))
    obtain ⟨w, hw⟩ : ∃ w : W, d (b w) = d r := h_surj (d r)
    obtain ⟨x, hx⟩ : ∃ x : K, f x = r - b w := (hfd (r - b w)).1 (by simp [hw])
    exact ⟨x, by simp [hx, hbc.apply_apply_eq_zero]⟩

/-- Fix `i : W' ⟶ W`, `δ : W ⟶ W`, `q : W ⟶ X`, a class `η ∈ Ext²(X, Y)` and `ε : Z₀ ⟶ Y`.
The maps `j : B ⟶ X`, `y : Z₀ ⟶ K` and the class `ω ∈ Ext(B, K)` cancel `η` if `j` has a lifting
property and, after any exact functor `Φ` that makes the cokernel of `i` acyclic for a
coefficient `F`, the product with `ω` is onto and `j^* (η m)` determines `ε^* m`. -/
structure IsTodaCancellation {X Y B K : AbFunctor C} (i : W' ⟶ W) (δ : W ⟶ W) (q : W ⟶ X)
    (η : H X Y 2) (ε : Z₀ ⟶ Y) (j : B ⟶ X) (y : Z₀ ⟶ K) (ω : TotalH B K) : Prop where
  /-- If `g` kills `i` and `δ` and `g ≫ r = q ≫ s`, then `j ≫ s` lifts along `r`. -/
  exists_lift {Q R : AbFunctor C} (g : W ⟶ Q) (r : Q ⟶ R) (s : X ⟶ R) (hi : i ≫ g = 0)
    (hδ : δ ≫ g = 0) (hr : g ≫ r = q ≫ s) : ∃ t : B ⟶ Q, t ≫ r = j ≫ s
  /-- After `Φ`, if `j^* (η m) = ω s`, then `ε^* m = y^* s`. -/
  pullback_eq {E : Type 1} [Category.{0} E] (Φ : AbFunctor C ⥤ AbFunctor E) [IsExactFunctor Φ]
    {F : AbFunctor E} (h_acyclic : ∀ n : ℕ, Subsingleton (H (Φ (cokernel i)) F n))
    (m : TotalH (Φ Y) F) (s : TotalH (Φ K) F)
    (h_eq : pullbackAlong (Φ.map j) (comp (TotalH.map Φ η.toTotalH) m) = comp (TotalH.map Φ ω) s) :
    pullbackAlong (Φ.map ε) m = pullbackAlong (Φ.map y) s
  /-- After `Φ`, the product `s ↦ ω s` is onto. -/
  surjective {E : Type 1} [Category.{0} E] (Φ : AbFunctor C ⥤ AbFunctor E) [IsExactFunctor Φ]
    {F : AbFunctor E} (h_acyclic : ∀ n : ℕ, Subsingleton (H (Φ (cokernel i)) F n)) :
    Surjective (comp (F := F) (TotalH.map Φ ω))

/-- After `Φ`, if `j^* (η m) = ω s`, then `ε^* m` and `y^* s` have the same pull-back along
every `τ`. -/
lemma IsTodaCancellation.pullbackAlong_comp_map_eq {X Y B K : AbFunctor C} {i : W' ⟶ W} {δ : W ⟶ W}
    {q : W ⟶ X} {η : H X Y 2} {ε : Z₀ ⟶ Y} {j : B ⟶ X} {y : Z₀ ⟶ K} {ω : TotalH B K}
    (h_toda : IsTodaCancellation i δ q η ε j y ω) {E : Type 1} [Category.{0} E]
    (Φ : AbFunctor C ⥤ AbFunctor E) [IsExactFunctor Φ] {F N : AbFunctor E}
    (h_acyclic : ∀ n : ℕ, Subsingleton (H (Φ (cokernel i)) F n)) (τ : N ⟶ Φ Z₀)
    (m : TotalH (Φ Y) F) (s : TotalH (Φ K) F)
    (h_eq : pullbackAlong (Φ.map j) (comp (TotalH.map Φ η.toTotalH) m) = comp (TotalH.map Φ ω) s) :
    pullbackAlong (τ ≫ Φ.map ε) m = pullbackAlong (τ ≫ Φ.map y) s := by
  rw [← pullbackAlong_pullbackAlong, ← pullbackAlong_pullbackAlong,
    h_toda.pullback_eq Φ h_acyclic m s h_eq]

/-- Let `δ' ≫ i = i ≫ δ` with `i` a monomorphism, and let `Φ` be an exact functor after which the
cokernel of `i` has no Ext into `F` in any degree. Then `Φ` of the map `(i, δ)` out of the
pushout of `δ'` and `i` is an equivalence for `F`: it induces bijections on `Ext(–, F)`. -/
lemma isCohomEquiv_pushout_desc {i : W' ⟶ W} [Mono i] {δ' : W' ⟶ W'} {δ : W ⟶ W}
    (h_comm : δ' ≫ i = i ≫ δ) {E : Type 1} [Category.{0} E] (Φ : AbFunctor C ⥤ AbFunctor E)
    [IsExactFunctor Φ] {F : AbFunctor E}
    (h_acyclic : ∀ n : ℕ, Subsingleton (H (Φ (cokernel i)) F n)) :
    IsCohomEquiv F (Φ.map (pushout.desc i δ h_comm)) := by
  -- `i` and `pushout.inl` have the same acyclic cokernel, so both are equivalences, and
  -- `pushout.inl` followed by `(i, δ)` is `i`.
  have h_eqv {M N : AbFunctor C} (g : M ⟶ N) [Mono g]
      (hg : ∀ k : ℕ, Subsingleton (H (Φ (cokernel g)) F k)) : IsCohomEquiv F (Φ.map g) :=
    (isCohomEquiv_iff_subsingleton (.map ⟨exact_cokernel g⟩ Φ)).2 hg
  have h_sq : IsPushout i δ' (pushout.inr δ' i) (pushout.inl δ' i) :=
    (IsPushout.of_hasPushout δ' i).flip
  let e := cokernel.map i (pushout.inl δ' i) δ' (pushout.inr δ' i) h_sq.w.symm
  have h_iso : IsIso e := isIso_cokernel_map_of_isPushout h_sq
  have h_inl : IsCohomEquiv F (Φ.map (pushout.inl δ' i)) :=
    h_eqv (pushout.inl δ' i) fun k ↦
      (IsCohomEquiv.of_isIso (Φ.map (inv e)) k).surjective.subsingleton
  refine h_inl.comp_iff.1 ?_
  rw [← Φ.map_comp, pushout.inl_desc]
  exact h_eqv i h_acyclic

-- Keeps definitional checks from unfolding the group structure of the Ext groups.
seal addCommGroupH in
/-- Lemma on squares, for short exact `S`, `T`: let `i` be mono with `δ' ≫ i = i ≫ δ`, `z ≫ δ = 0`,
`f : W ⟶ S.X₂` with `δ ≫ f = 0` and `i ≫ f = α₁ ≫ S.f`, and `α` with `α ≫ T.g = α₁ ≫ n` and
`δ' ≫ α = i ≫ κ ≫ T.f`. Let `η` be the extension class of `S` times that of `T` pulled back along
`n`, and set `q = f ≫ S.g` and `ε = z ≫ κ`. Then there are `j : B ⟶ S.X₃`, `y : Z₀ ⟶ K` and
`ω ∈ Ext(B, K)` that cancel `η` (`New.Variety.IsTodaCancellation`): `j` has the lifting property,
and after any exact functor that makes `coker i` acyclic for a coefficient F, the product with `ω`
is onto and `j^*(η m)` determines `ε^* m`. -/
lemma exists_isTodaCancellation {i : W' ⟶ W} [Mono i] {δ' : W' ⟶ W'} {δ : W ⟶ W}
    (h_comm : δ' ≫ i = i ≫ δ) (z : Z₀ ⟶ W) (hz : z ≫ δ = 0) (hS : S.ShortExact) (hT : T.ShortExact)
    (f : W ⟶ S.X₂) (α : W' ⟶ T.X₂) (κ : W ⟶ T.X₁) (n : S.X₁ ⟶ T.X₃) (α₁ : W' ⟶ S.X₁)
    (hα₁ : α₁ ≫ S.f = i ≫ f) (hδf : δ ≫ f = 0) (hα : δ' ≫ α = i ≫ κ ≫ T.f) (hn : α₁ ≫ n = α ≫ T.g) :
    ∃ (B K : AbFunctor C) (j : B ⟶ S.X₃) (y : Z₀ ⟶ K) (ω : TotalH B K),
      IsTodaCancellation i δ (f ≫ S.g) (hS.extClass.comp (H.map T.X₁ n 1 hT.extClass) rfl)
        (z ≫ κ) j y ω := by
  -- Let `σ` be the map `(i, δ)` out of the pushout `P` of `δ'` and `i`. Then `ω` is the class
  -- of `0 → ker σ → P → W → coker → 0`, the product of the classes of its halves `c₁`, `c₂`.
  let σ : pushout δ' i ⟶ W := pushout.desc i δ h_comm
  let ι : Abelian.coimage σ ⟶ W := Abelian.factorThruCoimage σ
  have c₁ : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
    ShortExact.mk (exact_cokernel ι)
  have c₂ : (ShortComplex.mk (kernel.ι σ) (cokernel.π (kernel.ι σ))
      (cokernel.condition (kernel.ι σ))).ShortExact :=
    ShortExact.mk (exact_cokernel (kernel.ι σ))
  let ω : TotalH (cokernel ι) (kernel σ) := comp c₁.extClass.toTotalH c₂.extClass.toTotalH
  have := hS.mono_f
  have := hT.mono_f
  -- `f` maps `c₁` to `S`: it restricts to `β` on the coimage of `σ` and induces `j` on the
  -- cokernel.
  have hδα₁ : δ' ≫ α₁ = i ≫ 0 := by simp [← cancel_mono S.f, reassoc_of% h_comm, hα₁, hδf]
  have h_square :
      CommSq (pushout.desc α₁ 0 hδα₁) (cokernel.π (kernel.ι σ)) S.f (ι ≫ f) :=
    ⟨by ext1 <;> simp [ι, σ, hα₁, hδf]⟩
  let β : Abelian.coimage σ ⟶ S.X₁ := h_square.lift
  have hβ : cokernel.π (kernel.ι σ) ≫ β = pushout.desc α₁ 0 hδα₁ := h_square.fac_left
  have hβf : β ≫ S.f = ι ≫ f := h_square.fac_right
  let j : cokernel ι ⟶ S.X₃ := cokernel.desc ι (f ≫ S.g) (by simp [← reassoc_of% hβf])
  -- `τ = (α, κ ≫ T.f)` maps `c₂` to `T`: it lies over `β ≫ n` and restricts to `u` on the kernel.
  let τ : pushout δ' i ⟶ T.X₂ := pushout.desc α (κ ≫ T.f) hα
  have hτ : τ ≫ T.g = cokernel.π (kernel.ι σ) ≫ β ≫ n := by
    ext1 <;> simp [τ, hn, reassoc_of% hβ]
  obtain ⟨u, hu⟩ : ∃ u : kernel σ ⟶ T.X₁, u ≫ T.f = kernel.ι σ ≫ τ :=
    hT.exact.lift' (kernel.ι σ ≫ τ) (by simp [hτ])
  let y : Z₀ ⟶ kernel σ := kernel.lift σ (z ≫ pushout.inr δ' i) (by simp [σ, hz])
  have hyu : y ≫ u = z ≫ κ := by simp [← cancel_mono T.f, y, τ, hu]
  -- Naturality of the classes of `c₁` and `c₂` gives `j^* η = ω u`.
  have h_nat₁ : c₁.extClass.comp (Ext.mk₀ β) (add_zero 1) =
      (Ext.mk₀ j).comp hS.extClass (zero_add 1) :=
    c₁.extClass_naturality hS ⟨β, f, j, hβf, (cokernel.π_desc ..).symm⟩
  have h_nat₂ : c₂.extClass.comp (Ext.mk₀ u) (add_zero 1) =
      (Ext.mk₀ (β ≫ n)).comp hT.extClass (zero_add 1) :=
    c₂.extClass_naturality hT ⟨u, τ, β ≫ n, hu, hτ⟩
  -- The product with `ω` is bijective because `σ` is an equivalence for `F`.
  have h_bij {E : Type 1} [Category.{0} E] (Φ : AbFunctor C ⥤ AbFunctor E) [IsExactFunctor Φ]
      {F : AbFunctor E} (h_acyclic : ∀ k : ℕ, Subsingleton (H (Φ (cokernel i)) F k)) :
      Bijective (comp (F := F) (TotalH.map Φ ω)) := by
    have hσ : Bijective (pullbackAlong (G := F) (Φ.map (cokernel.π (kernel.ι σ)) ≫ Φ.map ι)) := by
      rw [← Φ.map_comp, Abelian.coimage.fac]
      exact (isCohomEquiv_pushout_desc h_comm Φ h_acyclic).bijective_pullbackAlong
    have hσ_comp : Bijective ((pullbackAlong (G := F) (Φ.map (cokernel.π (kernel.ι σ)))).comp
        (pullbackAlong (Φ.map ι))) := by
      simpa only [AddMonoidHom.coe_comp, Function.comp_def, pullbackAlong_pullbackAlong] using hσ
    -- The connecting maps of the two image sequences compose to a bijection.
    have h_tri := bijective_of_two_triangles (exact_triangle (c₁.map_of_exact Φ) F)
      (exact_triangle (c₂.map_of_exact Φ) F) hσ_comp
    -- `using!`: the image of an extension class under `Φ` is the class of the image sequence only
    -- up to unfolding `ShortComplex.map` (`Ext.mapExactFunctor_extClass`).
    simpa [ω, funext (map_comp_assoc _), Ext.mapExactFunctor_extClass] using! h_tri
  have h_class : comp ω (homClass u) =
      comp (homClass j) (hS.extClass.comp (H.map T.X₁ n 1 hT.extClass) rfl).toTotalH := by
    simp [ω, j, H.map, h_nat₂, ← Ext.comp_assoc (h₁₂ := zero_add 1), comp_of, ← h_nat₁]
  refine ⟨_, _, j, y, ω, ⟨?_, ?_, ?_⟩⟩
  · -- `e` kills the image of `σ`, so it factors through the cokernel.
    intro Q R e r s hi hδ hr
    have h_ι_e : ι ≫ e = 0 := by
      refine coequalizer.hom_ext ?_
      ext1 <;> simp [ι, σ, hi, hδ]
    exact ⟨cokernel.desc ι e h_ι_e, coequalizer.hom_ext (by simp [j, hr])⟩
  · -- Cancel `ω` in `j^* (η m) = ω s` to get `s = u^* m`, then `ε = y ≫ u`.
    intro E _ Φ _ F h_acyclic m s hs
    have h_nat : comp (TotalH.map Φ ω) (homClass (Φ.map u)) = pullbackAlong (Φ.map j)
        (TotalH.map Φ (hS.extClass.comp (H.map T.X₁ n 1 hT.extClass) rfl).toTotalH) := by
      simpa only [TotalH.map_comp, map_homClass] using congr(TotalH.map Φ $h_class)
    have hs_eq : pullbackAlong (Φ.map u) m = s :=
      (h_bij Φ h_acyclic).1 ((comp_assoc_of_sq h_nat m).trans hs)
    rw [← hs_eq, pullbackAlong_pullbackAlong, ← Φ.map_comp, hyu]
  · exact fun Φ _ _ h_acyclic ↦ (h_bij Φ h_acyclic).2

section

variable {p : ℕ} [ThePrime p]

open Period in
lemma gluing_apply_point (c : PadicTest)
    (t : (PadicTest.tilt ⋙ reprBy (CommAlgCat.of OFlat OFlat)).obj c) :
    (gluing.app c).hom (.of (⟨⟨false⟩, t⟩ : (tiltPointsSum pointOrTorus).obj c)) =
      .of (⟨⟨false⟩, ⟨evalZero _ ≫ t.down⟩⟩ : twoDiscs.obj c) := freeAb.desc_of ..

open Period in
lemma gluing_apply_torus (c : PadicTest) (t : (PadicTest.tilt ⋙ reprBy (monoidAlg ℚ)).obj c) :
    (gluing.app c).hom (.of (⟨⟨true⟩, t⟩ : (tiltPointsSum pointOrTorus).obj c)) =
      .of (⟨⟨false⟩, ⟨discToTorus (-NNRat.coeHom) ≫ t.down⟩⟩ : twoDiscs.obj c) -
        .of (⟨⟨true⟩, ⟨discToTorus NNRat.coeHom ≫ t.down⟩⟩ : twoDiscs.obj c) := freeAb.desc_of ..

end

variable {ℓ : ℕ}
  {A : Type} [CommRing A] [InvertsPrime A ℓ]
  {g : C ⥤ TestOver A} (M : TorsionCoeff g) (Θ : Theory g)
  {S : AbFunctor C} [HasFlatValues S]

-- Keeps definitional checks from unfolding the Ext groups and their group structure.
seal CategoryTheory.Abelian.Ext addCommGroupH in
/-- Let `S` have flat values, let `M` be a torsion coefficient and let `v` lie in total Ext(S, M).
Take the product `v η` in total Ext(S ⊗ ℤ[ℙ¹], M), with η = `etaClass g`, and move it by
`sliceEquiv` to the category of points (c, x) of ℙ¹. The result is the restriction of `v` there
composed with `cupClass`, the product with η at the tautological point x. -/
lemma TorsionCoeff.sliceEquiv_mulClass (v : TotalH S M.functor) :
    sliceEquiv (M.mulClass (etaClass g).toTotalH v) =
      comp (TotalH.map (restrictAlong (elementsProj (projLineAlong g))) v) M.cupClass.toTotalH := by
  let π : (projLineAlong g).Elements ⥤ C := elementsProj (projLineAlong g)
  let η : TotalH (freeAb (projLineAlong (π ⋙ g))) (tateModule (π ⋙ g)) :=
    (etaClass (π ⋙ g)).toTotalH
  -- Restricting along `π` and composing with the identity class is restricting along `π`.
  have h_id {N : AbFunctor C} (x : TotalH N M.functor) :
      mapThenComp (restrictAlong π) (homClass (𝟙 (π ⋙ M.functor))) x = TotalH.map (restrictAlong π)
        x :=
    comp_id
  -- Restriction to the points of the line commutes with the product by η, and η restricts to η.
  have h_res : TotalH.map (restrictAlong π) (M.mulClass (etaClass g).toTotalH v) =
      M.onElements.mulClass (S := π ⋙ S) η (TotalH.map (restrictAlong π) v) := by
    have h_natural := M.mulClass_naturality π M.onElements (homClass (𝟙 (π ⋙ M.functor)))
      (etaClass g).toTotalH v
    refine (h_id _).symm.trans (.trans ?_
      (congrArg (M.onElements.mulClass (S := π ⋙ S) η) (h_id v)))
    simp only [map_restrictAlong_etaClass] at h_natural
    exact h_natural
  -- Restricting and then evaluating at the tautological point is the definition of `sliceEquiv`.
  change pullbackAlong (tensorPoint (freeAb.map tautologicalSection) (π ⋙ S))
    (TotalH.map (restrictAlong π) (M.mulClass (etaClass g).toTotalH v)) = _
  refine (congrArg (pullbackAlong (tensorPoint (freeAb.map tautologicalSection) (π ⋙ S)))
      h_res).trans ?_
  exact M.onElements.mulClass_eq_comp_etaAt (S := π ⋙ S) η _ rfl _

/-- Let `Θ` be a theory along `g` with coefficient `F` (an `ℓ`-torsion coefficient with Zariski
descent that behaves well on closed loci), `S` a functor with flat ℤ-module values, and `x` a class
in total `Ext(S ⊗ ℤ[ℙ¹], F)` whose pull-back along `s ↦ s ⊗ [(1 : 1)]` is zero. Then
`x(q) η(r) = x(r) η(q)` (Yoneda composites) for all sections `q`, `r` of the line. Here `x(q)` is
the pull-back of `x` along `s ↦ s ⊗ [q]`, and `η(r) = Θ.etaAt r ∈ Ext²(F, F)` is the composite
`F → F ⊗ ℤ[ℙ¹] → (F ⊗ T)[2] → F[2]` of `y ↦ y ⊗ [r]`, of `F ⊗ η` and of the action of the Tate
module `T`. -/
lemma etaAt_swap (x : TotalH (abTensor S (freeAb (projLineAlong g))) Θ.functor)
    (h_inf : pullbackAlong (tensorPoint (freeAbSectionMap (basePt g)) S) x = 0)
    (q r : (projLineAlong g).sections) :
    comp (pullbackAlong (tensorPoint (freeAbSectionMap q) S) x)
        (Θ.etaAt (freeAbSectionMap r)).toTotalH =
      comp (pullbackAlong (tensorPoint (freeAbSectionMap r) S) x)
        (Θ.etaAt (freeAbSectionMap q)).toTotalH := by
  -- `t q` is evaluation at `q`, and `o q r` is the product `x(q) η(r)`.
  let t (q : (projLineAlong g).sections) : S ⟶ abTensor S (freeAb (projLineAlong g)) :=
    tensorPoint (freeAbSectionMap q) S
  let o (q r : (projLineAlong g).sections) : TotalH S Θ.functor :=
    comp (pullbackAlong (t q) x) (Θ.etaAt (freeAbSectionMap r)).toTotalH
  -- `η_q + η_r` comes from a class `ξ` relative to the locus where `J` is the unit ideal, and
  -- `q = r` where `J = 0`: the product with it does not see the difference of `t q` and `t r`.
  have h_sum (q r : (projLineAlong g).sections) : o q q + o q r = o r q + o r r := by
    obtain ⟨J, hJ, ξ, hξ⟩ := exists_etaClass_supported_diagonal q r
    have h_cut (a : (projLineAlong g).sections) (ha : ∀ c : C, J.ideal c = ⊥ → t a c = t r c) :
        o a q + o a r = pullbackAlong (tensorPoint (relFreeAb.π J.topLocus) S)
          (pullbackAlong ((abTensor.map (t r)).app _) (Θ.mulClass (.of _ 2 ξ) x)) := by
      rw [← Θ.mulClass_congr_of_eq_on_zeros J ξ ha x, Θ.mulClass_eq_comp_etaAt _ _ hξ]
      simp [o]
    rw [h_cut r fun _ _ ↦ rfl]
    refine h_cut q fun c hc ↦ ?_
    ext s
    change _ ⊗ₜ FreeAddCommGroup.of (q.val c) = _ ⊗ₜ FreeAddCommGroup.of (r.val c)
    rw [hJ c hc]
  -- Taking `r` to be the base point, where both `x` and `η` vanish, kills the diagonal terms.
  have h_diag (q : (projLineAlong g).sections) : o q q = 0 := by
    have h_eta_base : o q (basePt g) = 0 := Θ.comp_etaAt_basePt _
    have h_x_base (r : (projLineAlong g).sections) : o (basePt g) r = 0 := by
      simp [o, show pullbackAlong (t (basePt g)) x = 0 from h_inf]
    simpa [h_eta_base, h_x_base] using h_sum q (basePt g)
  simpa [h_diag] using h_sum q r

-- Keeps definitional checks from unfolding the group structure of the Ext groups.
seal addCommGroupH in
/-- For a theory `Θ` along `g` and `S` with flat values, the projective line formula
(`New.Variety.IsLerayHirschBasis` of `Θ.lineBasis`, the two classes η and 1 indexed by `Bool`) holds
at `S` under two conditions. First, `h_inj`: the product y ↦ y · η is injective, where `η`
(`etaClass g`) is the class in Ext²(ℤ[ℙ¹], 𝕋) with 𝕋 the Tate module, and the map goes from total
Ext(S, F) to total Ext(S ⊗ ℤ[ℙ¹], F). Second, `h_image`: its image contains every `x` on
`S ⊗ ℤ[ℙ¹]` whose slice `sliceEquiv x` times `η`, on the category of points of the line, equals the
restriction of `x` composed with `η` at the tautological point (`Θ.cupClass`). -/
lemma isLerayHirschBasis_lineBasis_of_injective
    (h_inj : Injective (Θ.mulClass (S := S) (etaClass g).toTotalH))
    (h_image : ∀ x : TotalH (abTensor S (freeAb (projLineAlong g))) Θ.functor,
      Θ.onElements.mulClass (S := elementsProj (projLineAlong g) ⋙ S)
          (etaClass (elementsProj (projLineAlong g) ⋙ g)).toTotalH (sliceEquiv x) =
        comp (TotalH.map (restrictAlong (elementsProj (projLineAlong g))) x) Θ.cupClass.toTotalH →
      x ∈ (Θ.mulClass (etaClass g).toTotalH).range) :
    IsLerayHirschBasis Θ.lineBasis S := by
  -- The product with `η` and evaluation `at_inf` at the base point form a short exact sequence.
  -- It is split by `pull`, the pull-back to the points of the line read through `sliceEquiv`,
  -- and its splitting is the Leray–Hirsch map.
  let at_inf : TotalH (abTensor S (freeAb (projLineAlong g))) Θ.functor →+ TotalH S Θ.functor :=
    pullbackAlong (tensorPoint (freeAbSectionMap (basePt g)) S)
  let pull : TotalH S Θ.functor →+ TotalH (abTensor S (freeAb (projLineAlong g))) Θ.functor :=
    sliceEquiv.symm.toAddMonoidHom.comp
      (TotalH.map (restrictAlong (elementsProj (projLineAlong g))))
  have h_exact : Exact (Θ.mulClass (S := S) (etaClass g).toTotalH).toIntLinearMap
      at_inf.toIntLinearMap := by
    -- One inclusion holds as `η` vanishes at the base point.
    have h_comp (v : TotalH S Θ.functor) : at_inf (Θ.mulClass (etaClass g).toTotalH v) = 0 :=
      (Θ.mulClass_eq_comp_etaAt _ _ rfl v).trans (Θ.comp_etaAt_basePt v)
    refine .of_comp_of_mem_range (funext h_comp) fun x h_inf ↦ h_image x (sliceEquiv.injective ?_)
    -- If `x` vanishes at the base point, `etaAt_swap` over pairs of points of the line exchanges
    -- the two tautological points `a`, `b`; this is the criterion `h_image`.
    let π₁ : (projLineAlong g).Elements ⥤ C := elementsProj (projLineAlong g)
    let π₂ : (projLineAlong (π₁ ⋙ g)).Elements ⥤ (projLineAlong g).Elements :=
      elementsProj (projLineAlong (π₁ ⋙ g))
    let a : (projLineAlong (π₂ ⋙ π₁ ⋙ g)).sections :=
      ⟨fun X ↦ (π₂.obj X).val, fun f ↦ (π₂.map f).map_val⟩
    let b : (projLineAlong (π₂ ⋙ π₁ ⋙ g)).sections := ⟨fun X ↦ X.val, fun f ↦ f.map_val⟩
    let x' : TotalH (abTensor (π₂ ⋙ π₁ ⋙ S) (freeAb (projLineAlong (π₂ ⋙ π₁ ⋙ g))))
        Θ.onElements.onElements.functor :=
      TotalH.map (restrictAlong π₂) (TotalH.map (restrictAlong π₁) x)
    -- Evaluation at the base point commutes with the two restrictions, and it kills `x`.
    have h_inf' : pullbackAlong
        (tensorPoint (freeAbSectionMap (basePt (π₂ ⋙ π₁ ⋙ g))) (π₂ ⋙ π₁ ⋙ S)) x' = 0 := by
      have h_restrict :
          TotalH.map (restrictAlong π₂) (TotalH.map (restrictAlong π₁) (at_inf x)) = 0 := by
        rw [show at_inf x = 0 from h_inf, map_zero, map_zero]
      -- `using!`: the restricted base point and evaluation there agree with those of the
      -- restricted line only up to unfolding definitions.
      simpa -dsimp [at_inf, map_pullbackAlong] using! h_restrict
    -- Restriction respects products, and it takes `η` at a point to `η` at that point.
    have h_cup : TotalH.map (restrictAlong π₂)
          (comp (TotalH.map (restrictAlong π₁) x) Θ.cupClass.toTotalH) =
        comp x' (Θ.onElements.onElements.etaAt (freeAbSectionMap a)).toTotalH :=
      (map_comp _).trans (congrArg (comp x') (Θ.onElements.map_etaAt_onElements _ _))
    refine (Θ.onElements.sliceEquiv_mulClass (S := π₁ ⋙ S) (sliceEquiv x)).trans ?_
    have h_first :
        comp (TotalH.map (restrictAlong π₂) (sliceEquiv x)) Θ.onElements.cupClass.toTotalH =
          comp (pullbackAlong (tensorPoint (freeAbSectionMap a) (π₂ ⋙ π₁ ⋙ S)) x')
            (Θ.onElements.onElements.etaAt (freeAbSectionMap b)).toTotalH :=
      congrArg (fun ξ ↦ comp ξ Θ.onElements.cupClass.toTotalH) map_pullbackAlong
    exact h_first.trans ((etaAt_swap Θ.onElements.onElements x' h_inf' a b).trans
      ((comp_assoc ..).trans (congrArg (pullbackAlong _) h_cup.symm)))
  -- Restriction `r` from the points of the line to the base point undoes the pull-back, and it
  -- corresponds to `at_inf` under `sliceEquiv`.
  let r {N : AbFunctor C} : TotalH (elementsProj (projLineAlong g) ⋙ N)
      (elementsProj (projLineAlong g) ⋙ Θ.functor) →+ TotalH N Θ.functor :=
    TotalH.map (restrictAlong (sectionLift (𝟭 C) (basePt g)))
  have h_res {N : AbFunctor C} (x : TotalH N Θ.functor) :
      r (TotalH.map (restrictAlong (elementsProj (projLineAlong g))) x) = x :=
    (x.map_map (restrictAlong (elementsProj (projLineAlong g)))
      (restrictAlong (sectionLift (𝟭 C) (basePt g)))).trans x.map_id
  have h_base (x : TotalH (abTensor S (freeAb (projLineAlong g))) Θ.functor) :
      r (sliceEquiv x) = at_inf x := map_pullbackAlong.trans (congrArg _ (h_res x))
  have h_section (x : TotalH S Θ.functor) : at_inf (pull x) = x := by
    rw [← h_base]
    exact (congrArg r (sliceEquiv.apply_symm_apply _)).trans (h_res x)
  let split : (TotalH S Θ.functor × TotalH S Θ.functor) ≃ₗ[ℤ]
      TotalH (abTensor S (freeAb (projLineAlong g))) Θ.functor :=
    (Exact.splitSurjectiveEquiv h_exact h_inj
      ⟨pull.toIntLinearMap, LinearMap.ext h_section⟩).val.symm
  -- A family indexed by `Bool` is a pair: first the coefficient of `η`, then that of `1`.
  let pair : (Bool →₀ TotalH S Θ.functor) ≃ TotalH S Θ.functor × TotalH S Θ.functor :=
    equivFunOnFinite.trans (.boolArrowEquivProd _)
  refine (Comparison.bijective_iff_of_comm_sq (fun p ↦ ?_) pair.symm.bijective
    sliceEquiv.bijective).1 split.bijective
  -- Both sides are the sum of `π^* p.2` and `π^* p.1 · η`, with `π^*` the restriction to the points
  -- of the line, in opposite orders.
  simp [split, pair, pull, lerayHirsch, sum_fintype, mapThenComp, TorsionCoeff.lineBasis,
    Exact.splitSurjectiveEquiv]
  let π := elementsProj (projLineAlong g)
  change _ = sliceEquiv
    (Θ.mulClass (etaClass g).toTotalH p.1 + sliceEquiv.symm (TotalH.map (restrictAlong π) p.2))
  refine (add_comm _ _).trans ?_
  exact ((map_add sliceEquiv _ _).trans
    (congrArg₂ (· + ·) (Θ.sliceEquiv_mulClass ..) (sliceEquiv.apply_symm_apply _))).symm

-- Keeps definitional checks from unfolding the group structure of the Ext groups.
seal addCommGroupH in
open TensorProduct in
/-- The projective line formula holds for a theory `Θ` along `g` if the class `η` is cancelled
(`New.Variety.IsTodaCancellation`) along a map `i`, with `ε` the generator `tateGen` of the Tate
module, and `S ⊗ coker i` is acyclic for the coefficient of `Θ` whenever `S` has flat values. -/
lemma hasLineFormula_of_isTodaCancellation {B K : AbFunctor C} {i : W' ⟶ W} {δ : W ⟶ W}
    {q : W ⟶ freeAb (projLineAlong g)} {j : B ⟶ freeAb (projLineAlong g)}
    {y : freeAb (onePointFunctor C) ⟶ K} {ω : TotalH B K}
    (h_toda : IsTodaCancellation i δ q (etaClass g) (tateGen g) j y ω)
    (h_acyclic : ∀ (S : AbFunctor C) [HasFlatValues S] (n : ℕ),
      Subsingleton (H (abTensor S (cokernel i)) Θ.functor n)) :
    Θ.HasLineFormula := by
  -- Check the two conditions of `isLerayHirschBasis_lineBasis_of_injective`.
  -- It suffices to treat representable `S = ℤ[h_c]`.
  refine isLerayHirschBasis_of_reprBy fun c ↦
    isLerayHirschBasis_lineBasis_of_injective Θ ((injective_iff_map_eq_zero _).2 fun v hv ↦ ?_)
      fun x hx ↦ ?_
  · -- If `η v = 0`, take `s = 0` in `h_toda`: the action `m` of the Tate module on `v` pulls
    -- back to `0` along the generator `tateGen`, and that pull-back is `v`.
    let Φ : AbFunctor C ⥤ AbFunctor C := abTensor (freeAb (reprBy c))
    let m : TotalH (Φ (tateModule g)) Θ.functor :=
      comp (TotalH.map (abTensor.flip _) v) Θ.tateAction.toTotalH
    have h_eq : pullbackAlong (Φ.map j) (comp (TotalH.map Φ (etaClass g).toTotalH) m) =
        comp (TotalH.map Φ ω) 0 := by
      rw [show comp (TotalH.map Φ (etaClass _).toTotalH) m = 0 from hv, map_zero, map_zero]
    have h_pull : pullbackAlong (tensorPoint (tateGen _) _) m = 0 :=
      (h_toda.pullbackAlong_comp_map_eq Φ (h_acyclic _) (tensorPoint (𝟙 _) _) m 0 h_eq).trans
        (map_zero _)
    exact (Θ.pullbackAlong_tensorPoint_comp_tateAction v).symm.trans h_pull
  -- Write `j^* x = ω w`; the preimage of `x` is `y^* w`. Check this over the points of `ℙ¹`.
  let S : AbFunctor C := freeAb (reprBy c)
  let L : AbFunctor C := freeAb (projLineAlong g)
  obtain ⟨w, hw⟩ : ∃ w : TotalH (abTensor S K) Θ.functor,
      comp (TotalH.map (abTensor S) ω) w = pullbackAlong ((abTensor S).map j) x :=
    h_toda.surjective (abTensor S) (h_acyclic S) _
  refine ⟨pullbackAlong (tensorPoint y _) w, sliceEquiv.injective ?_⟩
  -- Over the points of `ℙ¹`, apply `h_toda` to the functor `Φ`, with `m` the action of the Tate
  -- module on `x` and `s = w η`.
  let π : (projLineAlong g).Elements ⥤ C := elementsProj (projLineAlong g)
  let Φ : AbFunctor C ⥤ AbFunctor (projLineAlong g).Elements := restrictAlong π ⋙ abTensor (π ⋙ S)
  let m : TotalH (Φ (tateModule g)) Θ.onElements.functor :=
    comp (TotalH.map (abTensor.flip (tateModule (π ⋙ g))) (sliceEquiv x))
      Θ.onElements.tateAction.toTotalH
  let s : TotalH (Φ K) Θ.onElements.functor :=
    comp (TotalH.map (restrictAlong π) w) Θ.cupClass.toTotalH
  -- The hypothesis `j^* (η m) = ω s` of `h_toda` follows from `hx` and `hw`.
  have h_eq : pullbackAlong (Φ.map j) (comp (TotalH.map Φ (etaClass g).toTotalH) m) =
      comp (TotalH.map Φ ω) s := by
    have h_eta : comp (TotalH.map Φ (etaClass g).toTotalH) m =
        comp (TotalH.map (restrictAlong π) x) Θ.cupClass.toTotalH := by
      change comp
        (TotalH.map (restrictAlong π ⋙ abTensor (π ⋙ S)) (etaClass g).toTotalH) m = _
      rw [← TotalH.map_map, map_restrictAlong_etaClass]
      exact hx
    have h_lhs :
        pullbackAlong (Φ.map j) (comp (TotalH.map (restrictAlong π) x) Θ.cupClass.toTotalH) =
          comp (TotalH.map (restrictAlong π) (pullbackAlong ((abTensor S).map j) x))
            Θ.cupClass.toTotalH :=
      (comp_assoc ..).symm.trans (congrArg (comp · Θ.cupClass.toTotalH)
        (map_pullbackAlong (Φ := restrictAlong π) (f := (abTensor S).map j) (x := x)).symm)
    have h_rhs :
        comp (TotalH.map (restrictAlong π) (comp (TotalH.map (abTensor S) ω) w))
          Θ.cupClass.toTotalH = comp (TotalH.map Φ ω) s :=
      (map_comp_assoc ..).trans (congrArg (comp · s) (TotalH.map_map ..))
    have h_mid :=
      congrArg (fun z ↦ comp (TotalH.map (restrictAlong π) z) Θ.cupClass.toTotalH) hw.symm
    exact (congrArg (pullbackAlong (Φ.map j)) h_eta).trans <|
      h_lhs.trans (h_mid.trans h_rhs)
  -- Acyclicity over the points of `ℙ¹` is that of `h_c × ℙ¹`, after swapping two tensor factors.
  have h_acyclic_Φ (n : ℕ) : Subsingleton (H (Φ (cokernel i)) Θ.onElements.functor n) := by
    let swap : abTensor (abTensor S L) (cokernel i) ≅
        abTensor (abTensor S (cokernel i)) L :=
      NatIso.ofComponents (fun _ ↦ (rightComm ℤ _ _ _).toAddCommGrpIso) fun _ ↦
        AddCommGrpCat.hom_ext <| AddMonoidHom.toIntLinearMap_injective <|
          TensorProduct.ext_threefold fun _ _ _ ↦ rfl
    have h_line (k : ℕ) : Subsingleton (H (abTensor (abTensor S L) (cokernel i)) Θ.functor k) :=
      h_acyclic (abTensor S L) k
    have h_swapped : Subsingleton (TotalH (abTensor (abTensor S (cokernel i)) L) Θ.functor) :=
      (IsCohomEquiv.of_isIso swap.hom).bijective_pullbackAlong.injective.subsingleton
    have h_total : Subsingleton (TotalH (Φ (cokernel i)) Θ.onElements.functor) :=
      (sliceEquiv (N := abTensor S (cokernel i))).symm.injective.subsingleton
    exact (DirectSum.of_injective (β := H (Φ (cokernel i)) Θ.onElements.functor) n).subsingleton
  have h_first :
      sliceEquiv (Θ.mulClass (S := S) (etaClass g).toTotalH (pullbackAlong (tensorPoint y S) w)) =
        pullbackAlong (tensorPoint (𝟙 _) (π ⋙ S) ≫ Φ.map y) s :=
    (Θ.sliceEquiv_mulClass _).trans <|
      (congrArg (comp · Θ.cupClass.toTotalH) map_pullbackAlong).trans (comp_assoc ..)
  exact h_first.trans ((h_toda.pullbackAlong_comp_map_eq Φ h_acyclic_Φ _ m s h_eq).symm.trans
    (Θ.onElements.pullbackAlong_tensorPoint_comp_tateAction (S := π ⋙ S) _))

open Period in
/-- The roots of unity `compatibleRootsOfUnity` of `A`, mapped to `ℂ_ℓ`, lift to a character `χ` of
`ℚ` with values in `O^♭`: the untilt of `χ s` is the image of the root of unity at `s`. -/
private lemma exists_tilt_lift_compatibleRootsOfUnity [Algebra A ℂ_[ℓ]] :
    ∃ χ : Multiplicative ℚ →* OFlat, ∀ s : Multiplicative ℚ,
      ((χ s).untilt : ℂ_[ℓ]) = algebraMap A ℂ_[ℓ]
        ((compatibleRootsOfUnity (ℓ := ℓ) (A := A)).val s : A) := by
  have h_root : (compatibleRootsOfUnity (ℓ := ℓ) (A := A)).val (.ofAdd 1) = 1 :=
    (compatibleRootsOfUnity (ℓ := ℓ) (A := A)).property.left
  let a : Multiplicative ℚ →* ℂ_[ℓ] :=
    (algebraMap A ℂ_[ℓ]).toMonoidHom.comp
      ((Units.coeHom A).comp (compatibleRootsOfUnity (ℓ := ℓ)).val)
  exact exists_tilt_lift_of_character a (by simp [a, h_root])

open AddMonoidAlgebra Period freeAb in
/-- On the cover of the perfect projective line by two discs glued along the torus, let `χ` be a
character of `ℚ` with values in `O^♭`, whose operators `1 - Δ` (`oneSub`, with Δ the twist
`charTwist χ`: `discTwist χ` on the discs, `pointOrTorusTwist χ` on the source of the gluing)
commute with the gluing map (`oneSub_comp_gluing`). Let `f`, `α`, `κ` satisfy the three conditions
of `exists_isTodaCancellation` for this square (`h_torus`, `h_disc`, `h_kummer`), with `κ` at the
origin equal to `tateGen`. Then the class `η` is cancelled, with `ε` the generator `tateGen`. -/
private lemma exists_isTodaCancellation_etaClass_of_squares [Algebra A ℂ_[ℓ]]
    (χ : Multiplicative ℚ →* OFlat)
    (f : freeAb twoDiscs ⟶ (cocycle (genericTestOver A)).extension.X₂)
    (α : freeAb (tiltPointsSum pointOrTorus) ⟶ (kummerSeq (genericTestOver A)).X₂)
    (κ : freeAb twoDiscs ⟶ (kummerSeq (genericTestOver A)).X₁)
    (h_torus : (α ≫ (kummerSeq (genericTestOver A)).g) ≫
      (cocycle (genericTestOver A)).extension.f = gluing ≫ f)
    (h_disc : oneSub (discTwist χ) ≫ f = 0)
    (h_kummer : oneSub (pointOrTorusTwist χ) ≫ α = gluing ≫ κ ≫ (kummerSeq (genericTestOver A)).f)
    (h_gen : origin ⟨true⟩ ≫ κ = tateGen (genericTestOver A)) :
    ∃ (δ : freeAb twoDiscs ⟶ freeAb twoDiscs)
      (q : freeAb twoDiscs ⟶ freeAb (projLineAlong (genericTestOver A)))
      (B K : AbFunctor PadicTest) (j : B ⟶ freeAb (projLineAlong (genericTestOver A)))
      (y : freeAb (onePointFunctor PadicTest) ⟶ K) (ω : TotalH B K),
      IsTodaCancellation gluing δ q (etaClass (genericTestOver A)) (tateGen (genericTestOver A))
        j y ω := by
  -- The twist of either disc fixes the origin.
  have h_origin : origin ⟨true⟩ ≫ oneSub (discTwist χ) = 0 := by
    refine freeAb.hom_ext fun c x ↦ ?_
    let z : twoDiscs.obj c := ⟨⟨true⟩, ⟨evalZero _⟩⟩
    have h_origin_app : (origin ⟨true⟩).app c (FreeAddCommGroup.of x) = FreeAddCommGroup.of z :=
      freeAb.desc_of ..
    let z' : twoDiscs.obj c :=
      ⟨⟨true⟩, ⟨discTwist χ ⟨true⟩ ≫ evalZero (PadicTest.tilt.obj c)⟩⟩
    have h_twist : (oneSub (discTwist χ)).app c (.of z) = .of z - .of z' :=
      freeAb.desc_of ..
    have h_fixed : z' = z :=
      congrArg (fun t ↦ (⟨⟨true⟩, ⟨t⟩⟩ : twoDiscs.obj c)) (discTwist_comp_evalZero ..)
    exact (congrArg ((oneSub (discTwist χ)).app c) h_origin_app).trans
      (h_twist.trans (sub_eq_zero.mpr (congrArg FreeAddCommGroup.of h_fixed.symm)))
  obtain ⟨B, K, j, y, ω, h_toda⟩ := exists_isTodaCancellation (oneSub_comp_gluing χ) (origin ⟨true⟩)
    h_origin
    (cocycle _).shortExact_extension (shortExact_kummerSeq (genericTestOver A)) f α κ (𝟙 _) _
    h_torus h_disc h_kummer (Category.comp_id _)
  -- The 2-extension along the identity is `η`.
  have h_eta : (cocycle (genericTestOver A)).shortExact_extension.extClass.comp
      (H.map _ (𝟙 _) 1 (shortExact_kummerSeq (genericTestOver A)).extClass) rfl =
      etaClass (genericTestOver A) := by
    unfold etaClass
    exact congrArg (fun x ↦ (cocycle (genericTestOver A)).shortExact_extension.extClass.comp x rfl)
      (H.map_id (x := (shortExact_kummerSeq (genericTestOver A)).extClass))
  refine ⟨oneSub (discTwist χ), f ≫ (cocycle (genericTestOver A)).extension.g, B, K, j, y, ω, ?_⟩
  rw [← h_eta, ← h_gen]
  exact h_toda

open AddMonoidAlgebra Period freeAb in
/-- On the cover of the perfect projective line by two discs glued along the torus (`gluing`), the
class `η` is cancelled, with `ε` the generator `tateGen` of the Tate module. That is, some `δ`, `q`,
`j`, `y`, `ω` satisfy `IsTodaCancellation`. So after any exact functor making `coker gluing`
acyclic, product with `ω` is onto and `j^*(η m)` determines `ε^* m`. -/
lemma exists_isTodaCancellation_etaClass [Algebra A ℂ_[ℓ]] :
    ∃ (δ : freeAb twoDiscs ⟶ freeAb twoDiscs)
      (q : freeAb twoDiscs ⟶ freeAb (projLineAlong (genericTestOver A)))
      (B K : AbFunctor PadicTest) (j : B ⟶ freeAb (projLineAlong (genericTestOver A)))
      (y : freeAb (onePointFunctor PadicTest) ⟶ K) (ω : TotalH B K),
      IsTodaCancellation gluing δ q (etaClass (genericTestOver A)) (tateGen (genericTestOver A))
        j y ω := by
  -- The gluing map commutes with the operators `1 - charTwist χ _` (`oneSub_comp_gluing`); read `η`
  -- on this square by `exists_isTodaCancellation_etaClass_of_squares`. First, the character `χ` of
  -- `ℚ` with values in the tilt that lifts the roots of unity `compatibleRootsOfUnity`, which are
  -- `1` at `1`.
  have h_root : (compatibleRootsOfUnity (ℓ := ℓ) (A := A)).val (.ofAdd 1) = 1 :=
    (compatibleRootsOfUnity (ℓ := ℓ) (A := A)).property.left
  obtain ⟨χ, hχ⟩ := exists_tilt_lift_compatibleRootsOfUnity (A := A)
  -- The row `(1 + x.1 * x.2, x.2)` is the unit `ε x` times the chosen row of its class. `F c x` is
  -- this frame, a unit and a point of `ℙ¹`; it is natural in `c`.
  let R : PadicTest ⥤ CommRingCat := ringOf (genericTestOver A)
  have h_row : ∀ (B : CommRingCat) (x : B × B),
      ∃ ε : Bˣ, (1 + x.1 * x.2, x.2) = ε.val • unimodularRow ⟨⟦x⟧⟩ :=
    fun _ x ↦ exists_unit_smul_unimodularRow x
  choose ε hε using h_row
  let F (c : PadicTest) (x : R c × R c) : (cocycle (genericTestOver A)).extension.X₂ c :=
    (⟨ε (R.obj c) x⟩, .of ⟨⟦x⟧⟩)
  have F_nat (c d : PadicTest) (f : c ⟶ d) (x : R c × R c) :
      (cocycle _).extension.X₂.map f (F c x) = F d (R.map f x.1, R.map f x.2) := by
    -- `R.map f` sends `ε x` times the row of `⟦x⟧`, that is `(1 + x.1 * x.2, x.2)`, to the row of
    -- the image pair.
    have h_image : Prod.map (R.map f) (R.map f) ((ε (R.obj c) x).val • unimodularRow ⟨⟦x⟧⟩) =
        (1 + R.map f x.1 * R.map f x.2, R.map f x.2) := by
      rw [← hε (R.obj c) x]
      simp only [Prod.map_apply, RingHom.map_add, RingHom.map_one, RingHom.map_mul]
    have h_row := hε (R.obj d) (R.map f x.1, R.map f x.2)
    exact Prod.ext (add_rowUnit_eq (R.map f) _ (h_image.trans h_row)) rfl
  -- The untilt `ρ` is natural, and it sends a constant `s` from `OFlat` to the untilt of `s`.
  let ρ (c : PadicTest) : PadicTest.tilt c →*₀ c.GenericRing :=
    .comp (.ofClass (algebraMap ..)) (Perfection.teichmuller₀ ..)
  have ρ_nat (c d : PadicTest) (f : c ⟶ d) (x : PadicTest.tilt c) :
      R.map f (ρ c x) = ρ d (tiltMap f.toRingHom x) := by
    -- These lemmas match `R.map f` and `ρ` only up to unfolding definitions.
    exact (c.mapGeneric_algebraMap _ _).trans (congrArg _ (untilt_tiltMap ..).symm)
  have ρ_const (c : PadicTest) (s : OFlat) :
      ρ c (algebraMap _ _ s) = c.genericStructureMap s.untilt := by
    -- As for `ρ_nat`, these lemmas match only up to unfolding definitions.
    exact ((c.genericStructureMap_coe _).trans (congrArg _ (untilt_tiltMap c.structureMap s).symm)).symm
  -- With `X` the untilt of the coordinate, `f` is `[(1, 0)] - [(X, 1)]` on the disc `true` and
  -- `[(1, 0)] - [(1, X)]` on the other one.
  let f : freeAb twoDiscs ⟶ (cocycle (genericTestOver A)).extension.X₂ := desc
    (fun c y ↦ F c (0, 0) -
      F c (cond y.fst.down (fun X ↦ (X - 1, 1)) (fun X ↦ (0, X))
        (ρ c (y.snd.down.hom (single 1 1)))))
    (by
      -- On each disc, `twoDiscs.map` keeps the disc and composes the point, by definition.
      rintro c d j ⟨⟨_ | _⟩, y⟩
      · let x := y.down.hom (single 1 1)
        change F d (0, 0) - F d (0, ρ d (tiltMap j.toRingHom x)) =
          ((cocycle _).extension.X₂.map j).hom (F c (0, 0) - F c (0, ρ c x))
        rw [_root_.map_sub, F_nat c d j (0, 0), F_nat c d j (0, ρ c x)]
        simp [ρ_nat]
      · let x := y.down.hom (single 1 1)
        let xc : R c := ρ c x
        let xd : R d := ρ d (tiltMap j.toRingHom x)
        change F d (0, 0) - F d (xd - 1, 1) =
          ((cocycle _).extension.X₂.map j).hom (F c (0, 0) - F c (xc - 1, 1))
        rw [_root_.map_sub, F_nat c d j (0, 0), F_nat c d j (xc - 1, 1)]
        simp [xc, xd]
        have h_coordinate :
            R.map j (xc - 1) = xd - 1 :=
          (map_sub (R.map j).hom _ _).trans
            (congrArg₂ (· - ·) (ρ_nat c d j x) (map_one (R.map j).hom))
        exact congrArg (fun a : R d ↦ F d (a, 1)) h_coordinate.symm)
  -- `α` sends a point `t` of the torus to `pow c t`, the untilts of the powers of the coordinate.
  let pow (c : PadicTest) (t : (PadicTest.tilt ⋙ reprBy (monoidAlg ℚ)).obj c) :
      (kummerSeq (genericTestOver A)).X₂ c :=
    .comp (.mk' ULift.up fun _ _ ↦ rfl)
      ((ρ c).toMonoidHom.comp
        (t.down.hom.toRingHom.toMonoidHom.comp (of OFlat ℚ))).toHomUnits.toAdditiveRight
  let α : freeAb (tiltPointsSum pointOrTorus) ⟶ (kummerSeq (genericTestOver A)).X₂ :=
    projFirst ≫ desc pow fun c d φ t ↦ AddMonoidHom.ext fun s ↦ Gm.ext.2 (ρ_nat c d φ _).symm
  let κ : freeAb twoDiscs ⟶ (kummerSeq (genericTestOver A)).X₁ :=
    projFirst ≫ freeAb.map (toUnit _) ≫ tateGen _
  -- The three squares that `exists_isTodaCancellation_etaClass_of_squares` needs, each checked on
  -- the generators of a free functor.
  have h_f_app (c : PadicTest) (y : twoDiscs.obj c) :
      (f.app c).hom (FreeAddCommGroup.of y) = F c (0, 0) -
        F c (cond y.fst.down (fun X ↦ (X - 1, 1)) (fun X ↦ (0, X))
          (ρ c (y.snd.down.hom (single 1 1)))) := freeAb.desc_of ..
  have h_alpha (c : PadicTest) (q : (PadicTest.tilt ⋙ reprBy (monoidAlg ℚ)).obj c) :
      (α.app c).hom (FreeAddCommGroup.of (⟨⟨true⟩, q⟩ : (tiltPointsSum pointOrTorus).obj c)) =
        pow c q := by
    let r : (tiltPointsSum pointOrTorus).obj c := ⟨⟨true⟩, q⟩
    change FreeAddCommGroup.lift (pow c)
      (((projFirst (B := pointOrTorus)).app c).hom (FreeAddCommGroup.of r)) = _
    exact (congrArg (FreeAddCommGroup.lift (pow c))
      (projFirst_true (B := pointOrTorus) c q)).trans (FreeAddCommGroup.lift_apply_of ..)
  have h_torus : (α ≫ (kummerSeq (genericTestOver A)).g) ≫
      (cocycle (genericTestOver A)).extension.f = gluing ≫ f := by
    -- On the torus the frames `(X, 1)` and `(1, X⁻¹)` differ by the unit `X`.
    refine hom_ext ?_
    rintro c ⟨⟨_ | _⟩, y⟩
    · let y₀ : (tiltPointsSum pointOrTorus).obj c := ⟨⟨false⟩, y⟩
      let z : twoDiscs.obj c := ⟨⟨false⟩, ⟨evalZero (PadicTest.tilt.obj c)⟩⟩
      have h_glue : (gluing.app c).hom (FreeAddCommGroup.of y₀) = FreeAddCommGroup.of z := by
        simpa only [y₀, z, evalZero_comp] using gluing_apply_point c y
      have h_a : (α.app c).hom (FreeAddCommGroup.of y₀) = 0 := by
        change FreeAddCommGroup.lift (pow c)
          (((projFirst (B := pointOrTorus)).app c).hom (FreeAddCommGroup.of y₀)) = 0
        exact (congrArg (FreeAddCommGroup.lift (pow c))
          (projFirst_false (B := pointOrTorus) c y)).trans (map_zero _)
      change ((cocycle _).extension.f.app c).hom
          (((kummerSeq (genericTestOver A)).g.app c).hom ((α.app c).hom (FreeAddCommGroup.of y₀))) =
        (f.app c).hom ((gluing.app c).hom (FreeAddCommGroup.of y₀))
      rw [h_a, h_glue, h_f_app]
      simp [z, evalZero]
      exact (map_zero ((cocycle (genericTestOver A)).extension.f.app c).hom).trans
        (sub_self _).symm
    · let X : R c := ρ c (y.down.hom (single 1 1))
      let X' : R c := ρ c (y.down.hom (single (-1) 1))
      let v : (cocycle (genericTestOver A)).extension.X₂ c :=
        ((cocycle (genericTestOver A)).extension.f.app c).hom
          (((kummerSeq (genericTestOver A)).g.app c).hom (pow c y))
      -- The first component of `v` is the unit `X`, with inverse `X'`.
      have h_rows : (v + F c (0, X')).1.down.val • unimodularRow (B := R c) ⟨⟦(0, X')⟧⟩ =
          (F c (X - 1, 1)).1.down.val • unimodularRow (B := R c) ⟨⟦(X - 1, 1)⟧⟩ := by
        -- `erw`: the rows of the two frames match `hε` only up to unfolding definitions.
        erw [mul_smul, ← hε, ← hε]
        simpa only [zero_mul, add_zero, Prod.smul_mk, smul_eq_mul, mul_one, add_sub_cancel,
          Prod.mk.injEq] using ⟨rfl, Units.mul_inv _⟩
      obtain ⟨h_unit, h_point⟩ := eq_and_eq_of_smul_unimodularRow_eq h_rows
      have h_frame : v + F c (0, X') = F c (X - 1, 1) :=
        Prod.ext (ULift.down_injective h_unit)
          ((zero_add _).trans (congrArg FreeAddCommGroup.of h_point))
      let y₁ : (tiltPointsSum pointOrTorus).obj c := ⟨⟨true⟩, y⟩
      let z₀ : twoDiscs.obj c := ⟨⟨false⟩, ⟨discToTorus (-NNRat.coeHom) ≫ y.down⟩⟩
      let z₁ : twoDiscs.obj c := ⟨⟨true⟩, ⟨discToTorus NNRat.coeHom ≫ y.down⟩⟩
      have h_glue := gluing_apply_torus c y
      change ((cocycle _).extension.f.app c).hom
          (((kummerSeq (genericTestOver A)).g.app c).hom ((α.app c).hom (FreeAddCommGroup.of y₁))) =
        (f.app c).hom ((gluing.app c).hom (FreeAddCommGroup.of y₁))
      erw [h_alpha, h_glue, _root_.map_sub, h_f_app, h_f_app]
      have h_coord (g : ℚ≥0 →+ ℚ) :
          (discToTorus g ≫ y.down).hom (single 1 1) = y.down.hom (single (g 1) 1) := by
        change y.down.hom (mapDomain g (single 1 1)) = _
        exact congrArg y.down.hom (AddMonoidAlgebra.mapDomain_single ..)
      simp only [Bool.cond_false, Bool.cond_true, h_coord]
      change v = (F c (0, 0) - F c (0, X')) - (F c (0, 0) - F c (X - 1, 1))
      simpa only [sub_sub_sub_cancel_left, eq_sub_iff_add_eq] using h_frame
  have h_disc : oneSub (discTwist χ) ≫ f = 0 := by
    -- `charTwist χ` fixes `X`, as the roots of unity are trivial at `1` and `-1`.
    refine freeAb.hom_ext fun c y ↦ ?_
    let y' : twoDiscs.obj c := ⟨y.fst, ⟨discTwist χ y.fst ≫ y.snd.down⟩⟩
    change (f.app c).hom (((oneSub (discTwist χ)).app c).hom (.of y)) = 0
    have h_sub : ((oneSub (discTwist χ)).app c).hom (.of y) = .of y - .of y' :=
      freeAb.desc_of ..
    refine (congrArg (f.app c).hom h_sub).trans ?_
    refine (_root_.map_sub (f.app c).hom _ _).trans ?_
    refine (congrArg₂ (· - ·) (h_f_app c y) (h_f_app c y')).trans ?_
    rcases y with ⟨⟨_ | _⟩, y⟩ <;>
      simp [y', discTwist, charTwist, ρ_const, hχ, h_root, -coe_algebraMap, -Functor.comp_obj]
  have h_kummer : oneSub (pointOrTorusTwist χ) ≫ α =
      gluing ≫ κ ≫ (kummerSeq (genericTestOver A)).f := by
    -- `charTwist χ` multiplies the untilted powers by the roots of unity of `tateGen`.
    refine hom_ext ?_
    rintro c ⟨⟨_ | _⟩, y⟩
    · let y₀ : (tiltPointsSum pointOrTorus).obj c := ⟨⟨false⟩, y⟩
      let z : twoDiscs.obj c := ⟨⟨false⟩, ⟨evalZero (PadicTest.tilt.obj c)⟩⟩
      have h_twist : ((oneSub (pointOrTorusTwist χ)).app c).hom
          (FreeAddCommGroup.of y₀) = 0 := by
        change FreeAddCommGroup.lift _ (FreeAddCommGroup.of y₀) = _
        rw [FreeAddCommGroup.lift_apply_of]
        change Sub.sub (FreeAddCommGroup.of y₀)
          (FreeAddCommGroup.of (⟨⟨false⟩, ⟨𝟙 _ ≫ y.down⟩⟩ : (tiltPointsSum pointOrTorus).obj c)) = 0
        rw [Category.id_comp]
        exact sub_self _
      have h_glue : (gluing.app c).hom (FreeAddCommGroup.of y₀) = FreeAddCommGroup.of z := by
        simpa only [y₀, z, evalZero_comp] using gluing_apply_point c y
      change (α.app c).hom (((oneSub (pointOrTorusTwist χ)).app c).hom (FreeAddCommGroup.of y₀)) =
        ((kummerSeq (genericTestOver A)).f.app c).hom
          ((κ.app c).hom ((gluing.app c).hom (FreeAddCommGroup.of y₀)))
      rw [h_twist, h_glue]
      change _ = ((kummerSeq (genericTestOver A)).f.app c).hom
        (((tateGen (genericTestOver A)).app c).hom ((freeAb.map (toUnit _)).app c
          (((projFirst (B := fun _ ↦ monoidAlg ℚ≥0)).app c).hom (FreeAddCommGroup.of z))))
      rw [projFirst_false (B := fun _ ↦ monoidAlg ℚ≥0) c z.snd]
      simp only [map_zero]
    · let y₁ : (tiltPointsSum pointOrTorus).obj c := ⟨⟨true⟩, y⟩
      let t : (PadicTest.tilt ⋙ reprBy (monoidAlg ℚ)).obj c :=
        ⟨charTwist χ (AddMonoidHom.id ℚ) ≫ y.down⟩
      let z₀ : twoDiscs.obj c := ⟨⟨false⟩, ⟨discToTorus (-NNRat.coeHom) ≫ y.down⟩⟩
      let z₁ : twoDiscs.obj c := ⟨⟨true⟩, ⟨discToTorus NNRat.coeHom ≫ y.down⟩⟩
      have h_glue := gluing_apply_torus c y
      let π := (freeAb.map (toUnit (PadicTest.tilt ⋙ reprBy (monoidAlg ℚ≥0)))).app c
      let τ := ((tateGen (genericTestOver A)).app c).hom
      have h_zero : (κ.app c).hom (FreeAddCommGroup.of z₀) = 0 := by
        change τ (π (((projFirst (B := fun _ ↦ monoidAlg ℚ≥0)).app c).hom
          (FreeAddCommGroup.of z₀))) = 0
        rw [projFirst_false (B := fun _ ↦ monoidAlg ℚ≥0) c z₀.snd]
        simp only [map_zero]
      have h_one : (κ.app c).hom (FreeAddCommGroup.of z₁) = τ (FreeAddCommGroup.of PUnit.unit) := by
        change τ (π (((projFirst (B := fun _ ↦ monoidAlg ℚ≥0)).app c).hom
          (FreeAddCommGroup.of z₁))) = _
        rw [projFirst_true (B := fun _ ↦ monoidAlg ℚ≥0) c z₁.snd]
        change τ ((freeAb.map (toUnit (PadicTest.tilt ⋙ reprBy (monoidAlg ℚ≥0)))).app c
          (FreeAddCommGroup.of z₁.snd)) = _
        rw [freeAb.map_of]
        rfl
      change (α.app c).hom (((oneSub (pointOrTorusTwist χ)).app c).hom (FreeAddCommGroup.of y₁)) =
        ((kummerSeq (genericTestOver A)).f.app c).hom
          ((κ.app c).hom ((gluing.app c).hom (FreeAddCommGroup.of y₁)))
      change (α.app c).hom (FreeAddCommGroup.lift _ (FreeAddCommGroup.of y₁)) = _
      rw [FreeAddCommGroup.lift_apply_of]
      let t₁ : (tiltPointsSum pointOrTorus).obj c := ⟨⟨true⟩, t⟩
      change (α.app c).hom (FreeAddCommGroup.of y₁ - FreeAddCommGroup.of t₁) = _
      erw [_root_.map_sub, h_alpha, h_alpha, h_glue, _root_.map_sub, h_zero, h_one, zero_sub, map_neg]
      apply neg_injective
      rw [neg_sub, neg_neg]
      refine sub_eq_of_eq_add (AddMonoidHom.ext fun s ↦ Gm.ext.2 ?_)
      -- The twist sends the power `X^s` to `χ s · X^s`, whose untilt is the root of unity at `s`
      -- times the untilt of `X^s`.
      have h_twist : ρ c (y.down.hom (lift OFlat OFlat[ℚ] ℚ
            (((algebraMap OFlat OFlat[ℚ] : OFlat →* OFlat[ℚ])).comp χ * of OFlat ℚ)
            (of OFlat ℚ (.ofAdd s)))) =
          c.genericStructureMap (algebraMap A ℂ_[ℓ]
              ((compatibleRootsOfUnity (ℓ := ℓ) (A := A)).val (.ofAdd s) : A)) *
            ρ c (y.down.hom (of OFlat ℚ (.ofAdd s))) := by
        erw [lift_of, MonoidHom.mul_apply, map_mul, map_mul, ← hχ, ← ρ_const]
        exact congrArg (fun z ↦ ρ c z * _) (y.down.hom.commutes _)
      refine h_twist.trans ?_
      -- `erw` and `rfl`: `tateGen` is the family of these roots of unity by definition.
      erw [desc_of]
      rfl
  have h_gen : origin ⟨true⟩ ≫ κ = tateGen (genericTestOver A) := hom_ext fun _ _ ↦ rfl
  exact exists_isTodaCancellation_etaClass_of_squares χ f α κ h_torus h_disc h_kummer h_gen

open Period in
/-- Let `O^♭` be the inverse limit of `O_C/ℓ` along `x ↦ x^ℓ`, `M` an `O^♭`-module, and `ℂ_ℓ` an
`A`-algebra. Suppose every perfect `O^♭`-algebra `b` is acyclic for `M` (`h_acyclic_perfect`): on
`ℓ`-adic tests, the functor `S ↦ Hom(b, S^♭)` with coefficients `S ↦ S^♭ ⊗_{O^♭} M` has cohomology
`b ⊗_{O^♭} M`, concentrated in degree 0. Then the tilted theory `tiltTheory` (on `ℓ`-adic tests
along `R ↦ R[1/ℓ]`, with coefficients `R ↦ R^♭ ⊗_{O^♭} M`) satisfies the projective line formula
`H(ℙ¹ × S) = H(S) ⊕ η H(S)`: the classes `1` and `η` are a basis over the cohomology of every
`S`. -/
lemma hasLineFormula_tiltTheory (M : ModuleCat OFlat) [Algebra A ℂ_[ℓ]]
    (h_acyclic_perfect : IsAcyclicOnPerfect (moduleCoeff (tensorCoeff M))) :
    (tiltTheory A M h_acyclic_perfect).HasLineFormula := by
  -- Cancel `η` on the cover of the perfect projective line by two discs.
  obtain ⟨δ, q, B, K, j, y, ω, h_toda⟩ := exists_isTodaCancellation_etaClass (A := A)
  -- Every flat `S ⊗ coker gluing` is acyclic for the coefficient, so `h_toda` applies.
  let Θ : Theory (genericTestOver A) := tiltTheory A M h_acyclic_perfect
  have h_acyclic (S : AbFunctor PadicTest) [HasFlatValues S] (n : ℕ) :
      Subsingleton (H (abTensor S (cokernel gluing)) Θ.functor n) :=
    subsingleton_H_cokernel_gluing (F := Θ.functor)
      (fun c ↦ isCohomEquiv_tensorCoeff_gluing c h_acyclic_perfect) S n
  exact hasLineFormula_of_isTodaCancellation Θ h_toda h_acyclic

end New.Variety

end TiltedLineFormula
