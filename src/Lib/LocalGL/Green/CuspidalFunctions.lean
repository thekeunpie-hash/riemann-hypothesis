module

public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Polynomial.Module.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Lib.General.Groups.BesselGroups
public import Lib.General.Groups.CharacterTheory
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Semisimple
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.RingTheory.Artinian.Instances
import Lib.General.LinearAlgebra.MatrixPolynomials
import Lib.General.NumberTheory.FrobeniusOrbits

section
/-!
# Hall algebra of class functions: induction product, Mackey formula, Frobenius reciprocity

`New.Hall k` is the space of complex-valued functions on similarity classes of square matrices of
all sizes over a field `k`. For finite `k` it is a commutative ℂ-algebra in which the constant
function `New.Hall.constOne` is invertible. From here on `k` is finite. Let δ denote the block
average `New.Hall.blockAverage` over block triangular matrices. Then δ is multiplicative (Mackey's
formula) and adjoint to the induction product. This yields the adjoint `New.Hall.skew` of
multiplication, a derivation for cuspidal functions, and Frobenius reciprocity along parabolic
subgroups.

## Main definitions and results

* `New.Hall k`: complex-valued functions on `New.SimClass k`. The product is
  `(f * h) g = ∑ W, f (g | W) * h (g | V / W)` over stable `W` (a `finsum`), and `1` is the
  indicator of size `0`. The constant function with value `1` is `New.Hall.constOne`.
* `New.Hall.blockAverage`, `New.Hall.IsCuspidal`: the average over block triangular maps;
  cuspidality.
* `New.Hall.blockAverage_mul`: Mackey's formula, `δ(F * H) = δF * δH`, by a bijection between the
  stable subspaces of the block maps and triples (pair of stable subspaces, map, shear).
* `New.Hall.rankInner_mul_eq_rankInner_skew`: for `f` supported in dimension `d`,
  `New.Hall.skew d f` is adjoint to multiplication by `f`.
* `New.Hall.skew_mul`: for cuspidal `c` and `d ≠ 0`, `New.Hall.skew d c` is a derivation. It follows
  from Mackey's formula `New.Hall.blockAverage_mul` and the degree-zero case
  `New.Hall.rankInner_mul_of_isCuspidal`.
* `New.classInner_evalGL_prod`: the inner product `New.classInner` of a product with a class
  function `Y` is a mean over the group `New.parabolic b` of matrices that are block upper
  triangular for the levels `b : n → ι`; `New.blockHom b a` is the diagonal block of level `a`.

Notions from other files:
* `New.finMean`: the average of a complex function `f` on a finite set `G`: the sum of its values
  divided by the cardinality of `G`.
* `New.classInner f h`: the average over a finite group of `conj (f g) * h g`.

## Relation to the literature

Known; see `Lib.LocalGL.Green.TauFunctions` and `Lib.LocalGL.Green.CuspidalFunctions` for sources.
-/

@[expose] public section

noncomputable section

namespace New

/-!
## Similarity classes of matrices and the induction product

* `New.SimClass k`: similarity classes of square matrices of any size, invertible or not.
  `New.simClassOf g` is the class of an endomorphism `g`, and `New.SimClass.dim` and
  `New.SimClass.charpoly` give its size and characteristic polynomial. The size does not depend on
  the representative (`New.SimClass.dim_mk`).
-/

section HallDefs

open Module Quot

variable (k : Type*) [Field k]

/-- Similarity classes of square matrices over k of all sizes: pairs (n, endomorphism of kⁿ)
modulo intertwining by linear isomorphisms. -/
def SimClass : Type _ :=
  Quot fun a b : Σ n : ℕ, End k (Fin n → k) ↦
    ∃ e : (Fin a.fst → k) ≃ₗ[k] Fin b.fst → k, e.conj a.2 = b.2

/-- The complex-valued functions on similarity classes of square matrices over k of all sizes; the
product is parabolic induction (sum over stable subspaces). -/
@[implicit_reducible]
def Hall : Type _ := SimClass k → ℂ
  deriving AddCommGroup, Module ℂ, TopologicalSpace, T2Space, IsTopologicalAddGroup

variable {k}
  {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] (g : End k V) (c : SimClass k)

/-! ### The class of an endomorphism; stable subspaces -/

/-- The similarity class of an endomorphism g of a finite-dimensional k-vector space V, obtained
by choosing a basis of V. -/
def simClassOf : SimClass k := Quot.mk _ ⟨finrank k V, (finBasis k V).equivFun.conj g⟩

@[simp]
lemma simClassOf_out : simClassOf c.out.2 = c := (sound ⟨_, rfl⟩).symm.trans c.out_eq

/-- The subspaces W of V that are stable under the endomorphism g. -/
abbrev StableSubspace : Type _ := {W : Submodule k V // ∀ x ∈ W, g x ∈ W}

variable {g} (W : StableSubspace g) (n : ℕ) (F : Hall k)

/-- The endomorphism of a g-stable subspace W obtained by restricting g. -/
def StableSubspace.endOnSub : End k W := g.restrict W.prop

/-- The endomorphism of the quotient of V by a g-stable subspace W induced by g. -/
def StableSubspace.endOnQuot : V ⧸ (W : Submodule k V) →ₗ[k] V ⧸ (W : Submodule k V) :=
  W.val.mapQ _ g W.prop

/-- The dimension `n` of the space `k ^ n` on which the chosen representative of the class `c` acts.
-/
abbrev SimClass.dim : ℕ := c.out.1

/-- The class of an endomorphism of `k ^ n` has dimension `n`, whichever representative is
chosen. -/
lemma SimClass.dim_mk (a : Σ n : ℕ, End k (Fin n → k)) :
    SimClass.dim (k := k) (Quot.mk _ a) = a.1 := by
  -- The size is constant on classes (similar matrices have the same size), so it descends to a
  -- function `dimOf` on classes; both sides are values of `dimOf`.
  let dimOf : SimClass k → ℕ := Quot.lift (·.1) fun _ _ ⟨e, _⟩ ↦ eq_of_fin_equiv k e
  exact congrArg dimOf (Quot.out_eq (Quot.mk _ a : SimClass k))

/-- The function sending the similarity class of a k-linear endomorphism of k^n to its
characteristic polynomial in k[X]. -/
def SimClass.charpoly : SimClass k → Polynomial k :=
  lift (·.2.charpoly) fun _ _ ⟨_, h⟩ ↦ by simp [← h]

/-- The induction product: `(f * h) c` is the sum, over the subspaces `W` stable under the chosen
representative of `c`, of `f` at its class on `W` times `h` at its class on the quotient by `W`. -/
instance : Mul (Hall k) where
  mul f h := (∑ᶠ W : StableSubspace ·.out.2, f (simClassOf W.endOnSub) * h (simClassOf W.endOnQuot))

/-! ### Particular class functions -/

/-- The complex-valued function on classes of endomorphisms that takes the value 1 on every class,
in every dimension. -/
@[simp]
def Hall.constOne : Hall k := fun _ ↦ 1

/-- The function on similarity classes equal to F on classes of dimension n and zero on the
others. -/
@[simp]
def Hall.rankPart : Hall k := fun c ↦ if c.dim = n then F c else 0

/-- The unit of the induction product: the function that is `1` on the classes of dimension `0`
and `0` elsewhere. -/
instance : One (Hall k) := ⟨.rankPart 0 .constOne⟩

/-- For a complex function F on similarity classes and an invertible matrix g in `GL n k`, indexed
by a finite type n, the value of F at the class of the endomorphism of `n → k` given by g. -/
def Hall.evalGL {n : Type*} [Fintype n] [DecidableEq n] (g : GL n k) :
    ℂ := F (simClassOf g.val.toLin')

end HallDefs

/-!
## The commutative ring of class functions and invertibility of the constant function

* `New.simClassOf_eq_dualMap`: an endomorphism is similar to its transpose; this gives
  commutativity.
-/

section HallAlgebra

open Module StableSubspace Submodule Function Finset LinearMap LinearEquiv Polynomial BilinForm
  AEval' Quot

section

variable {k V V' : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup V'] [Module k V'] [Module.Finite k V']
  {g : End k V} {g' : End k V'} {f h : Hall k}

/-! ### Similarity classes and stable subspaces -/

/-- Two endomorphisms `g` and `g'` have the same similarity class if and only if a linear
isomorphism intertwines them. -/
lemma simClassOf_eq_iff :
    simClassOf g = simClassOf g' ↔ ∃ e : V ≃ₗ[k] V', ∀ x : V, e (g x) = g' (e x) := by
  unfold simClassOf
  generalize (finBasis k V).equivFun = b, (finBasis k V').equivFun = c
  -- Similarity is an equivalence relation, so equality of classes is similarity of the matrices.
  have h_equiv : Equivalence fun A B : Σ n, End k (Fin n → k) ↦
      ∃ e : (Fin A.fst → k) ≃ₗ[k] Fin B.fst → k, e.conj A.snd = B.snd := by
    refine ⟨fun A ↦ ⟨LinearEquiv.refl k _, rfl⟩, ?_, ?_⟩
    · rintro A B ⟨e, he⟩
      exact ⟨e.symm, by simp [← he]⟩
    · rintro A B C ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e.trans e', by simp [← he', ← he, DFunLike.ext_iff]⟩
  refine (h_equiv.quot_mk_eq_iff _ _).trans ?_
  -- Transport an intertwiner along the coordinate maps `b` and `c`, in either direction.
  constructor
  · rintro ⟨e, he⟩
    refine ⟨b ≪≫ₗ e ≪≫ₗ c.symm, fun x ↦ ?_⟩
    simpa [symm_apply_eq] using LinearMap.congr_fun he (e (b x))
  · rintro ⟨e, he⟩
    exact ⟨b.symm ≪≫ₗ e ≪≫ₗ c, by simp [DFunLike.ext_iff, he]⟩

lemma simClassOf_eq_of_equiv (e : V ≃ₗ[k] V') (he : ∀ x : V, e (g x) = g' (e x)) :
    simClassOf g = simClassOf g' :=
  simClassOf_eq_iff.mpr ⟨e, he⟩

/-- The chosen representative of the class of `g`, an endomorphism of `k^d` with `d` the dimension
of `V`, is conjugate to `g` by a linear isomorphism `e : k^d ≃ V`. -/
lemma exists_equiv_simClassOf_out (g : End k V) :
    ∃ e : (Fin (simClassOf g).dim → k) ≃ₗ[k] V, ∀ x : Fin (simClassOf g).dim → k,
      e ((simClassOf g).out.2 x) = g (e x) :=
  simClassOf_eq_iff.mp (simClassOf_out (simClassOf g))

@[simp]
lemma dim_simClassOf : (simClassOf g).dim = finrank k V :=
  SimClass.dim_mk (k := k) _

@[simp]
lemma charpoly_simClassOf : (simClassOf g).charpoly = g.charpoly :=
  charpoly_conj (finBasis k V).equivFun g

/-! ### Values of sums and products -/

/-- Two class functions are equal once they agree at the class of every endomorphism of every
`k^n`. -/
@[ext]
lemma Hall.ext (H : ∀ (n : ℕ) (g : End k (Fin n → k)), f (simClassOf g) = h (simClassOf g)) :
    f = h := by
  funext c
  simpa only [simClassOf_out c] using H c.out.fst c.out.snd

/-- The value of the induction product `f * h` at a class `c`, as in its definition. Let g be the
chosen representative of `c`. The value is the finite sum, over the g-stable subspaces W, of `f` at
the class of the restriction of g to W times `h` at the class of the map g induces on the quotient
by W. -/
lemma Hall.mul_apply (c : SimClass k) :
    (f * h) c =
      ∑ᶠ W : StableSubspace c.out.2, f (simClassOf W.endOnSub) * h (simClassOf W.endOnQuot) :=
  rfl

/-- If `f` vanishes in dimensions below `m` and `h` in dimensions below `n`, then the induction
product `f * h` vanishes in dimensions below `m + n`. -/
lemma Hall.mul_apply_eq_zero_of_dim_lt {m n : ℕ} (hf : ∀ c : SimClass k, c.dim < m → f c = 0)
    (hh : ∀ c : SimClass k, c.dim < n → h c = 0) (c : SimClass k) (hc : c.dim < m + n) :
    (f * h) c = 0 := by
  -- The dimensions of `W` and of the quotient add up to `c.dim < m + n`, so one factor vanishes.
  rw [Hall.mul_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun W ↦ ?_
  have h_dims : finrank k ((Fin c.out.1 → k) ⧸ W.val) + finrank k W.val = c.dim := by
    rw [W.val.finrank_quotient_add_finrank, Module.finrank_fin_fun]
  rcases lt_or_ge (finrank k W.val) m with h_lt | h_ge
  · rw [hf _ (dim_simClassOf.trans_lt h_lt), zero_mul]
  · have h_quot_lt : finrank k ((Fin c.out.1 → k) ⧸ W.val) < n := by omega
    rw [hh _ (dim_simClassOf.trans_lt h_quot_lt), mul_zero]

@[simp]
lemma Hall.add_apply (c : SimClass k) : (f + h) c = f c + h c := rfl

@[simp]
lemma Hall.zero_apply (c : SimClass k) : (0 : Hall k) c = 0 := rfl

@[simp]
theorem Hall.neg_apply (c : SimClass k) : (-f) c = -f c := rfl

@[simp]
lemma Hall.smul_apply (a : ℂ) (c : SimClass k) : (a • f) c = a * f c := rfl

@[simp]
lemma Hall.one_apply (c : SimClass k) : (1 : Hall k) c = if c.dim = 0 then 1 else 0 := rfl

/-- The block triangular endomorphism `(w, v) ↦ (b w, x w + a v)` of `V' × V`. -/
abbrev blockTriangularEnd (a : End k V) (b : End k V') (x : V' →ₗ[k] V) : V' × V →ₗ[k] V' × V :=
  (b.prod x).coprod (LinearMap.prod 0 a)

/-- For finite `k`, an endomorphism of a finite-dimensional space has finitely many stable
subspaces. -/
instance fintypeStableSubspace [Finite k] : Fintype (StableSubspace g) :=
  have := @finite_of_finite k V
  .ofFinite _

/-- For finite k, there are finitely many linear maps between two finite-dimensional spaces. -/
instance fintypeLinearHom [Finite k] : Fintype (V →ₗ[k] V') := @.ofFinite _ (finite_of_finite k)

/-- If `p` is surjective with kernel `W` and intertwines `g` and `g'`, then `g` on `V / W` has the
class of `g'`. -/
lemma simClassOf_endOnQuot (p : V →ₗ[k] V') (hp : ∀ x : V, p (g x) = g' (p x))
    (W : StableSubspace g) (h_surj : Surjective p) (h_ker : (W : Submodule k V) = p.ker) :
    simClassOf W.endOnQuot = simClassOf g' := by
  -- `p` induces an isomorphism `e : V ⧸ W ≃ V'`, which sends the class of `v` to `p v`.
  let e : (V ⧸ W.val) ≃ₗ[k] V' :=
    quotEquivOfEq W.val p.ker h_ker ≪≫ₗ p.quotKerEquivOfSurjective h_surj
  refine simClassOf_eq_of_equiv e fun x ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | H v => simpa [e, StableSubspace.endOnQuot] using hp v

/-- If `p` is injective with image `U` and intertwines `g` and `g'`, then `g'` on `U` has the class
of `g`. -/
lemma simClassOf_endOnSub (p : V →ₗ[k] V') (hp : ∀ x : V, p (g x) = g' (p x))
    {U : StableSubspace g'} (h_inj : Injective p) (h_range : p.range = (U : Submodule k V')) :
    simClassOf U.endOnSub = simClassOf g := by
  -- `p` induces an isomorphism `e : V ≃ U`; on vectors, the intertwining is `hp`.
  let e : V ≃ₗ[k] U.val := ofInjective p h_inj ≪≫ₗ ofEq p.range U.val h_range
  have he (x : V) : e (g x) = U.endOnSub (e x) := Subtype.ext (hp x)
  exact (simClassOf_eq_of_equiv e he).symm

/-- For a `k`-linear map `p` intertwining `g` and `g'`, the preimage `p⁻¹(U)` of a `g'`-stable
subspace `U`, as a `g`-stable subspace. -/
def StableSubspace.comap (p : V →ₗ[k] V') (hp : ∀ x : V, p (g x) = g' (p x))
    (U : StableSubspace g') : StableSubspace g :=
  ⟨Submodule.comap p U, fun x hx ↦ by simpa [hp] using U.prop (p x) hx⟩

/-- For injective `p` intertwining `g` and `g'` and `U` in the image of `p`, `g` on `p⁻¹(U)` has
the class of `g'` on `U`. -/
@[simp]
lemma simClassOf_endOnSub_comap (p : V →ₗ[k] V') (hp : ∀ x : V, p (g x) = g' (p x))
    (h_ker : p.ker = ⊥) (U : StableSubspace g') (h_le : (U : Submodule k V') ≤ p.range) :
    simClassOf (StableSubspace.comap p hp U).endOnSub = simClassOf U.endOnSub :=
  -- `p` restricts to an isomorphism `p⁻¹(U) ≃ U`; on vectors, the intertwining is `hp`.
  simClassOf_eq_of_equiv (comap_equiv_self_of_inj_of_le (ker_eq_bot.mp h_ker) h_le)
    fun x ↦ Subtype.ext (hp x)

open scoped Classical in
/-- For `p` intertwining `g` and `g'`, the sum of `F` over the `g`-stable subspaces containing
`ker p` equals the sum of `F (p⁻¹ W)` over the `g'`-stable subspaces `W` contained in the image of
`p`. -/
lemma StableSubspace.sum_comap [Finite k] (p : V →ₗ[k] V') (hp : ∀ x : V, p (g x) = g' (p x))
    (F : StableSubspace g → ℂ) :
    ∑ W : StableSubspace g with p.ker ≤ W.val, F W =
      ∑ W : StableSubspace g' with W.val ≤ p.range, F (comap p hp W) := by
  -- Image and preimage under `p` are inverse bijections between the two index sets.
  have h_map_stable (W : StableSubspace g) : ∀ y ∈ W.val.map p, g' y ∈ W.val.map p := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨g x, W.prop x hx, hp x⟩
  refine sum_nbij' (fun W ↦ ⟨W.val.map p, h_map_stable W⟩) (comap p hp) ?_ ?_ ?_ ?_ ?_
  · -- The image of `W` lies in the range of `p`.
    simp [map_le_range]
  · -- The preimage of `U` contains `ker p`.
    simp [comap, ker_le_comap]
  · -- For `W` containing `ker p`, the preimage of the image of `W` is `W`.
    simp +contextual [comap, comap_map_eq]
  · -- For `U` in the range of `p`, the image of the preimage of `U` is `U`.
    simp +contextual [comap, map_comap_eq]
  · -- The summands match.
    simp +contextual [comap, comap_map_eq]

/-- For surjective `p` intertwining `g` and `g'`, `g` on `V / p⁻¹(U)` has the class of `g'` on
`V' / U`. -/
@[simp]
lemma simClassOf_endOnQuot_comap (p : V →ₗ[k] V') (hp : ∀ x : V, p (g x) = g' (p x))
    (h_range : p.range = ⊤) (U : StableSubspace g') :
    simClassOf (StableSubspace.comap p hp U).endOnQuot = simClassOf U.endOnQuot := by
  -- `p` followed by the quotient map is surjective with kernel `p⁻¹(U)`, and intertwines `g` with
  -- the map induced by `g'` on `V' ⧸ U`.
  have h_comm (x : V) : (U.val.mkQ ∘ₗ p) (g x) = U.endOnQuot ((U.val.mkQ ∘ₗ p) x) := by
    simp [hp, StableSubspace.endOnQuot]
  have h_ker : (StableSubspace.comap p hp U).val = (U.val.mkQ ∘ₗ p).ker := by
    simp [StableSubspace.comap, LinearMap.ker_comp]
  exact simClassOf_endOnQuot (U.val.mkQ ∘ₗ p) h_comm _
    (U.val.mkQ_surjective.comp (LinearMap.range_eq_top.mp h_range)) h_ker

variable [Finite k]

/-- The product f * h at the class of an endomorphism g is the sum, over the g-stable subspaces
W, of f at g on W times h at g on V/W. -/
@[local simp]
lemma Hall.mul_simClassOf :
    (f * h) (simClassOf g) =
      ∑ᶠ W : StableSubspace g, f (simClassOf W.endOnSub) * h (simClassOf W.endOnQuot) := by
  -- The product is defined through the chosen representative of `simClassOf g`; an isomorphism
  -- `e` intertwining it with `g` matches the stable subspaces and their classes.
  obtain ⟨e, he⟩ := exists_equiv_simClassOf_out g
  rw [Hall.mul_apply, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simpa using
    sum_comap e.toLinearMap he fun W ↦ f (simClassOf W.endOnSub) * h (simClassOf W.endOnQuot)

/-- For a finite field `k`, a finite-dimensional quotient `A` of `k[X]` carries a linear form `L`
for which the pairing `(x, y) ↦ L (x * y)` is nondegenerate. -/
lemma exists_nondegenerate_mul_form (I : Ideal k[X]) [Module.Finite k (k[X] ⧸ I)] :
    ∃ L : Dual k (k[X] ⧸ I), BilinForm.Nondegenerate ((LinearMap.mul k (k[X] ⧸ I)).compr₂ L) := by
  -- Let `k[X]` act on the dual of `A` by `(q • φ) x = φ (q • x)`. Over a principal ideal domain
  -- some `L` has the same annihilator as the whole module.
  let h_module : Module k[X] (Dual k (k[X] ⧸ I)) :=
    compHom _ (R := k[X]ᵈᵐᵃ) (.toOpposite (.id k[X]) .all)
  obtain ⟨L, hL⟩ : ∃ L : Dual k (k[X] ⧸ I), (toSpanSingleton k[X] (Dual k (k[X] ⧸ I)) L).ker =
      Module.annihilator k[X] (Dual k (k[X] ⧸ I)) :=
    exists_ker_toSpanSingleton_eq_annihilator k[X] (Dual k (k[X] ⧸ I))
  refine ⟨L, .ofSeparatingLeft ?_⟩
  rintro ⟨q⟩ hq
  -- If `q` pairs to zero with everything then `q • L = 0`, so `q` kills every linear form `φ`;
  -- evaluating `q • φ = 0` at `1` shows that `φ` vanishes on the class of `q`.
  have h_ann : q ∈ Module.annihilator k[X] (Dual k (k[X] ⧸ I)) := hL.le (LinearMap.ext hq)
  refine (forall_dual_apply_eq_zero_iff k _).mp fun φ ↦ ?_
  have h_smul_eq_zero : q • φ = 0 := Module.mem_annihilator.mp h_ann φ
  have h_eval : φ (q • 1) = 0 := LinearMap.congr_fun h_smul_eq_zero 1
  -- The class of `q` is `q • 1`.
  rwa [← mul_one q]

/-- Every endomorphism of a finite-dimensional space over a finite field is similar to its
transpose. -/
lemma simClassOf_eq_dualMap : simClassOf g = simClassOf g.dualMap := by
  classical
  -- By the structure theorem `V` is a product of cyclic modules `k[X] ⧸ (p i ^ n i)`, with `g`
  -- acting as `X`.
  obtain ⟨ι, h_fintype, p, -, n, ⟨e⟩⟩ :=
    equiv_directSum_of_isTorsion (AEval.isTorsion_of_finiteDimensional k V g)
  let E : V ≃ₗ[k] ∀ i, k[X] ⧸ k[X] ∙ p i ^ n i :=
    AEval'.of g ≪≫ₗ (e ≪≫ₗ DFinsupp.linearEquivFunOnFintype).restrictScalars k
  have h_fin : ∀ i, Module.Finite k (k[X] ⧸ k[X] ∙ p i ^ n i) := Finite.pi_iff.mp (.equiv E)
  -- Each factor is identified with its dual by a pairing `L i (x * y)`; summing over the factors
  -- identifies `V` with its dual.
  choose L hL using fun i ↦ exists_nondegenerate_mul_form (k[X] ∙ p i ^ n i)
  let D : V ≃ₗ[k] Dual k V :=
    E ≪≫ₗ piCongrRight (fun i ↦ toDual _ (hL i)) ≪≫ₗ lsum k _ k ≪≫ₗ E.dualMap
  -- Multiplication by `X` is self-adjoint for these pairings, so `D` carries `g` to its transpose.
  refine simClassOf_eq_of_equiv D ?_
  simp only [toDual, trans_apply, ← X_smul_of, LinearEquiv.restrictScalars_apply,
    LinearEquiv.map_smul, LinearMap.lsum_apply, piCongrRight_apply, Pi.smul_apply,
    linearEquivOfInjective_apply, map_sum, LinearMap.ext_iff, LinearMap.coe_sum, Finset.sum_apply,
    LinearEquiv.dualMap_apply, coe_comp, coe_proj, Function.comp_apply, Function.eval, compr₂_apply,
    mul_apply_apply, Algebra.smul_mul_assoc, LinearMap.dualMap_apply, Algebra.mul_smul_comm,
    implies_true, D, E]

open scoped Classical in
/-- For finite `k`, the induction product makes the class functions a commutative ring. -/
instance : CommRing (Hall k) := by
  refine' { mul_assoc := _, .. } <;> intros <;> ext _ g
  -- The laws of `0` and distributivity hold term by term; in `1 * a` only `W = ⊥` contributes,
  -- in `a * 1` only `W = ⊤`.
  any_goals solve
    | simp [simClassOf_endOnQuot (g' := g) 1 _ ⟨⊥, _⟩ surjective_id rfl,
        simClassOf_endOnSub (g := g) .id, finsum_eq_sum_of_fintype, injective_id, finrank_zero_iff,
        subsingleton_iff_eq_bot, Subtype.coe_eq_iff, mul_add, sum_add_distrib, add_mul]
  · -- Associativity. Both sides are sums over chains `U ≤ W` of stable subspaces: those of `W`
    -- are those of the whole space below `W`, those of a quotient are those above its kernel.
    have h_sums_sub (W : StableSubspace g) :=
      sum_comap (g := W.endOnSub) W.val.subtype (congrFun rfl)
    have h_sums_quot (W : StableSubspace g) :=
      sum_comap (g := g) (g' := W.endOnQuot) W.val.mkQ (by intro; rfl)
    simp_all only [ker_subtype, bot_le, filter_true, range_subtype, Subtype.coe_le_coe, sum_filter,
      Subtype.forall, ker_mkQ, range_mkQ, le_top, Hall.mul_simClassOf, finsum_eq_sum_of_fintype,
      Subtype.coe_eta, simClassOf_endOnSub_comap, sum_mul, ite_mul, mul_assoc, zero_mul, sum_comm,
      simClassOf_endOnQuot_comap, mul_sum]
    -- For `U ≤ W`, the quotient of `W` by `U` is the image of `W` in the quotient by `U`.
    congr!
    apply simClassOf_endOnQuot ((mkQ _).submoduleComap _) ?h_comm _ ?h_surj
    case h_comm => tauto
    case h_surj =>
      rintro ⟨⟨x⟩⟩
      tauto
    simp [submoduleComap, ker_restrict]
    rfl
  · -- Commutativity. Replace `g` by its transpose on the right. Taking annihilators matches the
    -- stable subspaces of `g` and of its transpose, and exchanges restriction and quotient up to
    -- transposition.
    nth_rw 2 [simClassOf_eq_dualMap]
    rw [Hall.mul_simClassOf, Hall.mul_simClassOf, finsum_eq_sum_of_fintype,
      finsum_eq_sum_of_fintype]
    refine sum_nbij' (⟨dualAnnihilator ·, by aesop⟩)
      (⟨dualCoannihilator ·, by grind [mem_dualCoannihilator, g.dualMap_apply]⟩) ?_ ?_ ?_ ?_ ?_
    all_goals simp_intro W [Subspace.dualCoannihilator_dualAnnihilator_eq]
    rw [simClassOf_eq_dualMap, mul_comm, simClassOf_eq_dualMap,
      simClassOf_endOnSub W.val.mkQ.dualMap, simClassOf_endOnQuot W.val.subtype.dualMap]
    · -- The transpose of the inclusion of `W` intertwines the transposes.
      aesop
    · exact dualMap_surjective_of_injective (Submodule.injective_subtype _)
    · -- The kernel of the transposed inclusion is the annihilator of `W`.
      aesop
    · -- The transpose of the quotient map intertwines the transposes.
      aesop
    · exact dualMap_injective_of_surjective (mkQ_surjective _)
    · -- The image of the transposed quotient map is the annihilator of `W`.
      aesop (add simp [range_dualMap_mkQ_eq])

/-! ### The constant function 1 is a unit -/

/-- The m-th power of 1 − 𝟙, where 1 is the unit and 𝟙 the constant function, vanishes in
dimensions below m. -/
lemma Hall.one_sub_constOne_pow_apply_eq_zero (m : ℕ) :
    ∀ c : SimClass k, c.dim < m → ((1 - constOne : Hall k) ^ m) c = 0 := by
  -- `1 - constOne` vanishes in dimension `0`, and such bounds add under products.
  have h_zero (c : SimClass k) (hc : c.dim < 1) : (1 - constOne : Hall k) c = 0 := by
    have h_dim : c.dim = 0 := by omega
    simp [sub_eq_add_neg, h_dim]
  induction m with
  | zero =>
    intro c hc
    exact absurd hc (Nat.not_lt_zero _)
  | succ m ih =>
    intro c hc
    simpa only [pow_succ] using mul_apply_eq_zero_of_dim_lt ih h_zero c hc

/-- The class functions form a `ℂ`-algebra: scalars act pointwise. -/
instance : Algebra ℂ (Hall k) := by
  -- At each class, a scalar comes out of every term of the finite sum defining the product.
  refine Algebra.ofModule ?_ ?_ <;>
    aesop (add simp [mul_sum, finsum_eq_sum_of_fintype]) (add 1% (by ring))

/-- Over a finite field `k`, the constant function `𝟙` on similarity classes of square matrices of
all sizes is invertible for the induction product. -/
lemma Hall.isUnit_constOne : IsUnit (constOne : Hall k) := by
  -- `(1 - constOne) ^ i` vanishes in dimensions below `i`, so the geometric series in
  -- `1 - constOne` is a finite sum at each class; its sum inverts `constOne = 1 - (1 - constOne)`.
  have h_sum : Summable fun i : ℕ ↦ (1 - constOne : Hall k) ^ i := by
    refine Pi.summable.mpr fun c ↦ summable_of_ne_finset_zero (s := Finset.range (c.dim + 1))
      fun i hi ↦ ?_
    exact one_sub_constOne_pow_apply_eq_zero i c (by simpa [Nat.succ_le_iff] using hi)
  -- The product is continuous: each of its values is a finite sum of products of values.
  have h_topRing : IsTopologicalRing (Hall k) := by
    refine { continuous_mul := continuous_pi fun c ↦ ?_ }
    rw [← simClassOf_out c]
    simp only [mul_simClassOf, finsum_eq_sum_of_fintype]
    fun_prop
  have h_geom : constOne * ∑' i : ℕ, (1 - constOne : Hall k) ^ i = 1 := by
    simpa only [sub_sub_cancel] using h_sum.one_sub_mul_tsum_pow
  exact .of_mul_eq_one _ h_geom

end

end HallAlgebra

end New

namespace New.Hall

/-!
## Block averages, cuspidality and inner products

* `New.Hall.rankInner`, `New.Hall.skew`: the inner product in rank `n`, and the inner product of `F`
  with the block average of `H` in the second class.
* `New.Hall.brauerLift`, `New.Hall.mulMoebius`, `New.Hall.greenCuspidal`: the sum `β_η` of `η` over
  the eigenvalues, and the function `(β_η · μ) * constOne`, where μ = `New.Hall.moebius` is the
  inverse of `New.Hall.constOne`.
-/

section CoproductDefs

open Module ComplexConjugate Ring

variable {k : Type*} [Field k] [Finite k] (n : ℕ) (F H : Hall k)

/-- For F on similarity classes, the function of two classes a, b averaging F over block upper
triangular endomorphisms with diagonal blocks a, b and arbitrary off-diagonal block. -/
def blockAverage : SimClass k → Hall k :=
  fun a b ↦ finMean fun x ↦ F (simClassOf (blockTriangularEnd a.out.2 b.out.2 x))

/-- The inverse μ of the constant function `New.Hall.constOne` for the induction product. -/
abbrev moebius : Hall k := constOne⁻¹ʳ

/-- The pointwise product F·μ, where μ is the inverse, for the parabolic-induction product, of
the constant class function 1. -/
abbrev mulMoebius : Hall k := fun c ↦ F c * moebius c

/-- F is cuspidal: its average over block triangular endomorphisms with diagonal blocks a, b
vanishes whenever both a and b have nonzero dimension. -/
def IsCuspidal : Prop := ∀ a b : SimClass k, a.dim ≠ 0 → b.dim ≠ 0 → F.blockAverage a b = 0

/-- For n and complex functions F, H on similarity classes, the average over GL_n(k) of the
conjugate of F times H. -/
def rankInner : ℂ :=
  finMean fun g : (End k (Fin n → k))ˣ ↦ conj (F (simClassOf g.val)) * H (simClassOf g.val)

/-- The function sending a class a to the average over b in GL_n(k) of conj F(b) times the block
average `New.Hall.blockAverage` of H at (a, b). -/
def skew : Hall k := fun a ↦ rankInner n F (H.blockAverage a)

variable (k) {K : Type*} [Field K] [Algebra k K] (η : K → ℂ)

/-- The class function β_η sending an endomorphism to the sum of η over the roots in K of its
characteristic polynomial, counted with multiplicity. -/
@[simp]
def brauerLift : Hall k := fun c ↦ ((c.charpoly.aroots K).map η).sum

/-- The class function C_η = (β_η·μ) ∗ 𝟙: the pointwise product of the eigenvalue sum β_η with
the inverse μ of 𝟙, multiplied in the induction product by the constant function 𝟙. -/
def greenCuspidal : Hall k := (brauerLift k η).mulMoebius * constOne

end CoproductDefs

/-! ## Mackey's formula for block averages -/

section MackeyFormula

open Module Submodule.Quotient StableSubspace Free LinearMap Fintype QuotientAddGroup

variable {k V W : Type*} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup W] [Module k W] [Module.Finite k W]
  (F H : Hall k) (a : End k V) (b : End k W)

/-- The block average of `F` at the classes of `a` and `b` is the average of `F` over the block maps
`New.blockTriangularEnd a b x`, the map `(w, v) ↦ (b w, x w + a v)` of `W × V` for `x : W →ₗ[k] V`,
for these representatives `a`, `b` rather than the chosen ones. -/
lemma blockAverage_simClassOf :
    F.blockAverage (simClassOf a) (simClassOf b) =
      finMean fun x : W →ₗ[k] V ↦ F (simClassOf (blockTriangularEnd a b x)) := by
  -- `blockAverage` is defined with the chosen representatives of the two classes; the isomorphisms
  -- `e` and `f` carry them to `a` and `b`, and `f × e` conjugates the block maps.
  obtain ⟨e, he⟩ : ∃ e : (Fin (simClassOf a).out.1 → k) ≃ₗ[k] V,
      ∀ x, e ((simClassOf a).out.2 x) = a (e x) := exists_equiv_simClassOf_out a
  obtain ⟨f, hf⟩ : ∃ f : (Fin (simClassOf b).out.1 → k) ≃ₗ[k] W,
      ∀ x, f ((simClassOf b).out.2 x) = b (f x) := exists_equiv_simClassOf_out b
  refine finMean_equiv (f.arrowCongr e).symm.toEquiv fun x ↦ congrArg F ?_
  exact simClassOf_eq_of_equiv (f.prodCongr e) (by simp [he, hf])

omit [Finite k] [Module.Finite k V] [Module.Finite k W] in
/-- Any maps `B → A` and `W ⧸ B → V ⧸ A` are induced by one map `W → V` that takes `B` into `A`. -/
lemma exists_restrict_eq_and_mapQ_eq {A : Submodule k V} {B : Submodule k W} (α : B →ₗ[k] A)
    (β : W ⧸ B →ₗ[k] V ⧸ A) :
    ∃ (y : W →ₗ[k] V) (hy : ∀ w ∈ B, y w ∈ A), y.restrict hy = α ∧ B.mapQ A y hy = β := by
  -- Extend `α` to `c : W → A`, lift `β` to `r : W ⧸ B → V`, and add.
  obtain ⟨c, rfl⟩ : ∃ g : W →ₗ[k] A, g ∘ₗ B.subtype = α := α.exists_extend
  obtain ⟨r, rfl⟩ := projective_lifting_property _ β A.mkQ_surjective
  refine ⟨A.subtype ∘ₗ c + r ∘ₗ B.mkQ, fun w hw ↦ by simp [(mk_eq_zero _).mpr hw], ?_, ?_⟩
  all_goals
    ext w
    simp [(mk_eq_zero _).mpr]

/-- The right side of Mackey's formula written out: a sum over the pairs `P = (A, B)` of stable
subspaces of `a` and `b` of the mean, over the maps `B → A` and `W ⧸ B → V ⧸ A`, of `F` at the block
map `blockTriangularEnd` on `B × A` of the restrictions `endOnSub` of `a`, `b`, times `H` at the
block map on the quotients of the induced maps `endOnQuot`. -/
private lemma sum_blockAverage_mul_blockAverage_eq :
    ∑ A : StableSubspace a,
        (F.blockAverage (simClassOf A.endOnSub) * H.blockAverage (simClassOf A.endOnQuot))
          (simClassOf b) =
      ∑ P : StableSubspace a × StableSubspace b,
        (∑ z : (P.2.val →ₗ[k] P.1.val) × (W ⧸ P.2.val →ₗ[k] V ⧸ P.1.val),
          F (simClassOf (blockTriangularEnd P.1.endOnSub P.2.endOnSub z.1)) *
            H (simClassOf (blockTriangularEnd P.1.endOnQuot P.2.endOnQuot z.2))) /
          ((Fintype.card (P.2.1 →ₗ[k] P.1.1) * Fintype.card (W ⧸ P.2.1 →ₗ[k] V ⧸ P.1.1) : ℕ) :
            ℂ) := by
  -- Expand the Hall product and the two block averages, and multiply the two means.
  simp [mul_simClassOf, blockAverage_simClassOf, finMean_eq, finsum_eq_sum_of_fintype,
    div_mul_div_comm, ← Nat.cast_mul, sum_mul_sum, ← sum_prod_type']

/-- Mackey formula for the block averaging map δ = `New.Hall.blockAverage`, where δF(x, y) averages
`F` over block upper triangular endomorphisms with diagonal blocks x, y and arbitrary off-diagonal
block. The claim is that δ(F * H) at the classes of `a` and `b` equals a sum over the `a`-stable
subspaces `A`, with `A.endOnSub` and `A.endOnQuot` the maps `a` induces on `A` and on `V ⧸ A`. Each
term is the Hall product of the functions δF(class of `A.endOnSub`, ·) and δH(class of
`A.endOnQuot`, ·), taken in the second variable and evaluated at the class of `b`. -/
lemma blockAverage_mul :
    (F * H).blockAverage (simClassOf a) (simClassOf b) =
      ∑ A : StableSubspace a,
        (F.blockAverage (simClassOf A.endOnSub) * H.blockAverage (simClassOf A.endOnQuot))
          (simClassOf b) := by
  classical
  -- The left side sums over pairs `(x, U)` with `U` stable under `blockTriangularEnd a b x`. Such a
  -- `U` is the preimage of a product `B × A` of stable subspaces under a shear
  -- `(w, v) ↦ (w, v + s w)`. Here `s` is unique modulo the space `S (A, B)` of maps taking `B` into
  -- `A`, which contains `y = x - (a s - s b)`. So `φ` parametrises the pairs by `(A, B)`, `y` and
  -- the class of `s`.
  let S (P : StableSubspace a × StableSubspace b) : Submodule k (W →ₗ[k] V) :=
    P.snd.val.compatibleMaps P.fst.val
  let φ : (Σ P : StableSubspace a × StableSubspace b, S P × ((W →ₗ[k] V) ⧸ S P)) →
      Σ x : W →ₗ[k] V, StableSubspace (blockTriangularEnd a b x)
    | ⟨⟨A, B⟩, y, s⟩ => ⟨a ∘ₗ s.out - s.out ∘ₗ b + y,
      comap (LinearEquiv.skewProd 1 1 s.out).toLinearMap (g' := blockTriangularEnd a b y)
        (by
          rintro ⟨w, v⟩
          simp only [coprod_apply, LinearMap.prod_apply, LinearMap.coe_add, Function.prod_apply,
            Pi.add_apply, LinearMap.sub_apply, coe_comp, Function.comp_apply, LinearMap.zero_apply,
            Prod.mk_add_mk, add_zero, LinearEquiv.coe_coe, LinearEquiv.skewProd_apply,
            one_apply_eq_self, map_add, Prod.mk.injEq, true_and]
          grind)
        ⟨.prod B A, fun _ hx ↦
          ⟨add_mem (B.prop _ hx.1) (zero_mem _), add_mem (y.prop hx.1) (A.prop _ hx.2)⟩⟩⟩
  have mem_φ (P : StableSubspace a × StableSubspace b) (y : S P) (s : (W →ₗ[k] V) ⧸ S P) (w : W)
      (v : V) : (w, v) ∈ (φ ⟨P, y, s⟩).snd.val ↔ w ∈ P.snd.val ∧ v + s.out w ∈ P.fst.val := by
    simp [φ, comap]
  have φ_inj : φ.Injective := by
    rintro ⟨⟨A, B⟩, y, s⟩ ⟨⟨A', B'⟩, y', s'⟩ h
    obtain ⟨hx, hU⟩ := Sigma.subtype_ext_iff.1 h
    have mem_iff (w : W) (v : V) :
        w ∈ B.val ∧ v + s.out w ∈ A.val ↔ w ∈ B'.val ∧ v + s'.out w ∈ A'.val := by
      rw [← mem_φ (A, B) y, ← mem_φ (A', B') y', hU]
    have hA (v : V) : v ∈ A.val ↔ v ∈ A'.val := by simpa using mem_iff 0 v
    obtain rfl : A = A' := Subtype.ext (SetLike.ext hA)
    -- at `v = -s w` the left side holds for `w ∈ B`, and at `v = -s' w` the right side for `w ∈ B'`
    have h_left (w : W) (hw : w ∈ B.val) : w ∈ B'.val ∧ -s.out w + s'.out w ∈ A.val :=
      (mem_iff w (-s.out w)).1 ⟨hw, by simp⟩
    have h_right (w : W) (hw : w ∈ B'.val) : w ∈ B.val :=
      ((mem_iff w (-s'.out w)).2 ⟨hw, by simp⟩).1
    obtain rfl : B = B' :=
      Subtype.ext (SetLike.ext fun w ↦ ⟨fun hw ↦ (h_left w hw).left, h_right w⟩)
    -- `-s w + s' w ∈ A` for `w ∈ B`: the two classes agree
    obtain rfl : s = s' := s.out_equiv_out.1 (leftRel_apply.2 fun w hw ↦ (h_left w hw).right)
    simpa [φ] using hx
  have φ_surj : φ.Surjective := by
    rintro ⟨x, U⟩
    -- `A` is the preimage of `U` under `inr` and `B` the first projection of `U`; the map `t`
    -- into `U` extends a section of `U → B`, and `s` is the class of minus its second component.
    let A : StableSubspace a := U.comap (inr ..) (by simp)
    let B : StableSubspace b := ⟨U.val.map (fst ..), fun _ ⟨z, hz, h_fst⟩ ↦
      ⟨blockTriangularEnd a b x z, U.property z hz, by simp [← h_fst]⟩⟩
    obtain ⟨r, hr⟩ := projective_lifting_property _ .id ((fst ..).submoduleMap_surjective U.val)
    obtain ⟨t, rfl⟩ := r.exists_extend
    have t_fst (w : W) (hw : w ∈ B.val) : (t w).val.fst = w := congr($hr ⟨w, hw⟩)
    let s := (S (A, B)).mkQ (-snd .. ∘ₗ U.val.subtype ∘ₗ t)
    -- For `w ∈ B` the vector `(w, -s.out w)` is `t w` plus an element of `0 × A`.
    have graph_mem (w : W) (hw : w ∈ B.val) : (w, -s.out w) ∈ U.val := by
      simpa [Prod.add_def,
        t_fst w hw] using add_mem (t w).property (QuotientAddGroup.eq.1 s.out_eq hw)
    have mem_U (w : W) (v : V) : w ∈ B.val ∧ v + s.out w ∈ A.val ↔ (w, v) ∈ U.val := by
      refine (and_congr_right fun hw ↦ ?_).trans (and_iff_right_of_imp fun h ↦ ⟨_, h, rfl⟩)
      -- membership in `A` is membership of `(0, v)` in `U`
      have h_A_mem : v + s.out w ∈ A.val ↔ ((0 : W), v + s.out w) ∈ U.val := Iff.rfl
      rw [h_A_mem]
      simpa using U.val.sub_mem_iff_left (x := (w, v)) (graph_mem w hw)
    have hy : x - (a ∘ₗ s.out - s.out ∘ₗ b) ∈ S (A, B) := fun w hw ↦ by
      simpa [sub_add,
        ← sub_eq_add_neg] using ((mem_U _ _).mpr (U.property _ (graph_mem w hw))).right
    -- `(A, B)`, `y` and `s` give back the map `x`, and by `mem_U` the subspace `U`.
    let y : S (A, B) := ⟨x - (a ∘ₗ s.out - s.out ∘ₗ b), hy⟩
    refine ⟨⟨(A, B), y, s⟩, Sigma.subtype_ext ?_ ?_⟩
    · exact add_sub_cancel ..
    · exact SetLike.ext fun ⟨w, v⟩ ↦ (mem_φ (A, B) y s w v).trans (mem_U w v)
  have φ_bij : φ.Bijective := ⟨φ_inj, φ_surj⟩
  -- The left side is the sum over the pairs `(x, U)`, reindexed by `φ`, divided by `#(W → V)`.
  have h_lhs : (F * H).blockAverage (simClassOf a) (simClassOf b) =
      (∑ i, F (simClassOf (φ i).2.endOnSub) * H (simClassOf (φ i).2.endOnQuot)) /
        (Fintype.card (W →ₗ[k] V) : ℂ) := by
    simp [mul_simClassOf, blockAverage_simClassOf, finMean_eq, finsum_eq_sum_of_fintype,
      ← sum_sigma', ← φ_bij.sum_comp]
  -- The right side is a sum over the pairs `(A, B)`; compare the terms of one pair.
  rw [h_lhs, sum_blockAverage_mul_blockAverage_eq, sum_sigma, Finset.sum_div]
  congr with ⟨⟨A, hA⟩, ⟨B, hB⟩⟩
  -- The number of all `x` is that of the `y` times that of the classes `s`.
  have h_card : Fintype.card (W →ₗ[k] V) =
      Fintype.card (B.compatibleMaps A) * Fintype.card ((W →ₗ[k] V) ⧸ B.compatibleMaps A) := by
    simpa using (B.compatibleMaps A).card_eq_card_quotient_mul_card
  simp_rw [S, h_card, ← card_prod, ← finMean_eq]
  -- So both sides are averages. The term at `(y, s)` depends only on the maps `B → A` and
  -- `W ⧸ B → V ⧸ A` that `y` induces, and every pair of such maps occurs.
  let induced :
      B.compatibleMaps A × (_ ⧸ B.compatibleMaps A) →+ (B →ₗ[k] A) × (_ ⧸ B →ₗ[k] _ ⧸ A) :=
    -- (`clear * -` keeps `aesop` fast: the context here is large.)
    .mk' (fun (⟨y, hy⟩, _) ↦ (y.restrict fun w hw ↦ hy hw, B.mapQ A y fun w hw ↦ hy hw))
      (by clear * -; aesop)
  have induced_surj : Function.Surjective induced := fun ⟨α, β⟩ ↦
    have ⟨y, hy, hα, hβ⟩ := exists_restrict_eq_and_mapQ_eq α β
    ⟨(⟨y, hy⟩, 0), Prod.ext hα hβ⟩
  refine (congrArg finMean (funext fun _ ↦ ?_)).trans (finMean_comp_surjective _ induced_surj _)
  -- The shear is bijective, so it identifies the maps on `U` and on the quotient by `U` with those
  -- for `B × A`; these are block maps on `B × A` and on the product of the quotients.
  rw [simClassOf_endOnSub_comap, simClassOf_endOnQuot_comap,
      simClassOf_endOnSub (B.subtype.prodMap A.subtype),
      simClassOf_endOnQuot (B.mkQ.prodMap A.mkQ)] <;>
    simp [induced, endOnSub, endOnQuot, ← ker_eq_bot, ← range_eq_top]

/-- If the class `o` has dimension `0`, the block average of `F` at `(o, a)` and at `(a, o)` is
`F a`. -/
lemma blockAverage_of_dim_eq_zero {o : SimClass k} (h_dim : o.dim = 0) (a : SimClass k) :
    F.blockAverage o a = F a ∧ F.blockAverage a o = F a := by
  -- With one block of dimension zero, each block map is similar to the other diagonal block.
  have h_empty : IsEmpty (Fin o.out.1) := (Fin.cast h_dim).isEmpty
  have h_left (x : (Fin a.out.1 → k) →ₗ[k] Fin o.out.1 → k) :
      simClassOf (blockTriangularEnd o.out.2 a.out.2 x) = simClassOf a.out.2 :=
    simClassOf_eq_of_equiv .prodUnique (by simp)
  have h_right (x : (Fin o.out.1 → k) →ₗ[k] Fin a.out.1 → k) :
      simClassOf (blockTriangularEnd a.out.2 o.out.2 x) = simClassOf a.out.2 :=
    simClassOf_eq_of_equiv .uniqueProd (by simp [Subsingleton.elim x 0])
  simp [blockAverage, h_left, h_right]

omit [Finite k] in
/-- For an `a`-stable subspace `U`, the characteristic polynomial of `a` is the product of those of
its restriction to `U` and of the induced map on `V ⧸ U`. -/
lemma charpoly_endOnSub_mul_endOnQuot (U : StableSubspace a) :
    U.endOnSub.charpoly * U.endOnQuot.charpoly = a.charpoly := by
  -- In a basis of `V` made of a basis of `U` and lifts of a basis of `V ⧸ U`, the matrix of `a`
  -- is block upper triangular, with the matrices of `U.endOnSub` and `U.endOnQuot` on the diagonal.
  let bU := chooseBasis k U.val
  let bQ := chooseBasis k (V ⧸ U.val)
  let M := toMatrix (bU.sumQuot bQ) (bU.sumQuot bQ) a
  have h_block :
      M = .fromBlocks (toMatrix bU bU U.endOnSub) M.toBlocks₁₂ 0 (toMatrix bQ bQ U.endOnQuot) := by
    -- For the lower right block, `bQ j` is the class of the lifted basis vector. (Without
    -- `-Basis.sumQuot_inr` the reversed rewrite loops.)
    ext (i | i) (j | j) <;>
      simp [M, U.property, endOnSub, restrict_apply, (mk_eq_zero _).2, Matrix.toBlocks₁₂, endOnQuot,
        ← Basis.sumQuot_inr bU bQ, -Basis.sumQuot_inr, toMatrix_apply]
  have h_charpoly : a.charpoly = M.charpoly := (charpoly_toMatrix a _).symm
  rw [h_charpoly, h_block, Matrix.charpoly_fromBlocks_zero₂₁, charpoly_toMatrix, charpoly_toMatrix]

end MackeyFormula

/-!
## Block averages as adjoint of the induction product

* `New.Hall.rankInner_eq_classInner_simClassOf`, `New.Hall.classInner_evalGL`: inner products over
  the automorphisms of any `V`, or over `GL ι k`, depend only on the dimension.
-/

section InductionMean

open Module Pointwise LinearMap GeneralLinearGroup StableSubspace Submodule Finset MulAction

attribute [local instance low] Fintype.ofFinite

variable {k V ι : Type*} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  {F H : Hall k} {a : End k V} (n : ℕ) (X A B : Hall k) [Fintype ι]

omit [Finite k] in
/-- The chosen representative of the class of `a` is the identity if and only if `a` is. -/
lemma simClassOf_out_eq_one_iff :
    (∀ x : Fin (Quot.out (simClassOf a)).fst → k, (simClassOf a).out.2 x = x) ↔ a = 1 := by
  obtain ⟨e, he⟩ := exists_equiv_simClassOf_out a
  simp [e.surjective.forall, ← he, LinearMap.ext_iff]

/-- The pairing `New.Hall.rankInner` in rank `dim V` is the mean over the automorphisms of `V`. -/
lemma rankInner_eq_classInner_simClassOf :
    rankInner (finrank k V) F H =
      classInner (fun g : (End k V)ˣ ↦ F (simClassOf g.val)) fun g : (End k V)ˣ ↦
        H (simClassOf g.val) := by
  -- Conjugate by the coordinates of a basis of `V`; this is how `simClassOf` is defined.
  refine finMean_equiv (congrLinearEquiv (finBasis k V).equivFun).toEquiv fun g ↦ ?_
  congr!
  all_goals exact (Quot.sound ⟨_, rfl⟩).symm

/-- For class functions F, H on matrices over the finite field k, the average over GL_ι(k) of
conj F(g) · H(g) is the inner product `New.Hall.rankInner` of F and H in rank |ι|. -/
lemma classInner_evalGL [DecidableEq ι] :
    classInner (G := GL ι k) F.evalGL H.evalGL = rankInner (Fintype.card ι) F H := by
  simp_rw [← finrank_pi k, rankInner_eq_classInner_simClassOf, classInner,
    finMean_equiv Matrix.GeneralLinearGroup.toLin.toEquiv]
  rfl

/-- `Hall k` is the space of complex functions on similarity classes of matrices over the finite
field k, with product given by parabolic induction. In it, `rankInner n (A * B) X`, the
GL_n(k)-average of conj(A * B)·X, equals ∑_{p+q=n} `rankInner p A (skew q B X)`. Here `skew q B X`
sends a class a to the GL_q(k)-average over b of conj B(b) times the block average of X at (a,
b). -/
lemma rankInner_mul_eq_sum_skew :
    rankInner n (A * B) X =
      ∑ p ∈ HasAntidiagonal.antidiagonal n, rankInner p.1 A (skew p.2 B X) := by
  -- Expand `A * B` as a sum over pairs `(g, U)`, `U` a `g`-stable subspace, and sum first over `g`
  -- in the stabiliser of `U`, which is the group of block triangular matrices for `U ⊕ Z`.
  let d (U : Submodule k (Fin n → k)) : ℕ := finrank k U
  have smul_eq (g : (End k (Fin n → k))ˣ) {U Y : Submodule k (Fin n → k)} (h : ∀ x ∈ U, g.val x ∈ Y)
      (hd : d Y = d U) : g • U = Y :=
    eq_of_le_of_finrank_eq (map_le_iff_le_comap.2 h)
      (((toLinearEquiv g).finrank_map_eq U).trans hd.symm)
  -- A sum over dimensions `p ≤ n` is a sum over subspaces, each weighted by `1 / #{dim = p}`.
  have image_d : Finset.range (n + 1) = univ.image d := by
    refine Subset.antisymm (fun p hp ↦ ?_) (by simp [subset_iff, (finrank_le _).trans, d])
    obtain ⟨f, hf⟩ : ∃ f : (Fin p → k) →ₗ[k] Fin n → k, Function.Injective f :=
      finrank_le_iff_exists_linearMap.1 (by simpa [Nat.lt_succ_iff] using hp)
    exact mem_image.2 ⟨_, mem_univ _, (finrank_range_of_inj hf).trans (finrank_fin_fun k)⟩
  have sum_dim (M : ℕ → ℂ) : ∑ p ∈ .range (n + 1), M p = ∑ U, M (d U) / #{Y | d Y = d U} := by
    rw [sum_comp (fun p ↦ M p / (#{Y | d Y = p} : ℂ)) d]
    exact sum_congr image_d (by simp [field])
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk, rankInner, finMean_eq, sum_dim]
  -- Expanding the product, the left side is a sum over the pairs `(g, U)`.
  suffices h_pairs : (∑ x : Σ g : (End k (Fin n → k))ˣ, StableSubspace g.val,
        starRingEnd ℂ (A (simClassOf x.2.endOnSub)) * starRingEnd ℂ (B (simClassOf x.2.endOnQuot)) *
          X (simClassOf x.1.val)) / (Fintype.card (End k (Fin n → k))ˣ : ℂ) =
      ∑ U, rankInner (d U) A (skew (n - d U) B X) / (#{Y | d Y = d U} : ℂ) by
    simpa [mul_simClassOf, sum_mul, sum_sigma', finsum_eq_sum_of_fintype] using h_pairs
  -- Reindex the pairs `(g, U)` by `U` first, then `g` in its stabiliser.
  let pairs : (Σ U : Submodule k (Fin n → k), stabilizer (End k (Fin n → k))ˣ U) ≃
      Σ g : (End k (Fin n → k))ˣ, StableSubspace g.val :=
    { toFun x := ⟨x.snd, x.fst, map_le_iff_le_comap.1 x.snd.property.le⟩
      invFun y := ⟨y.snd.val, y.fst, smul_eq y.fst y.snd.property rfl⟩ }
  rw [← pairs.sum_comp, Fintype.sum_sigma, sum_div]
  congr with U
  -- The orbit of `U` consists of the subspaces of the same dimension.
  have mem_orbit (Y : Submodule k (Fin n → k)) : d Y = d U ↔ Y ∈ orbit (End k (Fin n → k))ˣ U := by
    refine ⟨fun hY ↦ ?_, ?_⟩
    · obtain ⟨g, hg⟩ := exists_linearEquiv_restrict_eq (.ofFinrankEq U Y hY.symm)
      exact ⟨ofLinearEquiv g, smul_eq _ (fun x hx ↦ by simp [← hg ⟨x, hx⟩]) hY⟩
    · rintro ⟨g, rfl⟩
      exact (toLinearEquiv g).finrank_map_eq U
  -- The stabiliser of `U` is parametrised by the three blocks.
  obtain ⟨Z, hZ⟩ : ∃ Z, IsCompl U Z := U.exists_isCompl
  let e : (Z × U) ≃ₗ[k] Fin n → k := Z.prodEquivOfIsCompl U hZ.symm
  -- The automorphism of `Z × U` with diagonal blocks `b`, `a` and off-diagonal block `x`, carried
  -- to `Fin n → k` by `e`, maps `U` into `U`; an element of the stabiliser maps `U` onto `U`.
  have skewProd_mem (a : (End k U)ˣ) (b : (End k Z)ˣ) (x : Z →ₗ[k] U) (u : U) :
      (congrLinearEquiv e (ofLinearEquiv (.skewProd (toLinearEquiv b) (toLinearEquiv a) x)) :
        End k (Fin n → k)) u ∈ U := by
    simp [e]
  have map_eq (g : (End k (Fin n → k))ˣ) (hg : g ∈ stabilizer (End k (Fin n → k))ˣ U) :
      U.map (toLinearEquiv g : (Fin n → k) →ₗ[k] Fin n → k) = U := hg
  let blocks : (End k U)ˣ × (End k Z)ˣ × (Z →ₗ[k] U) ≃ stabilizer (End k (Fin n → k))ˣ U :=
    { toFun := fun (a, b, x) ↦
        ⟨congrLinearEquiv e (ofLinearEquiv (.skewProd (toLinearEquiv b) (toLinearEquiv a) x)),
          smul_eq _ (fun u hu ↦ skewProd_mem a b x ⟨u, hu⟩) rfl⟩
      invFun := fun ⟨g, hg⟩ ↦
        (ofLinearEquiv ((toLinearEquiv g).ofSubmodules U U (map_eq g hg)),
          congrLinearEquiv (U.quotientEquivOfIsCompl Z hZ)
            (ofLinearEquiv (Quotient.equiv U U (toLinearEquiv g) (map_eq g hg))),
          U.projectionOnto Z hZ ∘ₗ domRestrict g Z)
      left_inv _ := by ext <;> simp [e]
      right_inv _ := by
        ext : 2
        simp [e, LinearMap.ext_iff]
        grind [projection_add_projection_eq_self] }
  -- Orbit-stabiliser: the order of the group is `#{dim = d U}` times that of the stabiliser, so
  -- the term of `U` is the weight times an average over the stabiliser.
  rw [← card_orbit_mul_card_stabilizer_eq_card_group _ U,
    Fintype.card_of_subtype {Y | d Y = d U} fun Y ↦ (mem_filter_univ Y).trans (mem_orbit Y),
    Nat.cast_mul, div_mul_eq_div_div_swap, ← finMean_eq, finMean_equiv blocks fun _ ↦ rfl]
  -- For the element with blocks `a`, `b`, `x`, the restriction to `U` is `a`, the map on the
  -- quotient is similar to `b`, and the whole map to `blockTriangularEnd a b x`.
  have h_sub (a : (End k U)ˣ) (b : (End k Z)ˣ) (x : Z →ₗ[k] U) :
      simClassOf (pairs ⟨U, blocks (a, b, x)⟩).2.endOnSub = simClassOf a.val := by
    refine congrArg simClassOf (LinearMap.ext fun u ↦ Subtype.ext ?_)
    simp [pairs, blocks, ↓Equiv.coe_fn_mk, e, endOnSub]
  have h_quot (a : (End k U)ˣ) (b : (End k Z)ˣ) (x : Z →ₗ[k] U) :
      simClassOf (pairs ⟨U, blocks (a, b, x)⟩).2.endOnQuot = simClassOf b.val :=
    simClassOf_endOnQuot _ (by simp [pairs, blocks, ↓Equiv.coe_fn_mk, e]) _
      (projectionOnto_surjective hZ.symm) (by simp [pairs, ↓Equiv.coe_fn_mk])
  have h_whole (a : (End k U)ˣ) (b : (End k Z)ˣ) (x : Z →ₗ[k] U) :
      simClassOf (pairs ⟨U, blocks (a, b, x)⟩).1.1 = simClassOf (blockTriangularEnd a.1 b.1 x) :=
    simClassOf_eq_of_equiv e.symm (by simp [pairs, blocks, ↓Equiv.coe_fn_mk, add_comm])
  -- Both sides become means over `a`, `b`, `x`: `dim Z = n - dim U`, and `blockAverage_simClassOf`
  -- computes the block average on the representatives `a`, `b`.
  have dim_eq : n = finrank k Z + finrank k U := by simpa using e.finrank_eq.symm
  simp [h_sub, h_quot, h_whole, d, finMean_prod, rankInner_eq_classInner_simClassOf,
    blockAverage_simClassOf, skew, classInner, mul_assoc, ← finMean_const_mul, dim_eq]

end InductionMean

/-!
## Adjoint of multiplication by a class function

* `New.Hall.skew_of_isCuspidal`: for cuspidal `c` and `d ≠ 0`, `New.Hall.skew d f c` is the scalar
  `New.Hall.rankInner d f c` times the unit.
-/

section SkewOperator

open Module Finset

variable {k : Type*} [Field k] [Finite k]
  {F H c f : Hall k} {d n : ℕ} {o : SimClass k} (hc : c.IsCuspidal) (hd : d ≠ 0)

/-- Here `rankInner m F₁ F₂` is the average over g ∈ GL_m(k) of conj F₁(g)·F₂(g), and `skew d f F`
sends a class a to the average over b ∈ GL_d(k) of conj f(b) times the block average
(`New.Hall.blockAverage`) of `F` at (a, b). Adjunction: if `f` vanishes on the classes of dimension
other than `d`, then `rankInner (d + n) (f * H) F = rankInner n H (skew d f F)`, where `*` is the
parabolic induction product. -/
lemma rankInner_mul_eq_rankInner_skew (hf : ∀ c : SimClass k, c.dim ≠ d → f c = 0) :
    rankInner (d + n) (f * H) F = rankInner n H (skew d f F) := by
  -- In the expansion `rankInner_mul_eq_sum_skew` over the sizes (p, q) of the two diagonal blocks
  -- only (p, q) = (n, d) survives, as `f` vanishes off dimension `d`.
  rw [mul_comm, rankInner_mul_eq_sum_skew, sum_eq_single_of_mem (n, d) (by simp [add_comm])]
  intro p hp hne
  have h_size : p.2 ≠ d := by grind [HasAntidiagonal.mem_antidiagonal]
  simp [hf, h_size, rankInner, skew]

omit [Finite k] in
/-- The only class of dimension `0` is that of the zero map of the zero space. -/
lemma eq_simClassOf_zero_of_dim_eq_zero (h_dim : o.dim = 0) :
    o = simClassOf (0 : End k (Fin 0 → k)) := by
  -- Both spaces are zero, so any isomorphism intertwines the maps.
  rw [← simClassOf_out o]
  exact simClassOf_eq_of_equiv (.funCongrLeft k k (finCongr h_dim.symm)) (by subsingleton)

@[simp]
lemma mul_apply_of_dim_zero (h_dim : o.dim = 0) : (F * H) o = F o * H o := by
  -- In size zero an average has one term, so `rankInner_mul_eq_sum_skew` against `1` is the
  -- conjugate of the claim.
  simpa [eq_simClassOf_zero_of_dim_eq_zero, h_dim, rankInner, skew, blockAverage_of_dim_eq_zero]
    using
    star_inj.2 (rankInner_mul_eq_sum_skew 0 1 F H)

include hc hd

/-- For cuspidal `c` and `d ≠ 0`, the pairing with `c` in degree `d` satisfies the Leibniz rule, the
other factor being evaluated at the zero space (`New.Hall.rankInner 0`). -/
lemma rankInner_mul_of_isCuspidal :
    rankInner d c (F * H) =
      rankInner d c F * rankInner 0 constOne H + rankInner 0 constOne F * rankInner d c H := by
  classical
  -- Expand the conjugate pairing by `rankInner_mul_eq_sum_skew`. As `c` is cuspidal, only the block
  -- sizes (d, 0) and (0, d) contribute.
  have h_sum : rankInner d (F * H) c = rankInner d F (skew 0 H c) + rankInner 0 F (skew d H c) := by
    rw [rankInner_mul_eq_sum_skew, sum_eq_add (d, 0) (0, d) (by simp [hd]) _ (by simp) (by simp)]
    rintro ⟨p, q⟩ h_mem ⟨h_ne_d0, h_ne_0d⟩
    -- any other pair of sizes has both positive, and there `blockAverage` of `c` vanishes
    have h_add : p + q = d := HasAntidiagonal.mem_antidiagonal.1 h_mem
    have hp : p ≠ 0 := by grind
    have hq : q ≠ 0 := by grind
    have h_cusp : ∀ a b : SimClass k, a.dim ≠ 0 → b.dim ≠ 0 → c.blockAverage a b = 0 := hc
    simp [rankInner, skew, h_cusp, hp, hq]
  -- Conjugate; in these two terms `blockAverage` of `c` is `c` at the block of size `d`
  -- (`blockAverage_of_dim_eq_zero`).
  replace h_sum := congrArg star h_sum
  simp_all [← finMean_conj, mul_comm, IsCuspidal, rankInner, skew, blockAverage_of_dim_eq_zero]
  -- what is left is to pull the constant `rankInner 0 constOne H` out of an average
  simp [finMean_eq, sum_mul, field, mul_assoc]

/-- Take `c` cuspidal in the sense of `New.Hall.IsCuspidal` and `d ≠ 0`. Let `skew d f c` be the
function x ↦ average over y in GL_d(k) of conj f(y) · δc(x, y), with δ the block average
`New.Hall.blockAverage`. Then `skew d f c` equals the unit `1` of the Hall algebra times
`rankInner d f c`, the average over GL_d(k) of conj f · c. -/
lemma skew_of_isCuspidal : skew d f c = rankInner d f c • 1 := by
  funext o
  by_cases h_o : o.dim = 0
  · -- At a class of dimension zero `blockAverage` of `c` is `c` itself.
    have h_avg : c.blockAverage o = c := funext fun a ↦ (blockAverage_of_dim_eq_zero c h_o a).1
    simp [skew, h_avg, h_o]
  · -- At any other class it vanishes on blocks of size `d ≠ 0`, as `c` is cuspidal.
    have h_avg (g : (End k (Fin d → k))ˣ) : c.blockAverage o (simClassOf g.val) = 0 :=
      hc o _ h_o (by simpa using hd)
    simp [skew, rankInner, h_avg, h_o]

/-- `skew d c` is the map sending `F` to the function x ↦ average over y in GL_d(k) of conj
c(y) · δF(x, y), with δ the block average `New.Hall.blockAverage`. For `c` cuspidal in the sense of
`New.Hall.IsCuspidal` and `d ≠ 0`, this map is a derivation of the Hall algebra:
`skew d c (F * H) = skew d c F * H + F * skew d c H`.

This is the derivation property of the adjoint of multiplication by a cuspidal element, from
Zelevinsky's PSH-algebra structure on class functions of finite general linear groups; only the
Leibniz rule is stated. -/
lemma skew_mul : skew d c (F * H) = skew d c F * H + F * skew d c H := by
  -- At an endomorphism `g` both sides are sums over the `g`-stable subspaces `W`: the left by
  -- `blockAverage_mul`, the right by the definition of the product (`mul_simClassOf`).
  ext _ g
  simp only [skew, rankInner, add_apply, mul_simClassOf, finsum_eq_sum_of_fintype,
    ← sum_add_distrib]
  simp only [blockAverage_mul, mul_sum, finMean_sum]
  -- The terms at `W` agree by `rankInner_mul_of_isCuspidal` for
  -- `F.blockAverage (simClassOf W.endOnSub)` and `H.blockAverage (simClassOf W.endOnQuot)`, whose
  -- values at the zero space are `F (simClassOf W.endOnSub)` and `H (simClassOf W.endOnQuot)`.
  refine sum_congr rfl fun W _ ↦ (rankInner_mul_of_isCuspidal hc hd).trans ?_
  simp [rankInner, blockAverage_of_dim_eq_zero]

end SkewOperator

end New.Hall

/-!
## Frobenius reciprocity along parabolic subgroups

The proof removes the largest level and uses the adjunction
`New.Hall.rankInner_mul_eq_rankInner_skew`.
-/

namespace New

open Matrix Function Hall GeneralLinearGroup Finset Fintype Equiv

variable {k m n ι : Type*} [Field k] [Fintype m] [Fintype n] [DecidableEq n]
  [LinearOrder ι] (b : n → ι) (F : ι → Hall k)

/-- Reindexing the rows and columns of a matrix by one bijection does not change its similarity
class. -/
lemma simClassOf_submatrix [DecidableEq m] (e : m ≃ n) (M : Matrix n n k) :
    simClassOf (M.submatrix e e).toLin' = simClassOf M.toLin' :=
  simClassOf_eq_of_equiv (.funCongrLeft k k e.symm) (by simp [funext_iff])

/-- A function on `GL n k` that is invariant under conjugation is the restriction of a function on
similarity classes. -/
lemma exists_eq_evalGL {Y : GL n k → ℂ} (h_conj : IsClassFunction Y) :
    ∃ X : Hall k, Y = Hall.evalGL X := by
  -- Matrices in the same similarity class are conjugate, by the matrix of the intertwiner `e`.
  refine (factorsThrough_iff Y).1 fun g l h_cls ↦ ?_
  obtain ⟨e, he⟩ := simClassOf_eq_iff.1 h_cls.symm
  have h_g : g = toLin.symm (.ofLinearEquiv e) * l * (toLin.symm (.ofLinearEquiv e))⁻¹ := by
    simp_all [← toLin.injective.eq_iff, eq_mul_inv_iff_mul_eq, Units.ext_iff, DFunLike.ext_iff]
  rw [h_g, h_conj l]

/-- **Frobenius reciprocity.** Let `k` be a finite field. Each `F a` is a complex function on
similarity classes of square matrices over `k` of all sizes, in `Hall k`, whose product is parabolic
induction. Let `s` contain all levels `b i` and let `Y` be a class function on `GL n k`. Restrict
each `F a`, `a ∈ s`, to classes of the size of the block of level `a`, and take the product. The
mean over `GL n k` of conj of this product times `Y` equals the mean over block upper triangular `g`
of `conj (∏ a ∈ s, F a (g_a)) * Y g`. Here `g_a` is the diagonal block of level `a`. -/
lemma classInner_evalGL_prod [Finite k] {s : Finset ι} (hs : ∀ i : n, b i ∈ s) (Y : GL n k → ℂ)
    (hY : IsClassFunction Y) :
    classInner (∏ a ∈ s, (F a).rankPart (Fintype.card {i // b i = a})).evalGL Y =
      classInner (∏ a ∈ s, (F a).evalGL ∘ blockHom b a) fun g : parabolic (R := k) b ↦ Y g.val := by
  obtain ⟨X, rfl⟩ := exists_eq_evalGL hY
  clear hY
  -- Induction on the set of levels, removing the largest level `m`.
  induction s using induction_on_max generalizing n X with
  | empty => simp_all [← isEmpty_iff, classInner, Hall.evalGL, eq_simClassOf_zero_of_dim_eq_zero]
  | insert m s hm ih => ?_
  -- With the indices of level `m` put first by `e`, the matrix `M g` of an element of `parabolic b`
  -- has a zero upper right block and invertible diagonal blocks.
  let e := sumCompl (b · = m)
  let M (g : parabolic (R := k) b) := g.val.val.submatrix e e
  have h_zero (g : parabolic (R := k) b) : (M g).toBlocks₁₂ = 0 :=
    ext fun _ _ ↦ g.property (by grind [sumCompl_apply_inl, sumCompl_apply_inr])
  have h_blocks (g : parabolic (R := k) b) :
      fromBlocks (M g).toBlocks₁₁ 0 (M g).toBlocks₂₁ (M g).toBlocks₂₂ =
        g.val.val.submatrix e e := by
    rw [← h_zero g, fromBlocks_toBlocks]
  have h_unit (g : parabolic (R := k) b) : IsUnit (M g).toBlocks₁₁ ∧ IsUnit (M g).toBlocks₂₂ := by
    have h_M_unit :
        IsUnit (fromBlocks (M g).toBlocks₁₁ 0 (M g).toBlocks₂₁ (M g).toBlocks₂₂) := by
      simp [h_blocks g]
    exact isUnit_fromBlocks_zero₁₂.1 h_M_unit
  -- Move the factor of level `m` to the other side (`rankInner_mul_eq_rankInner_skew`) and apply
  -- the induction hypothesis to the indices of the other levels.
  let b' (i : {i // ¬b i = m}) := b i
  have h_card (a : ι) (ha : a ∈ s) : card {i // b i = a} = card {i // b' i = a} :=
    card_congr (subtypeSubtypeEquivSubtype (q := (b · = a)) (by grind)).symm
  have h_prod : ∏ a ∈ s, (F a).rankPart (card {i // b i = a}) =
      ∏ a ∈ s, (F a).rankPart (card {i // b' i = a}) :=
    prod_congr rfl fun a ha ↦ by rw [h_card a ha]
  have hs' (i : {i // ¬b i = m}) : b' i ∈ s := by grind
  have h_notMem : m ∉ s := by grind
  rw [classInner_evalGL, prod_insert h_notMem, ← card_congr e, card_sum,
    rankInner_mul_eq_rankInner_skew (by grind [rankPart]), ← classInner_evalGL, h_prod, ih b' hs']
  simp [skew, ← classInner_evalGL, classInner, blockAverage_simClassOf, ← finMean_const_mul,
    ← finMean_prod (Prod.rec _), Hall.evalGL]
  -- A matrix with invertible diagonal blocks and a zero upper right block is invertible, and it is
  -- block triangular for the levels `b` when its block of the levels in `s` is so for `b'`.
  have h_unit_inv (t : parabolic (R := k) b' × GL {i // b i = m} k ×
      (({i // b i = m} → k) →ₗ[k] {i // ¬b i = m} → k)) :
      IsUnit (reindex e e (fromBlocks t.2.1 0 t.2.2.toMatrix' t.1.val)) := by
    simp
  have h_tri_inv (t : parabolic (R := k) b' × GL {i // b i = m} k ×
      (({i // b i = m} → k) →ₗ[k] {i // ¬b i = m} → k)) :
      BlockTriangular (fromBlocks t.2.1 0 t.2.2.toMatrix' t.1.val) (b ∘ e) := by
    have h_tri : BlockTriangular t.1.val.val b' := t.1.property
    simp [e, BlockTriangular]
    grind [BlockTriangular]
  -- The left side is now a mean over the two diagonal blocks and the lower left block, which
  -- parametrise `parabolic b`.
  let blocks : parabolic (R := k) b ≃ parabolic (R := k) b' ×
      GL {i // b i = m} k × (({i // b i = m} → k) →ₗ[k] {i // ¬b i = m} → k) :=
    { toFun g := (⟨(h_unit g).2.unit, g.2.submatrix⟩, (h_unit g).1.unit, (M g).toBlocks₂₁.toLin')
      invFun t := ⟨(h_unit_inv t).unit, blockTriangular_reindex_iff.2 (h_tri_inv t)⟩
      left_inv := by aesop_cat
      right_inv := by aesop_cat }
  apply finMean_equiv blocks
  simp_intro g [blocks, ← mul_assoc, h_notMem]
  rw [mul_comm (∏ x ∈ s, _)]
  symm
  congr!
  · -- The blocks of the levels in `s` agree up to a bijection of their index sets.
    exact (simClassOf_submatrix (subtypeSubtypeEquivSubtype (by grind)) _).symm
  -- The matrix `g` is similar to the block triangular matrix of its blocks.
  rw [← simClassOf_submatrix e, ← h_blocks, simClassOf_eq_iff]
  use LinearEquiv.sumArrowLequivProdArrow _ _ k k
  simp [fromBlocks_mulVec]
  -- both sides are the pair of the two parts of `x`
  exact fun x ↦ rfl

end New

end
end
end

/-!
# Cuspidal class functions on GL_n over a finite field: μ, supports, values, inner products

Let `k` be a finite field. `New.Hall k` is the ring of functions on the similarity classes
`New.SimClass k` of endomorphisms over `k`, with the parabolic induction product. In it,
𝟙 = `New.Hall.constOne` is the constant function 1, μ = `New.Hall.moebius` is its inverse, and
C_η = `New.Hall.greenCuspidal k η`. The file proves that C_η is cuspidal and that cuspidal functions
vanish off classes whose characteristic polynomial is a power of an irreducible polynomial. It
computes μ and C_η at multiplication by a field generator, and writes the inner product of C_η with
B·μ as a mean over the units of a field extension.

## Main definitions and results

* `New.Hall.crapo_complementation`, `New.Hall.isSemisimple_of_moebius_ne_zero`: μ is a Möbius
  function on the lattice of stable subspaces, so it vanishes off semisimple classes.
* `New.Hall.greenCuspidal_mul_constOne`, `New.Hall.isCuspidal_greenCuspidal`: C_η ∗ 𝟙 = −β_η, and
  C_η is cuspidal.
* `New.Hall.IsCuspidal.exists_charpoly_eq_pow`: a cuspidal function vanishes at the class of `g`
  unless the characteristic polynomial of `g` is a power of an irreducible one.
* `New.greenCuspidal_simClassOf_eq_mul`: the value of `New.Hall.greenCuspidal k η` at the class of
  `g` depends on `η` only at the elements whose Frobenius orbit gives all eigenvalues of `g`.
* `New.rankInner_greenCuspidal_mulMoebius`: the inner product on GL_{[L:k]}(k) of C_η
  (`New.Hall.greenCuspidal`) with B·μ (`New.Hall.mulMoebius`) is the mean over z ∈ L^× of conj η(φz)
  times B at multiplication by z.

Notions from other files:
* `New.Hall.IsCuspidal`: F is cuspidal when its average over block triangular endomorphisms with
  diagonal blocks a, b vanishes whenever both a and b have nonzero dimension.
* `New.Hall.brauerLift`: The class function β_η sending an endomorphism to the sum of η over the
  roots in K of its characteristic polynomial, counted with multiplicity.
* `New.Hall.greenCuspidal`: The class function C_η = (β_η·μ) ∗ 𝟙: the pointwise product of the
  eigenvalue sum β_η with the inverse μ of 𝟙, multiplied in the induction product by the constant
  function 𝟙.

## Relation to the literature

Known result: Brauer lift is a virtual character; cuspidal times Steinberg is induced from a torus.
Brauer induction is not used here. The character induced from the Coxeter torus is instead divided
by the Steinberg character, read as a Möbius function on semisimple classes compatibly with the
Galois action, and only the vanishing half of Crapo's theorem is used. Source: Green 1955, Thm 1; T.
A. Springer, Sém. Bourbaki 441 (1973/74), 1.1-1.7; R. Carter, Finite groups of Lie type (1985), for
Steinberg times a torus character; P. Hall's lemma, D. Krasula, arXiv 2403.05656, Lemma 23, and H.
Crapo's complementation theorem, for the vanishing of the Möbius number off semisimple modules.

See also `Lib.LocalGL.Green.TauFunctions`.
-/

@[expose] public section

/-! ## Crapo's lemma, the inverse μ of 𝟙, and cuspidality of C_η -/

namespace New.Hall

open Module Finset StableSubspace Submodule LinearMap ComplexConjugate End Polynomial

open scoped Classical in
/-- The corollary to Theorem 3 of H. H. Crapo, *The Möbius function of a lattice*, specialized
to a finite modular lattice. The sum condition makes `μ X` equal to `μ ⊥` times the Möbius
function of the interval `[⊥, X]`. If `μ ⊤ ≠ 0`, every element has a complement. -/
lemma crapo_complementation {L : Type*} [Lattice L] [BoundedOrder L] [IsModularLattice L]
    [Fintype L] {μ : L → ℂ} (h_sum : ∀ X ≠ ⊥, ∑ U : L with U ≤ X, μ U = 0) (h_ne : μ ⊤ ≠ 0)
    (W : L) : IsComplemented W := by
  -- Take `C` maximal among the elements disjoint from `W`; we show that `W ⊔ C = ⊤`.
  obtain ⟨C, hC, h_max⟩ : ∃ C : L, Maximal (Disjoint W) C :=
    exists_maximal_of_wellFoundedGT (Disjoint W) ⟨⊥, disjoint_bot_right⟩
  refine ⟨C, hC, codisjoint_iff_le_sup.mpr ?_⟩
  by_contra h_top
  apply h_ne
  -- By induction on `U`, `μ U = 0` unless `U ≤ W ⊔ C`.
  suffices h_vanish : ∀ U : L, ¬U ≤ W ⊔ C → μ U = 0 from h_vanish ⊤ h_top
  intro U hU
  induction U using WellFoundedLT.induction with | ind U ih => ?_
  -- If `U ⊓ (W ⊔ C) = ⊥` then `W` is disjoint from `C ⊔ U` (modularity), so `U ≤ C` by maximality.
  have meet_ne : U ⊓ (W ⊔ C) ≠ ⊥ := by
    grind [disjoint_iff, le_sup_left, le_sup_right,
      hC.disjoint_sup_right_of_disjoint_sup_left (c := U)]
  -- The sums of `μ` below `U` and below `U ⊓ (W ⊔ C)` vanish; by `ih` their difference is `μ U`.
  have h_sub : ({A | A ≤ U ⊓ (W ⊔ C)} : Finset L) ⊆ ({A | A ≤ U} : Finset L) := by
    grind [le_inf_iff]
  rw [← h_sum U (ne_bot_of_le_ne_bot meet_ne inf_le_left), ← sum_sdiff h_sub, h_sum _ meet_ne,
    sum_eq_single U]
  · rw [add_zero]
  · -- an `A < U` outside `U ⊓ (W ⊔ C)` is not below `W ⊔ C`, so `μ A = 0` by `ih`
    grind [Ne.lt_of_le, le_inf_iff]
  · -- `U` itself lies in the difference, as `¬U ≤ W ⊔ C`
    grind [le_inf_iff]

variable {k V K : Type*} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  {g : End k V} {o : SimClass k} (B : Hall k) [Field K] [Algebra k K] (η : K → ℂ)

/-! ### The inverse of the constant function -/

/-- `μ` is inverse to `New.Hall.constOne`; at `g` this reads: the sum of `μ (g|W)` over the stable
subspaces `W` is `1` in dimension `0` and `0` otherwise. -/
lemma moebius_mul_constOne : moebius * constOne = (1 : Hall k) := by grind [isUnit_constOne]

/-- At the class of `g`, the sum of `μ (g|W)` over the `g`-stable subspaces `W` is the value of the
unit `1` of `New.Hall k` at the class of `g`. -/
lemma sum_moebius_simClassOf_endOnSub :
    ∑ W : StableSubspace g, moebius (simClassOf W.endOnSub) = (1 : Hall k) (simClassOf g) := by
  rw [← moebius_mul_constOne]
  simp [mul_simClassOf, finsum_eq_sum_of_fintype]

/-- An endomorphism at whose class `μ` does not vanish is semisimple. -/
lemma isSemisimple_of_moebius_ne_zero (h_mu_ne : moebius (simClassOf g) ≠ 0) : g.IsSemisimple := by
  classical
  -- Apply `crapo_complementation` to the (modular, finite) lattice of `g`-stable subspaces, with
  -- the function `U ↦ μ (simClassOf (endOnSub U))`: every stable subspace has a stable complement.
  have h_modular : IsModularLattice g.invtSubmodule :=
    ⟨fun y ↦ sup_inf_le_assoc_of_le (y : Submodule k V)⟩
  let fintype_invt : Fintype g.invtSubmodule := fintypeStableSubspace
  refine isSemisimple_iff'.mpr
    (crapo_complementation (μ := fun U ↦ moebius (simClassOf (endOnSub U))) (fun X hX ↦ ?_) ?_)
  · -- The sum over `U ≤ X` is that of `sum_moebius_simClassOf_endOnSub` for `endOnSub X`, which is
    -- `0` for `X ≠ ⊥`; `sum_comap` matches the stable subspaces of `X` with the stable `U ≤ X`.
    have h_subtype : ∀ v : (X : Submodule k V),
        (X : Submodule k V).subtype (endOnSub X v) = g ((X : Submodule k V).subtype v) := by aesop
    have h_reindex (F : StableSubspace (endOnSub X) → ℂ) :
        ∑ W, F W = ∑ U : StableSubspace g, if (U : Submodule k V) ≤ X then
          F (comap (X : Submodule k V).subtype h_subtype U) else 0 := by
      simpa [sum_filter] using sum_comap (g := endOnSub X) (X : Submodule k V).subtype h_subtype F
    -- The sum of the statement, over `g.invtSubmodule`, is the same sum over `StableSubspace g`.
    change ∑ U ∈ univ.filter fun U : StableSubspace g ↦ U.val ≤ X.val,
      moebius (simClassOf U.endOnSub) = 0
    simpa +contextual [hX, h_reindex, sum_filter] using sum_moebius_simClassOf_endOnSub
      (g := endOnSub X)
  · -- The restriction of `g` to `⊤` is similar to `g`.
    have h_top : simClassOf (endOnSub (⊤ : g.invtSubmodule)) = simClassOf g :=
      simClassOf_eq_of_equiv topEquiv fun _ ↦ rfl
    rwa [h_top]

@[simp]
lemma moebius_eq_one_of_dim_eq_zero (h_dim : o.dim = 0) : moebius o = 1 := by
  simpa [h_dim] using congrFun (moebius_mul_constOne (k := k)) o

/-- Let μ (`moebius`) be the inverse of the constant class function 1 for the parabolic-induction
product on similarity classes over the finite field k. For any class function `B`, the average of
the pointwise product `B μ` over the block triangular endomorphisms with diagonal blocks `a`, `b` is
`μ a * μ b * B (b ⊕ a)`. Here `b ⊕ a` is the block diagonal map of the chosen representatives of `b`
and `a`. -/
@[simp↓]
lemma blockAverage_mulMoebius (a b : SimClass k) :
    B.mulMoebius.blockAverage a b =
      moebius a * moebius b * B (simClassOf (b.out.snd.prodMap a.out.snd)) := by
  -- First `δ moebius = moebius ⊗ moebius` for `δ = blockAverage`: cancel the unit `constOne` in
  -- each of the two variables. By the Mackey formula `blockAverage_mul` and `δ 𝟙 = 𝟙 ⊗ 𝟙`, the left
  -- side becomes `δ (moebius * 𝟙) = δ 1`; this and the right side `(moebius * 𝟙) ⊗ (moebius * 𝟙)`
  -- are `1 ⊗ 1`.
  have delta_eq : blockAverage moebius a = moebius a • moebius := by
    refine isUnit_constOne.mul_right_cancel (ext fun _ y ↦ ?_)
    let F : Hall k := fun c ↦ (blockAverage moebius c * constOne : Hall k) (simClassOf y)
    let F' : Hall k := fun c ↦ (moebius c • moebius * constOne : Hall k) (simClassOf y)
    suffices key : F * constOne = F' * constOne from
      congrFun (isUnit_constOne.mul_right_cancel key) a
    ext _ x
    have h_mackey : (moebius * constOne).blockAverage (simClassOf x) (simClassOf y) =
        ∑ A : StableSubspace x, (moebius.blockAverage (simClassOf A.endOnSub) *
          constOne.blockAverage (simClassOf A.endOnQuot)) (simClassOf y) :=
      blockAverage_mul moebius constOne x y
    simp_all [F, F', blockAverage_simClassOf, ite_and, ← mul_sum, mul_simClassOf,
      finsum_eq_sum_of_fintype, sum_moebius_simClassOf_endOnSub]
  -- So it suffices that `B` agrees at a block triangular map and at `b ⊕ a` whenever `moebius` does
  -- not vanish at the former.
  have h_mu_ab : moebius a * moebius b = moebius.blockAverage a b := by simp [delta_eq]
  rw [h_mu_ab, blockAverage, blockAverage, mul_comm, ← finMean_const_mul]
  congr! 2 with x
  simp only [mul_eq_mul_right_iff, or_iff_not_imp_right]
  intro h_ne
  -- Then that map, say `g`, is semisimple, so the second factor has a stable complement `C`.
  have h_inv_prod : (⊥ : Submodule k (Fin b.out.fst → k)).prod ⊤ ∈
      invtSubmodule (blockTriangularEnd a.out.snd b.out.snd x) := fun v ↦ by aesop
  obtain ⟨C, C_inv, hC⟩ : ∃ C : Submodule k ((Fin b.out.fst → k) × (Fin a.out.fst → k)),
      C ∈ invtSubmodule (blockTriangularEnd a.out.snd b.out.snd x) ∧
        IsCompl ((⊥ : Submodule k (Fin b.out.fst → k)).prod ⊤) C :=
    isSemisimple_iff.mp (isSemisimple_of_moebius_ne_zero h_ne) _ h_inv_prod
  -- As `C` is stable, the projection `p` onto `⊥ × ⊤` along `C` satisfies `p ∘ g ∘ p = p ∘ g`.
  have proj_comm :
      projection _ C hC ∘ₗ blockTriangularEnd a.out.snd b.out.snd x ∘ₗ projection _ C hC =
      projection _ C hC ∘ₗ blockTriangularEnd a.out.snd b.out.snd x :=
    (isIdempotentElem_projection hC).ker_mem_invtSubmodule_iff.mp (by simpa using C_inv)
  have proj_mem : ∀ v, projection _ C hC v ∈ (⊥ : Submodule k (Fin b.out.fst → k)).prod ⊤ :=
    projection_apply_mem hC
  -- The first coordinate, paired with the projection `p`, conjugates `g` to `b ⊕ a`.
  refine congrArg B (simClassOf_eq_of_equiv
    (.ofInjectiveEndo (.prod (fst k (Fin b.out.fst → k) (Fin a.out.fst → k))
      (snd k (Fin b.out.fst → k) (Fin a.out.fst → k) ∘ₗ projection _ _ hC)) ?_) ?_)
  · -- the map is injective
    simp_all [injective_iff_map_eq_zero, Prod.ext_iff, mem_prod, DFunLike.ext_iff,
      projection_apply_of_mem_left]
  · -- and it conjugates the block triangular map to `b ⊕ a`; `↓`: membership in `⊥.prod ⊤` has
    -- to be split before the other lemmas act
    simp_all [Prod.ext_iff, ↓mem_prod, DFunLike.ext_iff, projection_apply_of_mem_left]

/-- `μ` takes real values: each value is its own complex conjugate. -/
@[simp]
lemma conj_moebius : ∀ c : SimClass k, conj (moebius c) = moebius c := by
  -- The values of `constOne` and `1` are real, so `conj moebius` is an inverse of `constOne` as
  -- well.
  let μ' : Hall k := fun c ↦ conj (moebius c)
  have h_inv : μ' * constOne = moebius * constOne := ext fun _ y ↦ by
    simp [μ', ← map_sum, mul_simClassOf, finsum_eq_sum_of_fintype, sum_moebius_simClassOf_endOnSub]
  exact congrFun (isUnit_constOne.mul_right_cancel h_inv)

/-! ### The cuspidal function attached to `η` -/

/-- The induction product of `New.Hall.greenCuspidal k η` with the constant function
`New.Hall.constOne` is minus the eigenvalue sum `New.Hall.brauerLift k η`. -/
@[simp]
lemma greenCuspidal_mul_constOne : greenCuspidal k η * constOne = -brauerLift k η := by
  -- It suffices that `greenCuspidal k η = -(moebius * brauerLift k η)`; multiply by `constOne`.
  suffices greenCuspidal k η + moebius * brauerLift k η = 0 by grind [moebius_mul_constOne]
  ext _ g
  -- `β = brauerLift k η` is additive, `β (g|W) + β (g|V/W) = β g`, so the sum factors as
  -- `β g * ∑ W, moebius (g|W) = 0`.
  trans brauerLift k η (simClassOf g) * ∑ W : StableSubspace g, moebius (simClassOf W.endOnSub)
  · simp [← sum_add_distrib, mul_sum, greenCuspidal, mul_simClassOf, finsum_eq_sum_of_fintype]
    refine sum_congr rfl fun W _ ↦ ?_
    simp [← charpoly_endOnSub_mul_endOnQuot _ W, field, charpoly_monic, Monic.ne_zero, aroots_mul]
  · simp +contextual [← g.charpoly_natDegree, sum_moebius_simClassOf_endOnSub, charpoly_monic]

/-- The value of `New.Hall.greenCuspidal k η` in dimension zero is zero. -/
lemma greenCuspidal_eq_zero_of_dim_lt_one (c : SimClass k) :
    c.dim < 1 → greenCuspidal k η c = 0 := by
      simp_all [eq_simClassOf_zero_of_dim_eq_zero, greenCuspidal]

/-- `New.Hall.greenCuspidal k η` is cuspidal: its block averages vanish when both blocks have
positive size. -/
lemma isCuspidal_greenCuspidal : (greenCuspidal k η).IsCuspidal := by
  intro a b ha hb
  -- Write `δ = blockAverage`, `β = brauerLift k η`. By the Mackey formula `blockAverage_mul`,
  -- `δ C_η = δ (β moebius) * δ 𝟙`, a sum over stable subspaces of `a` and of `b`.
  rw [← simClassOf_out a, ← simClassOf_out b, greenCuspidal, blockAverage_mul]
  -- By `blockAverage_mulMoebius` and additivity of `β`,
  -- `δ (β moebius) = β moebius ⊗ moebius + moebius ⊗ β moebius`. Each of the two parts has a factor
  -- `∑ W, moebius (c|W) = 1 c` with `c = a` or `c = b`, which is `0` as `c.dim ≠ 0`.
  -- `-simClassOf_out`: otherwise `simp` undoes the first rewrite, which wrote `a`, `b` as classes
  simp_all [blockAverage, -simClassOf_out, charpoly_prodMap, mul_add, ← mul_sum, ← sum_mul,
    mul_assoc, mul_simClassOf, finsum_eq_sum_of_fintype, charpoly_monic, Monic.ne_zero,
    aroots_mul, sum_add_distrib, sum_moebius_simClassOf_endOnSub]

end New.Hall

namespace New

/-!
## Supports of cuspidal class functions

Idea: the Fitting decomposition for an irreducible factor of the characteristic polynomial makes all
block triangular maps with the two given diagonal blocks similar.
-/

section CuspidalSupport

open Polynomial Hall LinearMap Module Multiset Submodule StableSubspace

variable {k K V : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
  (η η' : K → ℂ) [AddCommGroup V] [Module k V] [Module.Finite k V] {g : End k V}

omit [Finite k] in
/-- If `P(g)` is nilpotent, with `P` monic irreducible, the characteristic polynomial of `g` is a
power of `P`. -/
lemma charpoly_eq_pow_of_isNilpotent {P : k[X]} (hP_irred : Irreducible P) (hP_monic : Monic P)
    (h_nilp : IsNilpotent (aeval g P)) :
    charpoly g = P ^ (finrank k V / P.natDegree) := by
  -- `charpoly g` divides `(charpoly P(g)).comp P`, and `charpoly P(g) = X ^ finrank k V`
  have h_dvd : charpoly g ∣ P ^ finrank k V := by
    -- `↓`: `aeval_algHom_apply` has to act before `toMatrixAlgEquiv` is unfolded
    simpa [↓aeval_algHom_apply, toMatrixAlgEquiv, h_nilp.charpoly_eq_X_pow_finrank] using
      charpoly_dvd_charpoly_aeval_comp (Y := g.toMatrixAlgEquiv (finBasis k V)) P
  -- a monic divisor of a power of the prime `P` is a power of `P`; compare degrees
  obtain ⟨j, -, hj⟩ : ∃ j ≤ finrank k V, Associated (charpoly g) (P ^ j) :=
    (dvd_prime_pow hP_irred.prime _).mp h_dvd
  have h_eq : charpoly g = P ^ j :=
    eq_of_monic_of_associated (charpoly_monic g) (hP_monic.pow j) hj
  have h_deg : finrank k V = j * P.natDegree := by
    rw [← charpoly_natDegree g, h_eq, natDegree_pow]
  rw [h_eq, h_deg, Nat.mul_div_cancel _ hP_irred.natDegree_pos]

/-- Let `F` be a cuspidal element of `Hall k`, the complex-valued functions on similarity classes of
endomorphisms of finite-dimensional `k`-spaces. Cuspidal means that the average of `F` over block
triangular endomorphisms with diagonal blocks `a`, `b` vanishes whenever both blocks have nonzero
dimension. If `F` does not vanish at the similarity class of `g`, then the characteristic polynomial
of `g` is `P ^ j` for some irreducible `P ∈ k[X]` and some `j`. -/
lemma Hall.IsCuspidal.exists_charpoly_eq_pow {F : Hall k} (h_cusp : IsCuspidal F)
    (hF_ne : F (simClassOf g) ≠ 0) :
    ∃ (P : k[X]) (j : ℕ), Irreducible P ∧ charpoly g = P ^ j := by
  -- Let `P` be an irreducible factor of the characteristic polynomial of `g`, and `C` the Fitting
  -- component `ker P(g) ^ N`. Every block triangular map with diagonal blocks `g|C`, `g|V/C` is
  -- conjugate to `g`. As `F` is cuspidal, `F g ≠ 0` forces a block to be empty; it is not `C`,
  -- since `P(g)` is not invertible, so `P(g) ^ N = 0`.
  by_cases h_unit : IsUnit (charpoly g)
  · exact ⟨X, 0, irreducible_X, g.charpoly_monic.eq_one_of_isUnit h_unit⟩
  obtain ⟨P, hP_monic, hP_irred, hdvd⟩ :=
    (g.toMatrixAlgEquiv (Free.chooseBasis k V)).charpoly.exists_monic_irreducible_factor h_unit
  have not_unit : ¬IsUnit (aeval g P) := by
    simpa [aeval_algHom_apply] using fun h_inv ↦
      hP_irred.dvd_iff_not_isCoprime.mp hdvd (isUnit_aeval_iff_isCoprime.mp h_inv).symm
  obtain ⟨N, hN, hN₀⟩ :=
    ((aeval g P).eventually_isCompl_ker_pow_range_pow.and (Filter.eventually_ne_atTop 0)).exists
  have comm (Y : End k V) (hY : ∀ x : V, Y (g x) = g (Y x)) (x : V) :
      Y ((aeval g P ^ N) x) = (aeval g P ^ N) (Y x) :=
    LinearMap.congr_fun ((Algebra.commute_of_mem_adjoin_singleton_of_commute
      (aeval_mem_adjoin_singleton k g) (LinearMap.ext hY : Commute Y g)).pow_right N).eq x
  let C : StableSubspace g := ⟨ker (aeval g P ^ N), by simp +contextual [← comm g]⟩
  -- The Sylvester map `y ↦ a y - y b` (`a = g|C`, `b = g|V/C`) is injective: an intertwiner `y`
  -- commutes with `P(g) ^ N` and takes values in `C`, so it kills `range (P(g) ^ N)`.
  let sylvester : End k ((_ ⧸ C.val) →ₗ[k] C.val) :=
    C.endOnSub.compRight k - lcomp k _ C.endOnQuot
  have sylvester_inj : Function.Injective sylvester := by
    refine (injective_iff_map_eq_zero _).mpr fun y hy ↦ linearMap_qext _ <|
      ext_on_codisjoint hN.codisjoint ((ker_mkQ _).ge.trans (ker_le_ker_comp _ y)) ?_
    rintro _ ⟨v, rfl⟩
    refine Subtype.ext ((comm (C.val.subtype ∘ₗ y ∘ₗ mkQ _) (fun x ↦ ?_) v).trans (y _).prop)
    exact (congrArg Subtype.val (LinearMap.congr_fun (sub_eq_zero.mp hy) ⟦x⟧)).symm
  -- So it is surjective, and a solution `y` of `a y - y b = x` conjugates
  -- `blockTriangularEnd a b x` into `g`.
  have cls_blk (x : (V ⧸ C.val) →ₗ[k] C.val) :
      simClassOf (blockTriangularEnd C.endOnSub C.endOnQuot x) = simClassOf g := by
    obtain ⟨y, rfl⟩ := surjective_of_injective sylvester_inj x
    refine simClassOf_eq_of_equiv
      (.skewProd (quotKerEquivRange _) 1 y ≪≫ₗ prodEquivOfIsCompl _ _ hN.symm) ?_
    simp [Submodule.Quotient.forall, sylvester, endOnSub, endOnQuot, C, comm g (fun _ ↦ rfl)]
    intros
    abel
  -- The block average of `F` at `(a, b)` is thus `F g ≠ 0`, forcing `C = ⊤` (`C = ⊥` is excluded).
  refine ⟨P, _, hP_irred, charpoly_eq_pow_of_isNilpotent hP_irred hP_monic ⟨N, ?_⟩⟩
  -- `↓`: `finrank_eq_zero` has to act before the dimension facts are simplified further
  simpa [C, cls_blk, hF_ne, not_unit, hN₀, blockAverage_simClassOf, ← isUnit_iff_ker_eq_bot,
    finrank_zero_iff, ↓finrank_eq_zero] using
    h_cusp (simClassOf C.endOnSub) (simClassOf C.endOnQuot)

/-- Let k be a finite field, `q = |k|`, `d = finrank k V`, and let `greenCuspidal k η` be the class
function (β_η·μ) ∗ 𝟙, where β_η is the eigenvalue sum of η, μ is the inverse of the constant
function 𝟙 for the parabolic-induction product ∗, and β_η·μ is pointwise. Suppose `η'` is `a` times
`η` at every `z` in `K` with `z ^ q ^ d = z` whose Frobenius orbit `z, z ^ q, …, z ^ q ^ (d - 1)`
lists the eigenvalues of `g` in `K`. Then the value of `greenCuspidal` at the class of `g` for `η'`
is `a` times the value for `η`. -/
lemma greenCuspidal_simClassOf_eq_mul {a : ℂ}
    (h_scale : ∀ z : K,
      g.charpoly.aroots K =
        Multiset.map (fun i : ℕ ↦ z ^ Nat.card k ^ i) (Multiset.range (finrank k V)) →
      z ^ Nat.card k ^ finrank k V = z → a * η z = η' z) :
    greenCuspidal k η' (simClassOf g) = a * greenCuspidal k η (simClassOf g) := by
  -- If the two sides differ, some `greenCuspidal k θ (simClassOf g)` is nonzero. Then `charpoly g`
  -- is a power of an irreducible `P`, and every eigenvalue of `g` satisfies `h_scale`.
  by_cases! h_zero : ∀ θ : K → ℂ, greenCuspidal k θ (simClassOf g) = 0
  · simp [h_zero]
  obtain ⟨θ, hθ⟩ : ∃ θ : K → ℂ, greenCuspidal k θ (simClassOf g) ≠ 0 := h_zero
  obtain ⟨P, j, hP, hg⟩ : ∃ (P : k[X]) (j : ℕ), Irreducible P ∧ charpoly g = P ^ j :=
    (isCuspidal_greenCuspidal θ).exists_charpoly_eq_pow hθ
  -- By `aroots_pow_eq_frobenius_orbit`, the roots of `P ^ j` are the Frobenius orbit of any one
  -- root `z`.
  have h_root (z : K) (hz : aeval z g.charpoly = 0) : a * η z = η' z := by
    grind [aroots_pow_eq_frobenius_orbit, pow_ne_zero, charpoly_natDegree]
  -- `greenCuspidal k η` reads `η` only at eigenvalues of restrictions to stable subspaces `W`.
  have h_terms (W : StableSubspace g) (z : K) (hz : z ∈ (charpoly W.endOnSub).aroots K) :
      η' z = a * η z := by
    -- `z` is a root of `charpoly (g|W)`, a factor of `charpoly g`
    obtain ⟨-, hz_root⟩ : charpoly W.endOnSub ≠ 0 ∧ aeval z (charpoly W.endOnSub) = 0 :=
      mem_aroots.mp hz
    refine (h_root z ?_).symm
    rw [← charpoly_endOnSub_mul_endOnQuot _ W, map_mul, hz_root, zero_mul]
  suffices h_sum_eq : ∑ W : StableSubspace g,
      (Multiset.map (fun x ↦ η' x) ((charpoly W.endOnSub).aroots K)).sum *
        moebius (simClassOf W.endOnSub) =
      ∑ W : StableSubspace g,
        (Multiset.map (fun x ↦ a * η x) ((charpoly W.endOnSub).aroots K)).sum *
          moebius (simClassOf W.endOnSub) by
    simpa [greenCuspidal, mul_simClassOf, mulMoebius, Finset.mul_sum, ← mul_assoc,
      ← sum_map_mul_left, finsum_eq_sum_of_fintype] using h_sum_eq
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  rw [Multiset.map_congr rfl (h_terms W)]

end CuspidalSupport

/-!
## Values of μ and C_η at multiplication by a field generator

Let z generate a finite extension F = k[z] of k; class functions are evaluated at multiplication by
z.
-/

section CuspidalAtScalars

open Module Matrix Finset Hall Polynomial Fintype Algebra minpoly Lagrange Submodule StableSubspace
  GeneralLinearGroup

attribute [local instance low] Fintype.ofFinite

variable {k K F V : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [Field F] [Finite F]
  [Algebra k F]
  (z : PowerBasis k F) [AddCommGroup V] [Module k V] [Module F V] [IsScalarTower k F V]
  [Module.Finite k V] [Module.Finite F V]

/-- The order of GL_n(k), for a finite field k with q elements, is the product of q^i (q^{i+1} − 1)
over 0 ≤ i < n, as an identity in any field. -/
lemma card_GL_eq_prod {n R : Type*} [Fintype n] [DecidableEq n] [Field R] :
    Nat.card (GL n k) =
      ∏ i ∈ range (Fintype.card n), (Nat.card k ^ i * (Nat.card k ^ (i + 1) - 1) : R) := by
  -- Mathlib gives `∏ i, (q ^ n - q ^ i)`; regroup the factors by induction on `d`.
  suffices h_prod : ∀ d : ℕ,
      ∏ i : Fin d, ((Fintype.card k : R) ^ d - (Fintype.card k : R) ^ (i : ℕ)) =
      (∏ i ∈ range d, (Fintype.card k : R) ^ i) *
        ∏ i ∈ range d, ((Fintype.card k : R) ^ (i + 1) - 1) by
    have h_card : Nat.card (GL n k) = Nat.card (GL (Fin (card n)) k) :=
      Nat.card_congr (Units.mapEquiv (reindexRingEquiv k (equivFin n)).toMulEquiv).toEquiv
    rw [h_card, card_GL_field]
    simpa [Nat.pow_le_pow_right card_pos, prod_mul_distrib] using h_prod (card n)
  intro d
  induction d with
  | zero => rw [Fin.prod_univ_zero, prod_range_zero, prod_range_zero, one_mul]
  | succ m ih =>
    simp_all [Fin.prod_univ_succ, prod_range_succ, pow_succ, ← sub_mul, prod_mul_distrib]
    ring

open Classical in
/-- Let `g` be an endomorphism of a finite space `V` and `U ≠ V` a `g`-stable subspace. The sum of
μ at the classes of `g` on `V/W`, over the `g`-stable subspaces `W ⊇ U`, is `0`. -/
private lemma sum_moebius_endOnQuot_eq_zero_of_ne_top {g : Module.End k V}
    (U : StableSubspace g) (hU : (U : Submodule k V) ≠ ⊤) :
    ∑ W : StableSubspace g with (U : Submodule k V) ≤ W.val,
      moebius (simClassOf W.endOnQuot) = 0 := by
  -- The stable subspaces above `U` are those of `V/U`, so this sum is
  -- `(constOne * moebius)(V/U) = 0`.
  have h_mkQ_comm (x : V) :
      (U : Submodule k V).mkQ (g x) = U.endOnQuot ((U : Submodule k V).mkQ x) := rfl
  have h_quo : ∑ W : StableSubspace g with (U : Submodule k V).mkQ.ker ≤ W.val,
      moebius (simClassOf W.endOnQuot) =
        (constOne * moebius : Hall k) (simClassOf U.endOnQuot) := by
    refine (sum_comap (U : Submodule k V).mkQ (g' := U.endOnQuot) h_mkQ_comm _).trans ?_
    simp [mul_simClassOf, finsum_eq_sum_of_fintype]
  rw [mul_comm constOne, moebius_mul_constOne] at h_quo
  simpa [hU, finrank_zero_iff] using h_quo

/-- Let `F = k[z]` be a finite field extension of the finite field `k`, given by a power basis `z`,
and let `Q` be the number of elements of `F`. Let `V` be an `F`-space of dimension `d`, let
`N = ∏_{0≤i<d} (X − Q^i)`, and let `g` be multiplication by `z` on `V`, viewed as a `k`-linear
endomorphism. Then `moebius` (the inverse μ of the constant function 𝟙 under the induction product
on functions of similarity classes) takes the value `N(0)` at the class of `g`, and
`greenCuspidal k η` (the class function `C_η = (β_η·μ) ∗ 𝟙`) takes the value `−N′(1)` times the sum
of `η` over the roots in `K` of the minimal polynomial of `z`. -/
lemma moebius_and_greenCuspidal_lsmul (η : K → ℂ) :
    let N : ℂ[X] := nodal (range (finrank F V)) fun i : ℕ ↦ ((Nat.card F ^ i : ℕ) : ℂ)
    let g : Module.End k V := lsmul k k V z.gen
    moebius (simClassOf g) = N.eval 0 ∧
    greenCuspidal k η (simClassOf g) =
      -(((minpoly k z.gen).aroots K).map η).sum * N.derivative.eval 1 := by
  classical
  -- With `m = finrank F V`, `Q = |F|`: the polynomial `M = ∑_W μ(V/W) X ^ dim W` is monic of degree
  -- `m` and vanishes at `Q ^ j`, `j < m`, so `M = N`; both values are read off from `M`.
  intro N g
  have h_finite_V : Finite V := finite_of_finite k
  -- As `z.gen` generates `F`, a `g`-stable `k`-subspace is an `F`-subspace.
  let S (W : StableSubspace g) : Submodule F V :=
    { toAddSubmonoid := (W : Submodule k V).toAddSubmonoid
      smul_mem' := fun c x hx ↦ by
        obtain ⟨p, rfl⟩ : ∃ p : k[X], c = aeval z.gen p := z.exists_eq_aeval' c
        exact aeval_apply_smul_mem_of_le_comap' hx _ _ W.property }
  let M : ℂ[X] := ∑ W, monomial (finrank F (S W)) (moebius (simClassOf W.endOnQuot))
  -- `M` and `N` agree in degrees `≥ m`: there only `W = ⊤` contributes to `M`, giving `X ^ m`.
  have h_coeff (n : ℕ) (hn : finrank F V ≤ n) : (N - M).coeff n = 0 := by
    let W_top : StableSubspace g := ⟨⊤, fun _ _ ↦ Submodule.mem_top⟩
    have hS_top : S W_top = ⊤ := Submodule.ext fun _ ↦ by simp [S, W_top]
    have hN_monic : N.IsMonicOfDegree (finrank F V) := ⟨by simp [N], nodal_monic⟩
    rw [coeff_sub, ← (isMonicOfDegree_monomial_one _).coeff_eq hN_monic hn, finsetSum_coeff,
      Fintype.sum_eq_single W_top, hS_top, finrank_top]
    · simp [coeff_monomial, finrank_zero_iff, W_top]
    · intro W hW
      have h_lt : finrank F (S W) < finrank F V :=
        (S W).finrank_lt fun h ↦ hW (Subtype.ext (top_unique h.ge))
      exact coeff_monomial_of_ne _ (h_lt.trans_le hn).ne'
  -- `|W| ^ j` counts the `j`-tuples `v` in `W`; for `j < m` no `v` spans `V`.
  have h_root (j : ℕ) (hj : j < finrank F V) : M.eval ((Nat.card F ^ j : ℕ) : ℂ) = 0 := by
    have h_count (W : StableSubspace g) : ((Nat.card F ^ j : ℕ) : ℂ) ^ finrank F (S W) =
        ∑ v : Fin j → V, if span F (.range v) ≤ S W then 1 else 0 := by
      rw [← Nat.cast_pow, pow_right_comm, ← natCard_eq_pow_finrank]
      simp_rw [Nat.card_eq_fintype_card, Nat.cast_pow, Fintype.card_subtype, ← sum_boole,
        Fintype.sum_pow, Fintype.prod_boole, span_le, Set.range_subset_iff, SetLike.mem_coe]
      congr!
    simp_rw [M, eval_finsetSum, eval_monomial, h_count, mul_sum]
    rw [sum_comm]
    refine Finset.sum_eq_zero fun v _ ↦ ?_
    -- The span `U` of `v` is a stable subspace other than `V`, as `j < m`.
    let U : StableSubspace g := ⟨(span F (.range v)).restrictScalars k, by aesop⟩
    have hU_ne : (U : Submodule k V) ≠ ⊤ := by simp [U, mt finrank_le_of_span_eq_top, hj]
    have h_le_iff (W : StableSubspace g) :
        span F (.range v) ≤ S W ↔ (U : Submodule k V) ≤ W := Iff.rfl
    simpa [sum_filter, h_le_iff] using sum_moebius_endOnQuot_eq_zero_of_ne_top U hU_ne
  -- `N - M` has degree `< m` and vanishes at the `m` distinct points `Q ^ j`.
  have h_deg : (N - M).degree < #(range (finrank F V)) := by
    simpa [Finset.card_range, degree_lt_iff_coeff_zero] using h_coeff
  have hN : N = M :=
    eq_of_degree_sub_lt_of_eval_index_eq _
      (Nat.cast_injective.comp (Nat.pow_right_injective Finite.one_lt_card)).injOn h_deg
      fun j hj ↦ (eval_nodal_at_node hj).trans (h_root j (mem_range.mp hj)).symm
  rw [hN]
  constructor
  · -- In `moebius = 1 * moebius` and in `M(0)` only `W = ⊥` contributes.
    have hS_subsingleton (W : StableSubspace g) :
        Subsingleton (S W) ↔ Subsingleton (W : Submodule k V) := Iff.rfl
    rw [← one_mul moebius]
    simp [M, zero_pow_eq, finrank_zero_iff, mul_simClassOf, finsum_eq_sum_of_fintype,
      eval_finsetSum, hS_subsingleton]
  · -- On `W` the characteristic polynomial is the `dim W`-th power of the minimal polynomial.
    have h_brauer (W : StableSubspace g) : brauerLift k η (simClassOf W.endOnSub) =
        finrank F (S W) * (((minpoly k z.gen).aroots K).map η).sum := by
      change brauerLift k η (simClassOf (lsmul k k (S W) z.gen)) = _
      simp [z.finrank, ← finrank_mul_finrank k F, z.dim_pos.ne', monic z.isIntegral_gen,
        charpoly_eq_pow_of_isNilpotent (irreducible z.isIntegral_gen), Multiset.map_nsmul,
        Multiset.sum_nsmul]
    -- `moebius` is inverse to `constOne`; expand the product over `W` and compare with `M'(1)`.
    have h_cusp : greenCuspidal k η = -brauerLift k η * moebius := by
      grind [moebius_mul_constOne, greenCuspidal_mul_constOne η]
    -- `h_brauer` is applied before `simp` unfolds `brauerLift` (hence `↓`).
    simp [M, h_cusp, ↓h_brauer, derivative_monomial, mul_sum, mul_simClassOf,
      finsum_eq_sum_of_fintype, eval_finsetSum]
    -- The two sums agree term by term up to the order of the factors.
    ac_rfl

/-- Let F = k[z] have Q elements and let V be an F-space of dimension d. At multiplication by z
on V, μ = 𝟙⁻¹ takes the value N(0), where N = ∏_{0≤i<d} (X − Q^i). -/
lemma moebius_simClassOf_lsmul :
    moebius (simClassOf (lsmul k k V z.gen)) =
      (nodal (range (finrank F V)) fun i : ℕ ↦ ((Nat.card F ^ i : ℕ) : ℂ)).eval 0 :=
  (moebius_and_greenCuspidal_lsmul (K := k) z fun _ : k ↦ (0 : ℂ)).1

/-- Let F = k[z] have Q elements and let V be an F-space of dimension d. At multiplication by z
on V, C_η takes the value −N′(1) times the sum of η over the roots in K of the minimal polynomial
of z, where N = ∏_{0≤i<d} (X − Q^i). -/
private lemma greenCuspidal_simClassOf_lsmul (η : K → ℂ) :
    greenCuspidal k η (simClassOf (lsmul k k V z.gen)) =
      -(((minpoly k z.gen).aroots K).map η).sum *
        (nodal (range (finrank F V)) fun i : ℕ ↦ ((Nat.card F ^ i : ℕ) : ℂ)).derivative.eval 1 :=
  (moebius_and_greenCuspidal_lsmul z η).2

/-- Let k be a finite field, μ (`moebius`) the inverse of the constant class function 𝟙 for the
parabolic-induction product ∗, and C_η = `greenCuspidal k η` = (β_η·μ) ∗ 𝟙 for η : K → ℂ, where β_η
is the eigenvalue sum of η. Let F = k[z] and V a non-zero finite-dimensional F-space. Then the value
of the pointwise product C_η·μ at multiplication by z on V, times #V - 1, is the sum of η over the
roots in K of the minimal polynomial of z, times the order of the centraliser of z in GL_k(V). -/
lemma mulMoebius_greenCuspidal_lsmul (η : K → ℂ) [Nontrivial V] :
    (greenCuspidal k η).mulMoebius (simClassOf (lsmul k k V z.gen)) * (Nat.card V - 1 : ℕ) =
      (((minpoly k z.gen).aroots K).map η).sum *
        Nat.card {e : V ≃ₗ[k] V // ∀ x : V, e (z.gen • x) = z.gen • e x} := by
  -- As `z.gen` generates `F`, the `k`-automorphisms of `V` that commute with it are `F`-linear.
  have h_F_linear (f : V ≃ₗ[k] V) (hf : ∀ x : V, f (z.gen • x) = z.gen • f x) (c : F) :
      ∀ x : V, f (c • x) = c • f x := by
    induction eq_top_iff.mp z.adjoin_gen_eq_top c using adjoin_induction with
    | mem a ha => rwa [Set.mem_singleton_iff.mp ha]
    | algebraMap r => simp
    | add a b _ _ ha hb => simp [add_smul, ha, hb]
    | mul a b _ _ ha hb => simp [mul_smul, ha, hb]
  -- The `F`-linear automorphisms of `V` are the `k`-linear ones that commute with `z.gen`.
  let restrictScalarsEquiv : LinearMap.GeneralLinearGroup F V ≃
      {e : V ≃ₗ[k] V // ∀ x, e (z.gen • x) = z.gen • e x} :=
    .mk (fun g ↦ ⟨g.toLinearEquiv.restrictScalars k, by simp⟩) fun ⟨f, hf⟩ ↦
      .ofLinearEquiv { f with map_smul' := h_F_linear f hf }
  have h_card : Nat.card (GL (Fin (finrank F V)) F) =
      Nat.card {e : V ≃ₗ[k] V // ∀ x, e (z.gen • x) = z.gen • e x} :=
    Nat.card_congr ((toLin' (finBasis F V)).toEquiv.trans restrictScalarsEquiv)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, finrank F V = m + 1 := Nat.exists_eq_add_one.mpr finrank_pos
  -- With `N = (∏_{i<m} (X - Q ^ (i + 1))) (X - 1)`, `moebius_simClassOf_lsmul` and
  -- `greenCuspidal_simClassOf_lsmul` give the left side through `N'(1) = ∏_{i<m} (1 - Q ^ (i + 1))`
  -- and `N(0) = ∏_{i≤m} (-Q ^ i)`; compare with `card_GL_eq_prod`.
  simp_rw [mulMoebius, moebius_simClassOf_lsmul z, greenCuspidal_simClassOf_lsmul z η]
  rw [natCard_eq_pow_finrank (K := F) (V := V), eq_comm, ← h_card, card_GL_eq_prod, hm, nodal,
    prod_range_succ']
  -- With `s` the sum of `η` over the roots and `Q = |F|`, both sides are the following product.
  have h_regroup (s Q : ℂ) : s * ((-1) ^ m * ((∏ x ∈ range m, Q ^ x) * Q ^ m *
        ((∏ x ∈ range m, (1 - Q ^ x * Q)) * (1 - Q ^ m * Q)))) =
      (s * ∏ x ∈ range m, (1 - Q ^ x * Q)) * ((-1) ^ m * ((∏ x ∈ range m, Q ^ x) * Q ^ m)) *
        (1 - Q ^ m * Q) := by
    ring
  -- Write every factor in the form `1 - Q ^ j`; the two exclusions keep `simp` from undoing this.
  simpa [eval_prod, pow_succ, prod_range_succ, ← neg_sub (1 : ℂ), -neg_sub,
    -Nat.card_eq_fintype_card, prod_neg, prod_mul_distrib] using h_regroup _ _

end CuspidalAtScalars

/-!
## The inner product of C_η with B·μ

Let L be a finite extension of the finite field k, and let φ be a k-embedding of L into a field K.
Let η be a function K → ℂ.
-/

section CuspidalInnerProduct

open Polynomial Finset Hall Module LinearMap minpoly IntermediateField
  GeneralLinearGroup IsGalois LinearEquiv FiniteField ComplexConjugate Fintype IsTorsionBySet

attribute [local instance low] Fintype.ofFinite

variable {k : Type*} [Field k] [Finite k] {K : Type*} [Field K] [Algebra k K] (η : K → ℂ)

omit [Finite k] in
/-- Let `L` be a finite field that is a `k`-algebra, and `g` a semisimple `k`-linear endomorphism of
`L` whose characteristic polynomial is a power `P ^ j` of an irreducible `P`. Then `g` is conjugate
to a multiplication: there are a `k`-linear automorphism `e` of `L` and `y ∈ L` with
`e ∘ (y * ·) ∘ e⁻¹ = g`. Both `g` and a root of `P` in `L` make `L` a vector space over `k[X]/(P)`,
of the same dimension. -/
lemma exists_conj_mulLeft_eq {L : Type*} [Field L] [Finite L] [Algebra k L] {g : End k L} {P : k[X]}
    {j : ℕ} (hg : g.IsSemisimple) (hP : Irreducible P) (h_charpoly : g.charpoly = P ^ j) :
    ∃ (e : L ≃ₗ[k] L) (y : L), e.conjAlgEquiv k (Algebra.lmul k L y) = g := by
  -- The minimal polynomial is squarefree and divides `P ^ j`, so `P` kills `g`.
  have h_aeval : Polynomial.aeval g P = 0 := dvd_iff.mp <|
    hg.minpoly_squarefree.isRadical j P ((minpoly_dvd_charpoly g).trans h_charpoly.dvd)
  -- `V` is `L` as a `k[X]`-module through `g`, hence a vector space over `k[X]/(P)`.
  let V : Type _ := AEval' g
  have : Fact (Irreducible P) := ⟨hP⟩
  have : Module.Finite k (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have : Finite V := inferInstanceAs (Finite L)
  let _ : Module (AdjoinRoot P) V := IsTorsionBy.module (LinearMap.congr_fun h_aeval)
  have : IsScalarTower k (AdjoinRoot P) V := IsTorsionBySet.isScalarTower _
  have tower_V := finrank_mul_finrank k (AdjoinRoot P) V
  -- So `[k[X]/(P) : k] ∣ [L : k]`, giving an embedding `k[X]/(P) ↪ L` and an isomorphism `V ≃ L`.
  let _ : Algebra (AdjoinRoot P) L :=
    (nonempty_algHom_of_finrank_dvd (L := L) ⟨_, tower_V.symm⟩).some.toAlgebra
  let t : V ≃ₗ[AdjoinRoot P] L := ofFinrankEq _ _ <|
    mul_left_cancel₀ finrank_pos.ne' (tower_V.trans (finrank_mul_finrank k (AdjoinRoot P) L).symm)
  exact ⟨t.symm.restrictScalars k, algebraMap _ L (AdjoinRoot.root P),
    ext fun x ↦ (t.symm_apply_eq.mpr (t.map_smul _ x).symm).trans (AEval'.X_smul_of g x)⟩

/-- Let k be a finite field, K a field over k, η : K → ℂ, and C_η = `greenCuspidal k η` = (β_η·μ)
∗ 𝟙. Here β_η is the eigenvalue sum of η, μ (`moebius`) is the inverse of the constant class
function 𝟙 for the parabolic-induction product ∗, and B·μ is the pointwise product. For a finite
extension L of k with a k-embedding φ : L → K and any class function B, the average over
GL_{[L:k]}(k) of conj C_η times B·μ (`rankInner`) is the mean (`finMean`) over z ∈ L^× of conj η(φz)
times B at the class of multiplication by z on L. -/
lemma rankInner_greenCuspidal_mulMoebius {L : Type*} [Field L] [Finite L] [Algebra k L]
    (φ : L →ₐ[k] K) (B : Hall k) :
    rankInner (finrank k L) (greenCuspidal k η) B.mulMoebius =
      finMean fun z : Lˣ ↦ conj (η (φ z)) * B (simClassOf (mulLeft k z.val)) := by
  classical
  -- `ρ e z` is the conjugate by `e` of multiplication by `z`. The function
  -- `(greenCuspidal k η).mulMoebius` is induced from `η ∘ φ` (`induced`); the claim is then
  -- Frobenius reciprocity, `μ` being real.
  let ρ (e : L ≃ₗ[k] L) : L →ₐ[k] End k L := (e.conjAlgEquiv k).toAlgHom.comp (Algebra.lmul k L)
  let algebra_LK : Algebra L K := φ.toAlgebra
  have : Finite (L ≃ₗ[k] L) := DFunLike.finite (L ≃ₗ[k] L)
  have cls_conj (e : L ≃ₗ[k] L) (z : L) : simClassOf (ρ e z) = simClassOf (mulLeft k z) :=
    simClassOf_eq_of_equiv e.symm fun x ↦ by simp [ρ]
  have induced (g : End k L) : (greenCuspidal k η).mulMoebius (simClassOf g) =
      (∑ z, η (φ z) * Nat.card {e // ρ e z = g}) / Nat.card Lˣ := by
    rcases em' (∃ (a : L ≃ₗ[k] L) (y : L), ρ a y = g) with h_not_conj | ⟨a, y, rfl⟩
    · -- Off the conjugates of multiplications both sides vanish.
      suffices vanish : (greenCuspidal k η).mulMoebius (simClassOf g) = 0 by simp_all
      by_contra h_ne
      obtain ⟨hC, hμ⟩ : greenCuspidal k η (simClassOf g) ≠ 0 ∧ moebius (simClassOf g) ≠ 0 :=
        mul_ne_zero_iff.mp h_ne
      obtain ⟨P, j, hP, h_charpoly⟩ : ∃ (P : k[X]) (j : ℕ), Irreducible P ∧ charpoly g = P ^ j :=
        (isCuspidal_greenCuspidal η).exists_charpoly_eq_pow hC
      exact h_not_conj (exists_conj_mulLeft_eq (isSemisimple_of_moebius_ne_zero hμ) hP h_charpoly)
    -- At `ρ a y`, `mulMoebius_greenCuspidal_lsmul` for the field `k(y)` gives `#Lˣ` times the value
    -- as the sum of `η` over the roots of `minpoly k y` (simple, and in `L`) times the order of the
    -- centraliser of `y`; compare with the right side term by term.
    have h_card_ne : (Nat.card Lˣ : ℂ) ≠ 0 := by simp
    -- Multiplication by `y` on `L` is the action of the generator of the field `k⟮y⟯`.
    have h_mulLeft : mulLeft k y = Algebra.lsmul k k L (adjoin.powerBasis (integral k y)).gen := rfl
    have h_gen : (adjoin.powerBasis (integral k y)).gen = AdjoinSimple.gen k y := rfl
    rw [eq_div_iff h_card_ne, cls_conj, Nat.card_units, h_mulLeft,
      mulMoebius_greenCuspidal_lsmul (adjoin.powerBasis (integral k y)), h_gen, minpoly_gen,
      ← (splits _ y).map_aroots_algebraMap, Multiset.map_map,
      ← sum_mk _ (nodup_roots (.map (separable k y))), sum_mul]
    refine sum_subset_zero_on_sdiff le_top (fun z hz ↦ ?_) fun z hz ↦ ?_
    · -- If `z` is not a root of `minpoly k y`, no `ρ e z` is `ρ a y`.
      have h_aeval_ne (e : L ≃ₗ[k] L) :
          aeval (ρ e z) (minpoly k y) ≠ aeval (ρ a y) (minpoly k y) := by
        simp_all [aeval_algHom_apply, ne_zero_of_finite]
      have h_ne (e : L ≃ₗ[k] L) : ρ e z ≠ ρ a y :=
        ne_of_apply_ne (fun f ↦ aeval f (minpoly k y)) (h_aeval_ne e)
      simp [h_ne]
    · -- If `y = c z`, then `e ↦ a * e * c` maps the centraliser of `y` onto the `e` with
      -- `ρ e z = ρ a y`.
      obtain ⟨-, h_root⟩ : minpoly k y ≠ 0 ∧ aeval z (minpoly k y) = 0 := mem_aroots.mp hz
      obtain ⟨c, rfl⟩ : ∃ c : Gal(L/k), c z = y :=
        exists_algEquiv_of_root (IsAlgebraic.of_finite k _) h_root
      rw [Nat.card_congr ((Equiv.mulLeft a * .mulRight c).subtypeEquiv fun e ↦ ?_)]
      · rfl
      · rw [LinearMap.ext_iff]
        have h_comm_iff (v : L) :
            e (AdjoinSimple.gen k (c z) • v) = AdjoinSimple.gen k (c z) • e v ↔
              ρ ((Equiv.mulLeft a * Equiv.mulRight (c : L ≃ₗ[k] L)) e) z ((a * e) v) =
                ρ a (c z) ((a * e) v) := by
          simp [ρ, Algebra.smul_def, mul_eq_trans]
        exact (a * e).forall_congr h_comm_iff
  have unit_eq (e : L ≃ₗ[k] L) (z : Lˣ) (g : (End k L)ˣ) : ρ e z = g.val ↔ z.map (ρ e) = g :=
    .symm Units.ext_iff
  -- Write both sides as sums, drop `z = 0` (it gives no unit `g`) and sum over `g` first.
  refine star_injective ?_
  simp only [rankInner_eq_classInner_simClassOf, classInner, finMean]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp [induced, cls_conj, unit_eq, sum_eq_add_sum_subtype_ne _ (0 : L), mul_left_comm, Ne.symm,
    mul_div, ← unitsEquivNeZero.sum_comp, Fintype.card_subtype, ← sum_boole, ← sum_comm_cycle,
    ← sum_div, mul_sum, field, card_congr (generalLinearEquiv k L).toEquiv, mul_comm _ (η _)]

/-- The characteristic of a finite field is prime. -/
instance : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩

end CuspidalInnerProduct

end New
