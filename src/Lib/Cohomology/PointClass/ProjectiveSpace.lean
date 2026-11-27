module

public import Aesop.BuiltinRules
public import Mathlib.RingTheory.Invariant.Defs
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import Lib.General.Geometry.ProjectiveSpace
public import Lib.General.Geometry.EtaleCharts
import Lib.General.Algebra.MultivariatePolynomials
import Lib.General.Geometry.PointsOfProperSchemes
import Lib.PadicComparison.Descent.TestCategory
public import Lib.PadicComparison.HodgeTate.GenericFibre
import Lib.PadicComparison.Descent.TestCovers
import Lib.PadicComparison.Primitive.PeriodCoefficients

section
/-!
# Projective Noether normalisation and homogeneous coordinates of embedded points

Let k be a field. For a tuple `g : ι → L`, `New.Variety.CutsOutLocus.IsHomogeneousSolution k g w`
says that every homogeneous polynomial over k that vanishes at g also vanishes at w. The file proves
projective Noether normalisation by linear forms in characteristic zero and constructs its Galois
closure.

## Main definitions and results

* `New.Variety.CutsOutLocus.IsNoetherNormalization Λ g`: the linear forms `Λ₀, …, Λ_d` are a Noether
  normalisation of the cone, that is, their values at `g` are independent and the cone is integral
  over them.
* `New.Variety.CutsOutLocus.exists_isNoetherNormalization`: such forms exist for a non-zero finite
  tuple `g` over a field `k` of characteristic zero.
* `New.Variety.CutsOutLocus.IsNoetherNormalization.GaloisClosure`,
  `New.Variety.CutsOutLocus.IsNoetherNormalization.nonempty_galoisClosure`: the Galois closure of
  the normalisation, a finite algebra `B` over `k[X₀, …, X_d]` with points `b σ` of the cone,
  indexed by a finite group.
* `New.Variety.IsCoordsWithUnit.exists_universal_chart`,
  `New.Variety.IsCoordsWithUnit.exists_mem_open_of_isUnit`: a point ξ over a field F with
  coordinates g spreads out and specialises to the vectors w with w i (resp. aeval w b) a unit that
  satisfy the homogeneous relations of g.
* `New.Variety.IsCoordsWithUnit.exists_app_eq_algebraMap_of_isHomogeneousSolution`: over an
  algebraically closed k, a global function takes one constant value on all such specialisations.

Notions from other files:
* `New.LineBundle.IsHomogeneousCoords`: v is a vector of homogeneous coordinates of the point t for
  L: t lands in U_j exactly when v_j is a unit, and then g_jk(t) = v_k/v_j.
* `New.Variety.IsOpenSubfunctor`: V is an open subfunctor of X: each x ∈ X(A) has an ideal I of A
  such that, for φ: A → B, φ(x) ∈ V(B) iff φ(I)B = B.

## Relation to the literature

Known; see `Lib.Cohomology.PointClass.LinearIndependence` for sources.
-/

@[expose] public section

/-!
## Noether normalisation of a cone by linear forms

Noether normalisation is stated for coordinate vectors instead of varieties. A tuple `g : ι → L`
stands for the cone cut out by the homogeneous polynomials over `k` that vanish at `g`.
-/

section NoetherNormalization

open Fin MvPolynomial Finset Function Finite IsScalarTower FaithfulSMul Algebra Ideal RingHom

namespace New.Variety.CutsOutLocus

variable {k L ι A B C : Type} [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A]
  {u : A} [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
  {g : ι → B} {v : ι → A} {d : ℕ} (Λ : Fin (d + 1) → homogeneousSubmodule ι k 1)
  {F : MvPolynomial ι k} (φ : A →ₐ[k] C) (ψ : A →ₐ[k] L)

/-! ### The cone of a coordinate vector -/

variable (k g v) in
/-- The point `v` lies on the cone of `g`: every homogeneous polynomial over `k` that vanishes at
`g` vanishes at `v`. The two tuples may have entries in different `k`-algebras. -/
def IsHomogeneousSolution : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃F : MvPolynomial ι k⦄, F.IsHomogeneous n → F.aeval g = 0 → F.aeval v = 0

/-- The tuple of values of the polynomials `Λ j` at `v`. -/
noncomputable abbrev evalForms (v : ι → A) (j : Fin (d + 1)) : A := ((Λ j).val.aeval v : A)

/-- A homogeneous polynomial of degree `n` takes at `u • v` the value `u ^ n` times that at `v`. -/
@[grind =>]
lemma aeval_smul_of_isHomogeneous {n : ℕ} (hF : F.IsHomogeneous n) :
    aeval (u • v) F = u ^ n * aeval v F :=
  hF.eval₂_const_mul (algebraMap k A) v u

/-- If `χ` kills the kernel of `φ` and `φ ∘ v` lies on the cone of `g`, then so does `χ ∘ v`. -/
lemma IsHomogeneousSolution.of_ker {D : Type} [CommRing D] [Algebra k D] (χ : A →ₐ[k] D)
    (h_ker : ∀ r : A, φ r = 0 → χ r = 0) (h_sol : IsHomogeneousSolution k g (φ ∘ v)) :
    IsHomogeneousSolution k g (χ ∘ v) := fun _ F hF h_g ↦
  -- `F (χ ∘ v) = χ (F v)`, and `φ (F v) = F (φ ∘ v) = 0`
  (comp_aeval_apply v χ F).symm.trans (h_ker _ ((comp_aeval_apply v φ F).trans (h_sol hF h_g)))

lemma IsHomogeneousSolution.map : IsHomogeneousSolution k g v → IsHomogeneousSolution k g (φ ∘ v) :=
  of_ker 1 φ (by simp)

lemma IsHomogeneousSolution.smul (u : C) (h : IsHomogeneousSolution k g v) :
    IsHomogeneousSolution k g (u • φ ∘ v) := by
  intro n F hF h_g
  have h_map : aeval (φ ∘ v) F = 0 := h.map φ hF h_g
  rw [aeval_smul_of_isHomogeneous hF, h_map, mul_zero]

@[simp]
lemma evalForms_map (v : ι → A) : evalForms Λ (φ ∘ v) = φ ∘ evalForms Λ v := by
  simp [comp_aeval_apply, comp_def]

@[simp]
lemma evalForms_smul : evalForms Λ (u • v) = u • evalForms Λ v := by
  simp [funext_iff, aeval_smul_of_isHomogeneous (Λ _).prop]

/-- If `t` is transcendental over the ring `B` of the entries of `g`, every polynomial that
vanishes at `t • g`, homogeneous or not, vanishes at each point `v` of the cone of `g`. -/
lemma IsHomogeneousSolution.aeval_eq_zero_of_transcendental [Algebra B L] [IsScalarTower k B L]
    {t : L} (ht : Transcendental B t) (h_sol : IsHomogeneousSolution k g v)
    (h_zero : aeval (t • algebraMap B L ∘ g) F = 0) :
    aeval v F = 0 := by
  -- Split `F` into homogeneous components `F_n`. The values `F_n(g)` are the coefficients of a
  -- polynomial over `B` that vanishes at `t`, so they are zero.
  let P : Polynomial B :=
    ∑ n ∈ range (F.totalDegree + 1), .monomial n (aeval g (homogeneousComponent n F))
  rw [← F.sum_homogeneousComponent, map_sum] at h_zero ⊢
  -- `P (t)` is the sum in `h_zero`, by homogeneity of the `F_n`
  have h_sum : P.aeval t = ∑ n ∈ range (F.totalDegree + 1),
      aeval (t • algebraMap B L ∘ g) (homogeneousComponent n F) := by
    simp [P, Polynomial.aeval_monomial, mul_comm, aeval_algebraMap_apply,
      aeval_smul_of_isHomogeneous (homogeneousComponent_mem _ F)]
  have hP : P = 0 := transcendental_iff.mp ht P (h_sum.trans h_zero)
  refine sum_eq_zero fun n hn ↦ h_sol (homogeneousComponent_mem n F) ?_
  -- the value `F_n(g)` is the `n`-th coefficient of `P = 0`
  simpa [P, Polynomial.coeff_monomial, Finsupp.single_apply, hn] using
    congrArg (fun p : Polynomial B ↦ p.coeff n) hP

lemma IsHomogeneousSolution.refl : IsHomogeneousSolution k v v := by tauto

/-- An element of a field `L` that lies in every valuation ring containing the image of `f` is
integral over that image. -/
@[stacks 090P "part (1), for the integral closure of the image of a ring map"]
lemma isIntegralElem_of_valuationSubring {f : A →+* L} {x : L}
    (h : ∀ V : ValuationSubring L, (∀ a : A, f a ∈ V) → x ∈ V) :
    f.IsIntegralElem x := by
  -- The integral closure of `A` in `L` is the intersection of the valuation rings that contain it.
  let algebraL : Algebra A L := f.toAlgebra
  refine (integralClosure A L).toSubring.eq_iInf_of_isIntegrallyClosedIn.ge ?_
  simpa using fun V hV ↦ h V fun a ↦ hV isIntegral_algebraMap

/-! ### Noether normalisation -/

/-- Λ is a Noether normalisation of g: the Λ_0, …, Λ_d are linear forms, the values Λ_j(g) have no
non-zero homogeneous relation, and every field-valued point v of the cone of g is integral over
any image of a `k`-algebra that contains the values Λ_j(v). -/
def IsNoetherNormalization (g : ι → L) : Prop :=
  -- the values of the forms `Λ j` at `g` satisfy no non-zero homogeneous relation over `k`
  IsHomogeneousSolution k (evalForms Λ g) (X (R := k)) ∧
  -- a solution `v` of the homogeneous equations of `g` is integral over every ring `R` whose
  -- image contains the values of `Λ` at `v`
  ∀ {K R : Type} [Field K] [Algebra k K] [CommRing R] [Algebra k R] (φ : R →ₐ[k] K)
      (p : Fin (d + 1) → R) (v : ι → K),
    IsHomogeneousSolution k g v → evalForms Λ v = φ ∘ p → ∀ i : ι,
    φ.IsIntegralElem (v i)

/-- Let `φ : A → C` be integral and `ψ : A → L` a map to an algebraically closed field whose
kernel contains that of `φ`. Then `ψ = χ ∘ φ` for some map `χ : C → L` of `k`-algebras. -/
lemma exists_algHom_comp_eq_of_integral [IsAlgClosed L] (hφ_int : φ.IsIntegral)
    (h_ker : ker φ ≤ ker ψ) :
    ∃ χ : C →ₐ[k] L, χ.comp φ = ψ := by
  -- Take a prime `q` of `C` over the kernel of `ψ`. Then `C ⧸ q` is an algebraic extension of the
  -- domain `A ⧸ ker ψ`, whose embedding in `L` extends.
  algebraize [φ.toRingHom, (kerLiftAlg ψ).toRingHom]
  have h_prime : (ker ψ).IsPrime := ker_isPrime ψ
  obtain ⟨q, -, hq_prime, hq⟩ :
      ∃ q ≥ (⊥ : Ideal C), q.IsPrime ∧ q.comap (algebraMap A C) = ker ψ :=
    exists_ideal_over_prime_of_isIntegral (ker ψ) (⊥ : Ideal C) h_ker
  have : q.LiesOver (ker ψ) := ⟨hq.symm⟩
  have h_alg : Algebra.IsAlgebraic (A ⧸ ker ψ) (C ⧸ q) :=
    (Algebra.IsIntegral.tower_top A).isAlgebraic
  have : Module.IsTorsionFree (A ⧸ ker ψ) L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (kerLiftAlg_injective ψ)
  have : Module.IsTorsionFree (A ⧸ ker ψ) (C ⧸ q) :=
    FaithfulSMul.to_isTorsionFree (A ⧸ ker ψ) (C ⧸ q)
  let χ : C ⧸ q →ₐ[A ⧸ ker ψ] L := IsAlgClosed.lift
  exact ⟨(χ.restrictScalars k).comp (toAlgHom k C _), AlgHom.ext fun a ↦ χ.commutes ⟦a⟧⟩

variable {Λ} {g : ι → L}

open IsIntegralClosure FiniteGaloisIntermediateField in
/-- Finitely many elements of an algebraically closed field, integral over a noetherian normal
domain `A` of characteristic zero, lie in a finite `A`-algebra `B` whose ring of invariants is
`A`. -/
lemma exists_galois_hull [Finite ι]
    [IsDomain A] [IsNoetherianRing A] [CharZero A] [IsIntegrallyClosed A]
    [IsAlgClosed L] [Algebra A L] [FaithfulSMul A L] (hg : ∀ i : ι, IsIntegral A (g i)) :
    ∃ B : CommAlgCat.{0} A, ∃ _ : Fintype Gal(B/A), ∃ j : B →ₐ[A] L, ∃ x : ι → B,
      Algebra.IsInvariant A B Gal(B/A) ∧ (algebraMap A B).Finite ∧ Injective j ∧ j ∘ x = g := by
  -- `B` is the integral closure of `A` in a finite Galois extension `N` of `Frac A` in `L` that
  -- contains the `g i`.
  let K : Type := FractionRing A
  let algebraKL : Algebra K L := FractionRing.liftAlgebra A L
  let g' (i : ι) : algebraicClosure K L := ⟨g i, (hg i).tower_top⟩
  let N : IntermediateField K (algebraicClosure K L) :=
    (FiniteGaloisIntermediateField.adjoin K (.range g')).toIntermediateField
  let B : Subalgebra A N := integralClosure A N
  have h_frac : IsFractionRing B N := isFractionRing_of_finite_extension A K N B
  let x (i : ι) : B :=
    ⟨⟨g' i, subset_adjoin K _ ⟨i, rfl⟩⟩, .of_map (algebraMap_injective N L) (hg i)⟩
  let j : B →ₐ[A] L := ⟨algebraMap B L, fun _ ↦ rfl⟩
  exact ⟨.of A B, .ofEquiv _ (galRestrict A K N B).toEquiv, j, x, isInvariant_of_isGalois' A K N B,
    finite_algebraMap.mpr (finite A K N B), algebraMap_injective B L, rfl⟩

/-- Elimination step of Noether normalisation. If the values of the linear forms `Λ` at `g` satisfy
a homogeneous relation `f`, and `a` is a point with `f a ≠ 0` and `a 0 ≠ 0`, then on the cone of `g`
a common zero with entries in a field `K` of the forms `Λ (j + 1) - (a (j + 1) / a 0) • Λ 0` is a
common zero of `Λ`. -/
lemma aeval_eq_zero_of_eliminated_forms {m : ℕ} {f : MvPolynomial (Fin (d + 1)) k}
    (hf : f.IsHomogeneous m) (h_rel : aeval (evalForms Λ g) f = 0) {a : Fin (d + 1) → k}
    (hfa : MvPolynomial.eval a f ≠ 0) (ha₀ : a 0 ≠ 0) {K : Type} [Field K] [Algebra k K] {x : ι → K}
    (hx : IsHomogeneousSolution k g x)
    (h_zero : ∀ j : Fin d, (Λ j.succ - (a j.succ / a 0) • Λ 0).val.aeval x = 0) (j : Fin (d + 1)) :
    (Λ j).val.aeval x = 0 := by
  -- the relation is a homogeneous equation of `g`, so it holds at `x`
  have h_relx : aeval (evalForms Λ x) f = 0 := by
    simpa [comp_aeval_apply, h_rel] using hx (hf.aeval _ fun j ↦ (Λ j).prop)
  -- the values of `Λ` at `x` are proportional to `a`
  obtain ⟨c, h_prop⟩ : ∃ c : K, evalForms Λ x = c • algebraMap k K ∘ a := by
    refine ⟨(a 0)⁻¹ • evalForms Λ x 0, funext (forall_fin_succ.mpr ?_)⟩
    simpa [ha₀, algebraMap_eq_smul_one, smul_smul, div_eq_mul_inv, sub_eq_zero] using h_zero
  -- by homogeneity `c ^ m * f a = 0`, so `c = 0`
  have h_pow : c ^ m * algebraMap k K (MvPolynomial.eval a f) = 0 := by
    simpa [h_prop, aeval_smul_of_isHomogeneous hf, aeval_algebraMap_apply] using h_relx
  have hc : c = 0 :=
    eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h_pow).resolve_right (by simpa using hfa))
  simpa [hc] using congrFun h_prop j

/-- If linear forms `Λ` have no non-trivial common zero on the cone of a finite tuple `g` over any
field, then a point `v` of the cone with `Λ v = φ ∘ p` has coordinates integral over the image of
`φ`. -/
lemma isIntegralElem_of_no_common_zero [Finite ι]
    (h_no_common_zero : ∀ {K : Type} [Field K] [Algebra k K] (v : ι → K),
      IsHomogeneousSolution k g v →
      (∀ j : Fin (d + 1), (Λ j).val.aeval v = (0 : K)) → v = 0)
    {K R : Type} [Field K] [Algebra k K] [CommRing R] [Algebra k R] (φ : R →ₐ[k] K)
    (p : Fin (d + 1) → R) (v : ι → K) (hv : IsHomogeneousSolution k g v)
    (h_val : evalForms Λ v = φ ∘ p) (i : ι) :
    φ.IsIntegralElem (v i) := by
  -- Show `v i ∈ V` for each valuation ring `V` that contains the image of `φ`. Divide `v` by a
  -- coordinate `v j` of largest valuation. If `v j ∉ V`, the quotient reduces to a common zero
  -- of `Λ` over the residue field whose `j`-th coordinate is `1`, against `h_no_common_zero`.
  refine isIntegralElem_of_valuationSubring fun V hV ↦ ?_
  -- largest valuation says that each `v l` is a multiple of `v j` by some `x l ∈ V`
  have h_nonempty : Nonempty ι := ⟨i⟩
  obtain ⟨j, hj⟩ : ∃ j : ι, ∀ l : ι, ∃ x : V, x • v j = v l := exists_max (V.valuation ∘ v)
  choose x hx using hj
  algebraize [(φ.toRingHom.codRestrict V hV).comp (algebraMap k _)]
  let incl : V →ₐ[k] K := AlgHom.mk V.subtype φ.commutes'
  suffices h_vj_le : V.valuation (v j) ≤ 1 by
    rw [← hx i]
    exact mul_mem (x i).prop ((V.valuation_le_one_iff _).mp h_vj_le)
  by_contra! h_big
  have hvj : v j ≠ 0 := ne_zero_of_map h_big.ne_zero
  have h_quot : incl ∘ x = (v j)⁻¹ • v :=
    (eq_inv_smul_iff₀ hvj).mpr <| funext fun l ↦ (mul_comm _ _).trans (hx l)
  let red : V →ₐ[k] IsLocalRing.ResidueField V :=
    IsScalarTower.toAlgHom k V (IsLocalRing.ResidueField V)
  have h_res {y : V} : red y = 0 ↔ V.valuation y < 1 := by simp [red, V.valuation_lt_one_iff]
  -- the reduction of `x` lies on the cone, since `incl ∘ x` is a multiple of `v`
  have h_ker (r : V) (hr : incl r = 0) : red r = 0 := by
    rw [show r = 0 from Subtype.ext hr, map_zero]
  have h_incl : IsHomogeneousSolution k g (incl ∘ x) := by
    rw [h_quot]
    exact hv.smul (AlgHom.id k K) (v j)⁻¹
  have h_cone : IsHomogeneousSolution k g (red ∘ x) := .of_ker incl red h_ker h_incl
  -- `Λ l x = (v j)⁻¹ * φ (p l)` has valuation less than one
  have h_zero (l : Fin (d + 1)) : (Λ l).val.aeval (red ∘ x) = 0 := by
    have h_incl_l : (((Λ l).val.aeval x : V) : K) = (v j)⁻¹ * φ (p l) := by
      calc (((Λ l).val.aeval x : V) : K) = evalForms Λ (incl ∘ x) l :=
            comp_aeval_apply x incl (Λ l).val
        _ = ((v j)⁻¹ • evalForms Λ v) l := by rw [h_quot, evalForms_smul]
        _ = (v j)⁻¹ * φ (p l) := by simp [h_val]
    have h_le : V.valuation (φ (p l)) ≤ 1 := V.valuation_le_one ⟨φ (p l), hV (p l)⟩
    have h_lt_one : V.valuation ((v j)⁻¹ * φ (p l)) < 1 := by
      simpa [inv_mul_lt_one₀ h_big.pos] using h_le.trans_lt h_big
    -- `Λ l (red ∘ x) = red (Λ l x)`
    refine (comp_aeval_apply x red (Λ l).val).symm.trans ?_
    rw [h_res, h_incl_l]
    exact h_lt_one
  have h_lt : V.valuation (x j) < 1 := h_res.mp (congrFun (h_no_common_zero _ h_cone h_zero) j)
  -- but `x j = (v j)⁻¹ * v j = 1`
  have h_xj : ((x j : V) : K) = 1 := (congrFun h_quot j).trans (inv_mul_cancel₀ hvj)
  simp [h_xj] at h_lt

/-- Noether normalisation. Let `g` be a non-zero tuple, indexed by a finite type `ι`, in a field `L`
over a field `k` of characteristic zero. Then there are linear forms `Λ₀, …, Λ_d` over `k` with
`Λ₀(g) ≠ 0` that form a Noether normalisation of `u • g` for every unit `u` of `L`. This means the
values `Λ_j(u • g)` satisfy no non-zero homogeneous polynomial relation over `k`, and every
field-valued point `v` on the cone of `u • g` is integral over any image of a `k`-algebra that
contains the values `Λ_j(v)`. -/
lemma exists_isNoetherNormalization [CharZero k] [Finite ι] (hg : g ≠ 0) :
    ∃ (d : ℕ) (Λ : Fin (d + 1) → homogeneousSubmodule ι k 1),
      evalForms Λ g 0 ≠ 0 ∧ ∀ u : Lˣ, IsNoetherNormalization (k := k) (d := d) Λ (u • g) := by
  -- Start from the coordinates, linear forms without a non-trivial common zero on the cone of
  -- `g`. While the values at `g` satisfy a homogeneous relation, one form can be dropped; once
  -- they satisfy none, the forms are a Noether normalisation.
  obtain ⟨n, Λ, h_base⟩ :
      ∃ (n : ℕ) (Λ : Fin n → homogeneousSubmodule ι k 1),
        ∀ {K : Type} [Field K] [Algebra k K] (v : ι → K), IsHomogeneousSolution k g v →
          (∀ j : Fin n, (Λ j).val.aeval v = (0 : K)) → v = 0 := by
    refine ⟨Nat.card ι, fun j ↦ ⟨X ((equivFin ι).symm j), isHomogeneous_X k _⟩,
      fun v _ h_zero ↦ funext fun i ↦ ?_⟩
    simpa using h_zero (equivFin ι i)
  induction n with
  | zero => cases hg (h_base g .refl nofun)
  | succ n ih =>
    by_cases h_ind : IsHomogeneousSolution k (evalForms Λ g) (X (R := k))
    · -- no relation: in particular `X 0` is none, so `Λ 0` does not vanish at `g`
      have h_ne : evalForms Λ g 0 ≠ 0 := by simpa using h_ind (isHomogeneous_X k 0)
      refine ⟨n, Λ, h_ne, fun u ↦ ⟨fun m F hF h_rel ↦ h_ind hF ?_, fun φ p v hv ↦ ?_⟩⟩
      · -- no relation at `u • g` either: it would be one at `g`, up to a power of `u`
        simpa [u.smul_def, aeval_smul_of_isHomogeneous hF] using h_rel
      · -- a point of the cone of `u • g` lies on the cone of `g`
        have hv_g : IsHomogeneousSolution k g v := by grind [IsHomogeneousSolution, Units.smul_def]
        exact isIntegralElem_of_no_common_zero h_base φ p v hv_g
    · obtain ⟨m, f, hf, h_rel, hf₀⟩ : ∃ (m : ℕ) (f : MvPolynomial (Fin (n + 1)) k),
          f.IsHomogeneous m ∧ aeval (evalForms Λ g) f = 0 ∧ f ≠ 0 := by
        simpa [IsHomogeneousSolution, aeval_X_left_apply] using h_ind
      -- `k` is infinite, so the non-zero polynomial `f * X 0` has a non-zero value
      obtain ⟨a, ha⟩ : ∃ a : Fin (n + 1) → k, MvPolynomial.eval a (f * X 0) ≠ 0 := by
        by_contra! h_all
        exact mul_ne_zero hf₀ (X_ne_zero 0) (MvPolynomial.funext fun a ↦ by simpa using h_all a)
      obtain ⟨hfa, ha₀⟩ : MvPolynomial.eval a f ≠ 0 ∧ a 0 ≠ 0 := by simpa [not_or] using ha
      -- eliminate `Λ 0`: the `n` new forms still have no non-trivial common zero on the cone
      exact ih (fun j ↦ Λ j.succ - (a j.succ / a 0) • Λ 0) fun x hx h_zero ↦
        h_base x hx (aeval_eq_zero_of_eliminated_forms hf h_rel hfa ha₀ hx h_zero)

/-- Let `A` be the ring of invariants of the finite group of `A`-automorphisms of `B`. Two maps
of `k`-algebras from `B` to a field (`k` of characteristic zero) that agree on `A` differ by such an
automorphism. -/
lemma exists_algEquiv_of_comp_eq [CharZero k] [Algebra A B] [IsScalarTower k A B] [Fintype Gal(B/A)]
    (hinv : Algebra.IsInvariant A B Gal(B/A)) {χ ψ : B →ₐ[k] L}
    (h_agree : χ.comp (toAlgHom k A B) = ψ.comp (toAlgHom k A B)) :
    ∃ τ : Gal(B/A), ∀ a : B, ψ a = χ (τ a) := by
  -- A vector space over the infinite field `k` is not a finite union of proper subspaces, so it
  -- is enough to find, for each `a`, some `τ` with `ψ a = χ (τ a)`.
  suffices hcover : ∀ a : B, ∃ τ : Gal(B/A), ψ a = χ (τ a) by
    have h_mem (a : B) :
        a ∈ ⋃ τ : Gal(B/A), ((ψ.equalizer (χ.comp (τ.restrictScalars k))).toSubmodule : Set B) := by
      simpa using hcover a
    simpa [Submodule.eq_top_iff'] using Subspace.exists_eq_top_of_iUnion_eq_univ
      (p := fun τ : Gal(B/A) ↦ (ψ.equalizer (χ.comp (τ.restrictScalars k))).toSubmodule)
      (Set.eq_univ_of_forall h_mem)
  intro a
  -- The polynomial `∏ τ, (X - τ a)` comes from some `P` over `A`.
  obtain ⟨P, hP : P.map (algebraMap A B) = MulSemiringAction.charpoly Gal(B/A) a⟩ :
    MulSemiringAction.charpoly (B ≃ₐ[A] B) a ∈ Polynomial.lifts (algebraMap A B) :=
    hinv.charpoly_mem_lifts (b := a)
  have hroot (θ : B →ₐ[k] L) :
      P.eval₂ (θ.comp (toAlgHom k A B)).toRingHom (ψ a) = 0 ↔ ∃ τ : Gal(B/A), ψ a = θ (τ a) := by
    rw [show (θ.comp (toAlgHom k A B)).toRingHom = θ.toRingHom.comp (algebraMap A B) from rfl,
      ← P.eval₂_map, hP, MulSemiringAction.charpoly_eq, Polynomial.eval₂_finsetProd,
      prod_eq_zero_iff]
    simp [sub_eq_zero]
  -- `ψ a` is a root of the image of `P` under `ψ`, which is also its image under `χ`.
  rw [← hroot χ, h_agree, hroot ψ]
  exact ⟨1, rfl⟩

/-- Let `t` be transcendental over `L`, `j : B → Ω` a map of `k`-algebras with zero kernel, and `b`
a tuple over `B` with `j ∘ b = t • w` for a tuple `w` of elements of `Ω` integral over `L`. Every
polynomial relation of `b` holds for `u • φ ∘ b`, for every map `φ` of `k`-algebras from `B` to a
field `K` and every `u`: the relation splits into homogeneous relations of `w`, which `b`
satisfies. -/
private lemma ker_aeval_le_ker_aeval_smul_of_transcendental {κ B K Ω : Type} [CommRing B]
    [Algebra k B] [Field K] [Algebra k K] [Field Ω] [Algebra L Ω] [Algebra k Ω]
    [IsScalarTower k L Ω] {t : Ω} (ht : Transcendental L t) (j : B →ₐ[k] Ω)
    (hj_ker : ∀ r : B, j r = 0 → r = 0) (b : κ → B) (w : κ → integralClosure L Ω)
    (hw : t • toAlgHom k (integralClosure L Ω) Ω ∘ w = j ∘ b) (φ : B →ₐ[k] K) (u : K) :
    ker (aeval (R := k) b) ≤ ker (aeval (R := k) (u • φ ∘ b)) := by
  have h_tw : IsHomogeneousSolution k w (t • toAlgHom k (integralClosure L Ω) Ω ∘ w) :=
    .smul _ t .refl
  rw [hw] at h_tw
  have hwb : IsHomogeneousSolution k w b :=
    .of_ker j (AlgHom.id k B) (fun r hr ↦ by rw [hj_ker r hr, map_zero]) h_tw
  refine fun F hF ↦ (hwb.smul φ u).aeval_eq_zero_of_transcendental ht.integralClosure ?_
  change aeval (t • toAlgHom k (integralClosure L Ω) Ω ∘ w) F = 0
  rw [hw]
  exact (comp_aeval_apply b j F).symm.trans (by rw [RingHom.mem_ker.mp hF, map_zero])

/-- Let `f : k[X₀, …, X_d] → B` be finite and `b` a family of tuples over `B` such that `Λ` takes
the tuple `b σ₀` to `f ∘ X`. Then `aeval b` is integral: composed with the substitution of the
forms `Λ` in the variables `(σ₀, i)`, it is `f`. -/
private lemma isIntegral_aeval_of_evalForms_eq {G B : Type} [CommRing B] [Algebra k B]
    (f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B) (hf_fin : f.toRingHom.Finite) (b : G → ι → B)
    (σ₀ : G) (hΛb : evalForms Λ (b σ₀) = f ∘ X) :
    (aeval (R := k) ↿b).IsIntegral := by
  let θ : MvPolynomial (Fin (d + 1)) k →ₐ[k] MvPolynomial (G × ι) k :=
    aeval fun l ↦ rename (Prod.mk σ₀) (Λ l).val
  have hfactor : (aeval (R := k) ↿b).comp θ = f := by
    refine algHom_ext fun l ↦ ?_
    simp only [θ, AlgHom.comp_apply, aeval_X, aeval_rename]
    exact congrFun hΛb l
  refine .tower_top θ.toRingHom _ ?_
  change ((aeval (R := k) ↿b).comp θ).toRingHom.IsIntegral
  rw [hfactor]
  exact hf_fin.to_isIntegral

/-- Let `t` be transcendental over `L`, `j : B → Ω` a map of `k`-algebras with zero kernel, and each
tuple `t⁻¹ • j ∘ b σ` integral over `L`. Let `B` be finite over `k[X₀, …, X_d]` by `f`, with
`Λ` taking `b σ₀` to `f ∘ X`. Then for every map `φ` from `B` to an algebraically closed field
and every `u`, some map `χ` from `B` has `χ ∘ b σ = u • φ ∘ b σ` for all `σ`. -/
private lemma exists_algHom_comp_eq_smul {G B K Ω : Type} [CommRing B] [Algebra k B] [Field K]
    [IsAlgClosed K] [Algebra k K] [Field Ω] [Algebra L Ω] [Algebra k Ω] [IsScalarTower k L Ω]
    {t : Ω} (ht : Transcendental L t) (ht_ne : t ≠ 0) (j : B →ₐ[k] Ω)
    (hj_ker : ∀ r : B, j r = 0 → r = 0) (b : G → ι → B)
    (hw_int : ∀ (σ : G) (i : ι), IsIntegral L ((t⁻¹ • j ∘ b σ) i))
    (f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B) (hf_fin : f.toRingHom.Finite) (σ₀ : G)
    (hΛb : evalForms Λ (b σ₀) = f ∘ X) (φ : B →ₐ[k] K) (u : K) :
    ∃ χ : B →ₐ[k] K, ∀ σ : G, χ ∘ b σ = u • φ ∘ b σ := by
  -- `j ∘ b = t • w` with `w` integral over `L`, so every relation of `b` holds for `u • φ ∘ b`;
  -- as `B` is integral over the polynomials `Λ` in the `b σ₀ i`, `χ` extends `u • φ ∘ b`.
  let w : G × ι → integralClosure L Ω := fun (σ, i) ↦ ⟨_, hw_int σ i⟩
  have hw : t • toAlgHom k (integralClosure L Ω) Ω ∘ w = j ∘ ↿b := by
    funext ⟨σ, i⟩
    exact mul_inv_cancel_left₀ ht_ne _
  have hker : ker (aeval (R := k) ↿b) ≤ ker (aeval (R := k) (u • φ ∘ ↿b)) :=
    ker_aeval_le_ker_aeval_smul_of_transcendental ht j hj_ker ↿b w hw φ u
  obtain ⟨χ, hχ⟩ : ∃ χ : B →ₐ[k] K, χ.comp (aeval ↿b) = aeval (u • φ ∘ ↿b) :=
    exists_algHom_comp_eq_of_integral _ _ (isIntegral_aeval_of_evalForms_eq f hf_fin b σ₀ hΛb) hker
  refine ⟨χ, fun σ ↦ funext fun i ↦ ?_⟩
  simpa [Function.HasUncurry.uncurry] using DFunLike.congr_fun hχ (X (σ, i))

variable [CharZero k] [Finite ι]

/-- The Galois closure of a Noether normalisation `Λ` of a finite tuple `g`: a finite group `G`, a
finite injective map `f : k[X₀, …, X_d] → B` of `k`-algebras and tuples `b σ` over `B`, `σ ∈ G`, on
the cone of `g`, that `Λ` takes to the variables and that `G` permutes up to proportionality. -/
structure IsNoetherNormalization.GaloisClosure (Λ : Fin (d + 1) → homogeneousSubmodule ι k 1)
    (g : ι → L) where
  /-- The finite group that permutes the tuples `b σ`. -/
  G : GrpCat.{0}
  /-- The algebra over `k[X₀, …, X_d]` in which the tuples lie. -/
  B : CommAlgCat k
  /-- The group `G` is finite. -/
  fintype : Fintype G
  /-- The map from `k[X₀, …, X_d]`. -/
  f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B
  /-- The tuples, indexed by `G`. -/
  b : G → ι → B
  /-- Each `b σ` lies on the cone of `g`. -/
  isHomogeneousSolution (σ : G) : IsHomogeneousSolution k g (b σ)
  /-- The forms `Λ` take each `b σ` to the variables: `Λ j (b σ) = f (X j)`. -/
  evalForms_eq (σ : G) : evalForms Λ (b σ) = f ∘ X
  /-- The map `f` is finite. -/
  finite : f.toRingHom.Finite
  /-- The map `f` is injective. -/
  injective : Injective f
  /-- If `φ`, `ψ` map `B` to an algebraically closed field and `ψ (f (X j)) = u φ (f (X j))` for
  all `j`, then for some `τ ∈ G`, `ψ (b σ) = u φ (b (τ σ))` for all `σ`. -/
  exists_shift {K : Type} [Field K] [IsAlgClosed K] [Algebra k K] (φ ψ : B →ₐ[k] K) (u : K) :
    u • φ ∘ f ∘ X = ψ ∘ f ∘ X → ∃ τ : G, ∀ σ : G, ψ ∘ b σ = u • φ ∘ b (τ * σ)

/-- A Noether normalisation `Λ` of a finite tuple `g` with entries in a field `L`, over a field `k`
of characteristic zero, has a Galois closure
(`New.Variety.CutsOutLocus.IsNoetherNormalization.GaloisClosure`). -/
lemma IsNoetherNormalization.nonempty_galoisClosure (hΛ : IsNoetherNormalization Λ g) :
    Nonempty (IsNoetherNormalization.GaloisClosure Λ g) := by
  -- Take `t` transcendental over `L`. The values of `Λ` at `t • g` are algebraically independent,
  -- so they embed `A = k[X]` in an algebraically closed field `Ω`, and `t • g` is integral over
  -- `A`. `B` is a Galois hull of `t • g` over `A` and the `b σ` are the conjugates of `t • g`.
  obtain ⟨h_no_rel, h_integral⟩ := hΛ
  let Ω : Type := AlgebraicClosure (RatFunc L)
  let inc : L →ₐ[k] Ω := toAlgHom k L Ω
  let A : Type := MvPolynomial (Fin (d + 1)) k
  obtain ⟨t, ht⟩ : ∃ t : Ω, Transcendental L t :=
    ⟨_, (transcendental_algebraMap_iff (algebraMap_injective _ Ω)).mpr RatFunc.transcendental_X⟩
  have ht_ne : t ≠ 0 := by simpa using not_exists.mp ht .X
  have h_tg : IsHomogeneousSolution k g (t • inc ∘ g) := .smul inc t .refl
  algebraize [(aeval (R := k) (evalForms Λ (t • inc ∘ g))).toRingHom]
  -- The values of `Λ` at `t • g` are `t` times those at `g`, which satisfy no nonzero homogeneous
  -- relation. (`using!`: the algebra instance comes from `algebraize`.)
  have h_faithful : FaithfulSMul A Ω := by
    refine (faithfulSMul_iff_algebraMap_injective A Ω).mpr
      (algebraicIndependent_iff.mpr fun F ↦ ?_)
    simpa [aeval_X_left_apply] using! h_no_rel.aeval_eq_zero_of_transcendental ht
  have h_forms_X : evalForms Λ (t • inc ∘ g) = aeval (R := k) (evalForms Λ (t • inc ∘ g)) ∘ X :=
    funext fun l ↦ (aeval_X _ l).symm
  have h_int (i : ι) : IsIntegral A ((t • inc ∘ g) i) := h_integral (aeval _) X _ h_tg h_forms_X i
  -- `incA : B → Ω` is an injective `A`-algebra map with `incA ∘ x = t • inc ∘ g`
  obtain ⟨B, fintypeGal, incA, x, hinv, hfin, h_incA_inj, h_incA_x⟩ := exists_galois_hull h_int
  algebraize [(algebraMap A B).comp C]
  let j : B →ₐ[k] Ω := incA.restrictScalars k
  let f : A →ₐ[k] B := toAlgHom k A B
  have hjf : j ∘ f ∘ X = evalForms Λ (t • inc ∘ g) :=
    funext fun i ↦ (incA.commutes _).trans (aeval_X _ i)
  let b (σ : Gal(B/A)) : ι → B := σ.toAlgHom.restrictScalars k ∘ x
  -- `h_incA_x` with `j`, the form that the rewrites below need
  have h_jx : j ∘ x = t • inc ∘ g := h_incA_x
  have hj_ker : ∀ r : B, j r = 0 → r = 0 := fun r hr ↦ h_incA_inj (hr.trans (map_zero incA).symm)
  have hb (σ : Gal(B/A)) : IsHomogeneousSolution k g (b σ) :=
    .of_ker j _ (fun r hr ↦ by rw [hj_ker r hr, map_zero]) (by rwa [h_jx])
  have hx_forms : evalForms Λ x = f ∘ X := by
    apply h_incA_inj.comp_left
    calc incA ∘ evalForms Λ x = evalForms Λ (j ∘ x) := (evalForms_map Λ j x).symm
      _ = incA ∘ f ∘ X := by rw [h_jx]; exact hjf.symm
  -- `σ` fixes the image of `A`
  have hΛb (σ : Gal(B/A)) : evalForms Λ (b σ) = f ∘ X := by
    rw [evalForms_map, hx_forms]
    exact funext fun i ↦ σ.commutes (X i)
  have hf_inj : Injective f := .of_comp (f := incA) fun a a' h ↦
    algebraMap_injective A Ω <| by simpa [f] using h
  refine ⟨{
    G := .of Gal(B/A), B := .of k B, fintype := inferInstance, f := f, b := b,
    isHomogeneousSolution := hb, evalForms_eq := hΛb, finite := hfin, injective := hf_inj,
    exists_shift := fun {K _ _ _} φ ψ u hu ↦ ?_ }⟩
  -- Dividing by `t`: `t⁻¹ • j ∘ b σ` is integral over `L`, since `Λ` has values in `L` there.
  have hw_int (σ : Gal(B/A)) (i : ι) : IsIntegral L ((t⁻¹ • j ∘ b σ) i) := by
    refine h_integral inc (evalForms Λ g) _ ((hb σ).smul j t⁻¹) ?_ i
    simp [hΛb, hjf, ht_ne]
  -- So scaling `φ ∘ b` by `u` is induced by a map `χ` on `B`; it agrees with `ψ` on `A`.
  obtain ⟨χ, hχb⟩ : ∃ χ : B →ₐ[k] K, ∀ σ : Gal(B/A), χ ∘ b σ = u • φ ∘ b σ :=
    exists_algHom_comp_eq_smul ht ht_ne j hj_ker b hw_int f hfin 1 (hΛb 1) φ u
  have hχf : χ ∘ f ∘ X = u • φ ∘ f ∘ X := by
    simpa [hΛb] using congrArg (evalForms Λ) (hχb 1)
  have h_agree : χ.comp f = ψ.comp f := algHom_ext (congrFun (hχf.trans hu))
  obtain ⟨τ, hτ⟩ : ∃ τ : Gal(B/A), ∀ a : B, ψ a = χ (τ a) := exists_algEquiv_of_comp_eq hinv h_agree
  refine ⟨τ, fun σ ↦ ?_⟩
  rw [← hχb (τ * σ)]
  exact funext fun i ↦ hτ (b σ i)

/-- The Galois closure of a Noether normalisation `Λ` of a finite tuple `g` with entries in a field
`L`, over a field `k` of characteristic zero. There are a finite group `G`, a map of `k`-algebras
`f : k[X₀, …, X_d] → B` and tuples `b σ` over `B`, `σ ∈ G`, such that: (a) each `b σ` lies on the
cone of `g`, and `Λ j` takes the value `f (X j)` at it; (b) `f` is finite and injective; (c) if `φ`,
`ψ` map `B` to an algebraically closed field and `ψ (f (X j)) = u φ (f (X j))` for all `j`, then for
some `τ ∈ G` we have `ψ (b σ) = u φ (b (τ σ))` for all `σ`. -/
lemma IsNoetherNormalization.exists_galois_closure (hΛ : IsNoetherNormalization Λ g) :
    ∃ (G : GrpCat.{0}) (B : CommAlgCat k) (_ : Fintype G)
        (f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B)
        (b : G → ι → B),
      -- (a)
      (∀ σ : G, IsHomogeneousSolution k g (b σ) ∧ evalForms Λ (b σ) = f ∘ X) ∧
      -- (b)
      f.toRingHom.Finite ∧ Injective f ∧
      -- (c)
      ∀ {K : Type} [Field K] [IsAlgClosed K] [Algebra k K] (φ ψ : B →ₐ[k] K) (u : K),
        u • φ ∘ f ∘ X = ψ ∘ f ∘ X → ∃ τ : G, ∀ σ : G, ψ ∘ b σ = u • φ ∘ b (τ * σ) := by
  obtain ⟨⟨G, B, fintypeG, f, b, hb_hom, hb_lv, h_fin, h_inj, h_conj⟩⟩ :=
    hΛ.nonempty_galoisClosure
  exact ⟨G, B, fintypeG, f, b, fun σ ↦ ⟨hb_hom σ, hb_lv σ⟩, h_fin, h_inj, h_conj⟩

end New.Variety.CutsOutLocus

end NoetherNormalization

/-!
## Homogeneous coordinates of points of an embedded variety

Points of a scheme Y over Spec R with values in k-algebras A (`New.Variety.PointsIn`) are described
by homogeneous coordinates for a line bundle L that embeds Y (`New.LineBundle.IsProjEmbedding`,
finite index set ι).
-/

namespace New.Variety

open CategoryTheory Function AlgebraicGeometry MvPolynomial CutsOutLocus CommAlgCat ProjSpace Ideal
  Over Category

variable {k ι : Type} {F : Type} [Field k]
  {R : CommRingCat} [Algebra R.carrier k] {Y : Over (Spec R)}
  (L : LineBundle Y.left ι) {A B : CommAlg k} (x x' : PointsIn Y A)
  (v : ι → A) [Field F] [Algebra k F] [hL : Fact (L.IsProjEmbedding Y.hom)]

/-- The vector v in A^ι is a vector of homogeneous coordinates, for L, of the A-point x of Y,
and some coordinate v_i is a unit. -/
abbrev IsCoordsWithUnit : Prop := L.IsHomogeneousCoords x.down.left v ∧ ∃ i : ι, IsUnit (v i)

/-- If étale charts of dimension d cover Y (`IsChartCovered`), a point x over a field comes, along
some κ, from the universal point of such a chart that has coordinates with a unit entry. -/
lemma IsCoordsWithUnit.exists_chart_coords (hK : IsField A) {d : ℕ}
    [IsChartCovered d (algPointsOf k R Y)] :
    ∃ (c : EtaleChart d (algPointsOf k R Y)) (κ : c.coordRing ⟶ A) (w : ι → c.coordRing),
      PointsIn.map κ c.point = x ∧ IsCoordsWithUnit L c.point w := by
  -- `x` lands in some `L.opens i`. Shrink a chart around `x` into that open set; there the
  -- functions `L.transition i j` are homogeneous coordinates whose `i`-th entry is a unit.
  let fieldA : Field A := hK.toField
  obtain ⟨i, hi⟩ : ∃ i : ι, LandsIn x.down.left (L.opens i) := L.exists_landsIn x.down.left
  -- The points that land in `L.opens i` form an open subfunctor `U`, which contains `x`.
  let U : Subfunctor (algPointsOf k R Y) :=
    ⟨fun _ ↦ {y | LandsIn y.down.left (L.opens i)}, by tauto⟩
  -- Along `ψ : A ⟶ B` the point `PointsIn.map ψ y` is `Spec ψ` followed by `y`.
  have h_map_left : ∀ (A B : CommAlg k) (ψ : A ⟶ B) (y : PointsIn Y A),
      (PointsIn.map ψ y).down.left = specMap ψ.hom ≫ y.down.left := by tauto
  have hU : IsOpenSubfunctor U :=
    isOpenSubfunctor_of_landsIn (fun y ↦ y.down.left) h_map_left U fun _ _ ↦ .rfl
  obtain ⟨c, ⟨κ, hκ⟩, hc⟩ := hU.exists_mem_locus_and_point_mem hK hi
  have h_coords : L.IsHomogeneousCoords c.point.down.left
      (fun j : ι ↦ L.transition i j _ c.point.down.left) :=
    hL.out.isLinearSystem.isHomogeneousCoords_transition hc
  exact ⟨c, _, fun j ↦ L.transition i j _ c.point.down.left, hκ, h_coords, i,
    L.isUnit_transition hc hc⟩

variable {L x x' v} {ξ : PointsIn Y (of k F)} {g : ι → of k F} {i : ι}

omit [Fact (L.IsProjEmbedding Y.hom)] in
/-- Two vectors of coordinates with a unit entry of the same point `x` differ by a unit of `A`. -/
lemma IsCoordsWithUnit.exists_unit_smul_eq {w : ι → A} (hv : IsCoordsWithUnit L x v)
    (hw : IsCoordsWithUnit L x w) :
    ∃ u : Aˣ, u • v = w := by
  -- The unit is `w i / v i`, for a coordinate `v i` that is a unit; `w i` is a unit too, as `x`
  -- lands in `L.opens i`.
  obtain ⟨hv_coords, i, hvi⟩ := hv
  obtain ⟨hv_lands_iff, hv_transition⟩ := hv_coords i
  obtain ⟨hw_lands_iff, hw_transition⟩ := hw.left i
  have hwi : IsUnit (w i) := hw_lands_iff.mp (hv_lands_iff.mpr hvi)
  refine ⟨(hvi.ringInverse.mul hwi).unit, funext fun j ↦ ?_⟩
  -- Both `v j / v i` and `w j / w i` are the value of the chart function `L.transition i j` at `x`.
  have h_chart : v j * Ring.inverse (v i) = w j * Ring.inverse (w i) :=
    (hv_transition j hvi).symm.trans (hw_transition j hwi)
  calc Ring.inverse (v i) * w i * v j = v j * Ring.inverse (v i) * w i := by ring
    _ = w j := by rw [h_chart, Ring.inverse_mul_cancel_right _ _ hwi]

/-- If `v` is a vector of coordinates with a unit entry of `x`, `φ : A ⟶ B` is a map of
`k`-algebras and `u` is a unit of `B`, then `u • φ ∘ v` is a vector of coordinates with a unit entry
of the image of `x` under `φ`. -/
lemma IsCoordsWithUnit.map_unit_smul (hv : IsCoordsWithUnit L x v) (φ : A ⟶ B) (u : Bˣ) :
    IsCoordsWithUnit L (x.map φ) (u • φ ∘ v) := by
  obtain ⟨h_lifts, i, hi⟩ := hv
  -- the coordinates map along `φ` and scale by `u`; the entry `i` stays a unit
  have h_coords : L.IsHomogeneousCoords (x.map φ).down.left (u • φ ∘ v) :=
    (h_lifts.map hL.out.isLinearSystem hi _).smul u.isUnit
  exact ⟨h_coords, i, u.isUnit.mul (hi.map φ.hom)⟩

lemma IsCoordsWithUnit.comp (h : IsCoordsWithUnit L x v) (φ : A ⟶ B) :
    IsCoordsWithUnit L (x.map φ) (φ ∘ v) := by
  simpa using h.map_unit_smul φ 1

/-- Two `A`-points of `Y` with the same vector `v` of coordinates with a unit entry are equal. -/
lemma IsCoordsWithUnit.ext (h : IsCoordsWithUnit L x v) (H : IsCoordsWithUnit L x' v) :
    x = x' := by
  -- `L` is an embedding: two points over the base with the same coordinates agree.
  obtain ⟨hx_coords, i, hvi⟩ := h
  obtain ⟨hx'_coords, -⟩ := H
  have h_base : x.down.left ≫ Y.hom = x'.down.left ≫ Y.hom :=
    (Over.w x.down).trans (Over.w x'.down).symm
  have h_lands : LandsIn x.down.left (L.opens i) := ((hx_coords i).left).mpr hvi
  have h_left : x.down.left = x'.down.left :=
    hL.out.eq_of_isHomogeneousCoords h_base hx_coords hx'_coords ⟨i, h_lands⟩
  exact ULift.down_injective (OverMorphism.ext h_left)

/-! ### Points over a field: descent, spreading out and specialisation -/

variable [Finite ι]

/-- Descent. Let ξ be a point over a field F with coordinates g, and φ : A → F injective. If
g = g_i φ(v) for a vector v over A, then ξ comes from a point over A with coordinates v. -/
lemma IsCoordsWithUnit.exists_descend_of_injective (hξ : IsCoordsWithUnit L ξ g) (φ : A ⟶ of k F)
    (φ_inj : Function.Injective φ) (h_coord : g i • φ ∘ v = g) :
    ∃ x : PointsIn Y A, IsCoordsWithUnit L x v ∧ ξ = x.map φ := by
  -- View `Y` as a closed subscheme of projective space. The vector `v` gives a point `t` of
  -- projective space over `A` with image `ξ` under `φ`; as `φ` is injective, `t` lies in `Y`.
  -- Some entry `g l = g i * φ (v l)` is a unit, so `g i` is a unit; then `g i * φ (v i) = g i`
  -- gives `v i = 1`.
  obtain ⟨l, hgl_unit⟩ : ∃ l : ι, IsUnit (g l) := hξ.right
  have hgi_unit : IsUnit (g i) := by
    rw [← congrFun h_coord l] at hgl_unit
    exact isUnit_of_mul_isUnit_left hgl_unit
  have hvi : v i = 1 :=
    (map_eq_one_iff _ φ_inj).mp (hgi_unit.mul_eq_left.mp (congrFun h_coord i))
  have hv : IsUnit (v i) := by simp [hvi]
  obtain ⟨j, _, hj, rfl⟩ := hL.out.exists_isClosedImmersion
  obtain ⟨t, ht_over, ht⟩ := exists_isHomogeneousCoords (Opposite.unop ((specAlg k R).obj A)).hom hv
  -- `ξ` and the image of `t` both have coordinates `g` and lie over the same point of `Spec R`.
  have h_image : ξ.down.left ≫ j = Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ t := by
    have h_coords_image : LineBundle.IsHomogeneousCoords ((hyperplaneBundle ι).pull Limits.prod.fst)
        (Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ t) g :=
      h_coord ▸ (ht.map (isLinearSystem_hyperplaneBundle.pull _) hv _).smul hgi_unit
    refine isProjEmbedding_projSpace.eq_of_isHomogeneousCoords ?_ hξ.left h_coords_image
      (LineBundle.exists_landsIn _ _)
    let u := ((specAlg k R).map φ).unop
    change (ξ.down.left ≫ j) ≫ Limits.prod.snd = (u.left ≫ t) ≫ Limits.prod.snd
    calc
      _ = ξ.down.left ≫ Y.hom :=
        (assoc ..).trans (congrArg (ξ.down.left ≫ ·) hj)
      _ = u.left ≫ (t ≫ Limits.prod.snd) :=
        ξ.down.w.trans (u.w.symm.trans (congrArg (u.left ≫ ·) ht_over).symm)
      _ = _ := (assoc ..).symm
  -- The ideal `J` cutting out the locus where `t` lies in `Y` is killed by `φ`, hence is zero.
  obtain ⟨J, -, hJ⟩ := exists_ideal_le_ker_iff_factors j t
  have h_ker_le : RingHom.ker φ.hom.toRingHom ≤ RingHom.ker (RingHom.id A) :=
    ((RingHom.injective_iff_ker_eq_bot _).mp φ_inj).le.trans bot_le
  have hJ0 : J ≤ RingHom.ker (RingHom.id A) :=
    ((hJ φ.hom.toRingHom).mpr ⟨ξ.down.left, h_image⟩).trans h_ker_le
  obtain ⟨x, rfl⟩ : ∃ x : Spec (CommRingCat.of A) ⟶ Y.left, x ≫ j = t := by
    simpa using (hJ (RingHom.id A)).mp hJ0
  -- `x` lies over `Spec R`, since `x ≫ j` does
  have h_x_over : x ≫ Y.hom = (Opposite.unop ((specAlg k R).obj A)).hom := by
    rw [← hj, ← Category.assoc]
    exact ht_over
  let y : PointsIn Y A := ⟨homMk x h_x_over⟩
  have hx : IsCoordsWithUnit (((hyperplaneBundle ι).pull Limits.prod.fst).pull j) y v :=
    ⟨ht, i, hv⟩
  -- The image of `y` under `φ` has coordinates `g i • φ ∘ v = g`, as `ξ` has.
  have hx_map : IsCoordsWithUnit (((hyperplaneBundle ι).pull Limits.prod.fst).pull j)
      (PointsIn.map φ y) g := by
    simpa [← Units.smul_def, h_coord] using hx.map_unit_smul φ hgi_unit.unit
  exact ⟨_, hx, hξ.ext hx_map⟩

/-- Spreading out. Let ξ be a point over a field F with coordinates g, and let v_i ≠ 0 for some v
satisfying the homogeneous relations of g. Then there are a k-algebra D, a point y over D, a map j :
D → F and polynomials G_d (d ∈ D) with two properties. (a) j is injective and ξ = j(y). (b) Let w
over a k-algebra C satisfy the homogeneous relations of g, with w_i a unit. Then some φ : D → C has
φ(d) associated to G_d(w) for all d, and φ(y) has coordinates w. -/
lemma IsCoordsWithUnit.exists_universal_chart (hξ : IsCoordsWithUnit L ξ g)
    (hv : CutsOutLocus.IsHomogeneousSolution k g v) (hvi : v i ≠ 0) :
    ∃ (D : CommAlgCat k) (y : PointsIn Y D), ∃ (j : D ⟶ of k F) (G : D → MvPolynomial ι k),
      -- (a)
      (Function.Injective j ∧ ξ = PointsIn.map j y) ∧
      -- (b)
      ∀ {C : CommAlgCat k} {w : ι → C},
        CutsOutLocus.IsHomogeneousSolution k g w →
        IsUnit (w i) →
        ∃ φ : D ⟶ C,
          (∀ d : D, Associated (aeval w (G d)) (φ d)) ∧ IsCoordsWithUnit L (y.map φ) w := by
  -- `D` is the coordinate ring of the affine chart `X i = 1`: polynomials modulo those vanishing at
  -- `(g i)⁻¹ • g`. Homogeneous relations of `g` hold for `w`, so evaluation at `(w i)⁻¹ • w`
  -- factors through `D`.
  have hgi : IsUnit (g i) := by simpa [hvi] using hv (isHomogeneous_X _ i)
  -- `homog P` is homogeneous (`h_homog_deg`) and agrees with `P` under algebra maps with `X i ↦ 1`
  -- (`h_chart`).
  have h_homog (P : MvPolynomial ι k) : ∃ G : MvPolynomial ι k, G.IsHomogeneous P.totalDegree ∧
      ∀ {A : Type} [CommRing A] [Algebra k A] (φ : MvPolynomial ι k →ₐ[k] A),
        φ (X i) = 1 → φ G = φ P :=
    exists_homogenization (isHomogeneous_X k i) P le_rfl
  choose homog h_homog_deg h_chart using h_homog
  -- Evaluation at `(w i)⁻¹ • w` agrees up to a unit with evaluating the homogenisation at `w`.
  have h_eval {C : CommAlg k} {w : ι → C} (u : IsUnit (w i)) :
      ∃ φ : MvPolynomial ι k →ₐ[k] C,
        w i • φ ∘ X = w ∧ ∀ P, Associated ((homog P).aeval w) (φ P) := by
    refine ⟨aeval (u.unit⁻¹.val • w), by simp [← mul_assoc, funext_iff], fun P ↦ ?_⟩
    simp [← h_chart P, aeval_smul_of_isHomogeneous (h_homog_deg _), associated_unit_mul_right,
      IsUnit.pow]
  -- (`@` keeps `C` and `w` implicit in the chosen functions)
  choose φ hφX hφG using @h_eval
  -- `D = k[X] / ker (φ hgi)` embeds in `F`, so `ξ` descends to `y` with coordinates `X` mod kernel.
  obtain ⟨y, hy, hξy⟩ :=
    hξ.exists_descend_of_injective (ofHom _) (kerLiftAlg_injective (φ hgi)) (v := fun l ↦ ⟦X l⟧)
      (hφX hgi)
  refine ⟨.of k (MvPolynomial ι k ⧸ RingHom.ker (φ hgi)), y, ofHom (kerLiftAlg (φ hgi)),
    fun d ↦ homog d.out, ⟨kerLiftAlg_injective _, hξy⟩, fun hw u ↦ ?_⟩
  have h_ker (P : MvPolynomial ι k) (hP : P ∈ RingHom.ker (φ hgi)) : φ u P = 0 :=
    (hφG u P).eq_zero_iff.mp (hw (h_homog_deg P) ((hφG hgi P).eq_zero_iff.mpr hP))
  refine ⟨ofHom (Quotient.liftₐ _ (φ u) h_ker), fun d ↦ ?_, ?_⟩
  · conv_rhs => rw [← Quotient.out_eq d]
    exact hφG u d.out
  · -- The image of `y` has coordinates `w i • φ u ∘ X = w`. (`rw` cannot replace `w` here, as
    -- `φ u` depends on it.)
    exact (hφX u).subst (hy.map_unit_smul _ u.unit)

/-- Let `Y` be a scheme over `Spec R` with a line bundle `L` embedding it in projective space, and
let `k` be an algebraically closed `R`-algebra. Let `ξ` be an `F`-point of `Y` over a field `F ⊇ k`
with `L`-coordinates `g`, one of them a unit, and let `f` be a map from the functor `A ↦ Y(A)` on
`k`-algebras to the affine line. Then there is `c ∈ k` such that `f(x) = c` for every point
`x ∈ Y(A)` over a nonzero `k`-algebra `A` whose `L`-coordinates `v` have a unit entry and lie on the
cone of `g`, i.e. every homogeneous polynomial over `k` vanishing at `g` vanishes at `v`. -/
lemma IsCoordsWithUnit.exists_app_eq_algebraMap_of_isHomogeneousSolution
    (hξ : IsCoordsWithUnit L ξ g) [IsAlgClosed k] (f : algPointsOf k R Y ⟶ affineSpace k 1) :
    ∃ c : k, ∀ {A : CommAlg k} [Nontrivial A] {x : PointsIn Y A} {v : ι → A},
      IsCoordsWithUnit L x v →
      CutsOutLocus.IsHomogeneousSolution k g v → (f A x).down 0 = algebraMap k A c := by
  have h_nonempty : Nonempty ι := hξ.right.nonempty
  have h_f_map {A B : CommAlg k} (φ : A ⟶ B) (y : PointsIn Y A) :
      (f.app B (PointsIn.map φ y)).down 0 = φ ((f.app A y).down 0) :=
    congrArg (fun a ↦ a.down 0) (f.naturality_apply φ y)
  -- The value at `ξ` lies in every valuation ring `V` over `k`: dividing by the coordinate of
  -- largest valuation shows that `ξ` comes from a point over `V`. So it is integral over `k`.
  have h_integral : (algebraMap k F).IsIntegralElem ((f.app _ ξ).down 0) := by
    refine isIntegralElem_of_valuationSubring fun V hV ↦ ?_
    have h_max : ∃ i : ι, ∀ l : ι, ∃ x : V, x • g i = g l := Finite.exists_max (V.valuation ∘ g)
    choose i w hw using h_max
    -- the inclusion of `V`, as a subalgebra of `F`
    let toF : of k (⟨V.toSubsemiring, hV⟩ : Subalgebra k F) ⟶ of k F :=
      ofHom (Subalgebra.val ⟨V.toSubsemiring, hV⟩)
    have h_scaled : g i • ⇑toF ∘ w = g := funext fun l ↦ (mul_comm _ _).trans (hw l)
    obtain ⟨y, -, rfl⟩ := hξ.exists_descend_of_injective toF Subtype.val_injective h_scaled
    rw [h_f_map]
    exact Subtype.prop _
  -- As `k` is algebraically closed, this value is a constant `c`.
  obtain ⟨c, hc⟩ : ∃ c, algebraMap k F c = (f.app _ ξ).down 0 :=
    IsAbsIntegrallyClosed.mem_range_of_isIntegralElem h_integral
  refine ⟨c, fun {A} _ {x v} hx hv ↦ ?_⟩
  -- Both `ξ` and `x` are images of one point `y` over `D`, and `j : D ⟶ F` is injective.
  obtain ⟨i, hvi⟩ : ∃ i : ι, IsUnit (v i) := hx.right
  obtain ⟨D, y, j, G, ⟨j_inj, rfl⟩, h_spec⟩ := hξ.exists_universal_chart hv hvi.ne_zero
  obtain ⟨φ, -, hφ⟩ := h_spec hv hvi
  have h_f_y : (f.app D y).down 0 = algebraMap k D c :=
    j_inj ((h_f_map j y).symm.trans <| hc.symm.trans (j.hom.commutes c).symm)
  rw [hx.ext hφ, h_f_map, h_f_y]
  exact φ.hom.commutes c

/-- Let ξ be a point over a field F with coordinates g, lying in an open subfunctor V. Some
polynomial b with b(g) ≠ 0 has the property: every w that satisfies the homogeneous relations
of g and makes b(w) a unit is a vector of coordinates of a point of V. -/
lemma IsCoordsWithUnit.exists_mem_open_of_isUnit (hξ : IsCoordsWithUnit L ξ g)
    {V : Subfunctor (algPointsOf k R Y)} (hV : IsOpenSubfunctor V) (hξV : ξ ∈ V (of k F)) :
    ∃ b : MvPolynomial ι k,
      aeval g b ≠ 0 ∧
      ∀ {C : CommAlg k} {w : ι → C},
        CutsOutLocus.IsHomogeneousSolution k g w →
        IsUnit (aeval w b) →
        ∃ z ∈ V C, IsCoordsWithUnit L z w := by
  -- Spread `ξ` out to a point `z` over a subalgebra `D` of `F`; openness of `V` gives `b ∈ D` whose
  -- invertibility forces the specialisations of `z` into `V`. Take the polynomial `G b * X i`.
  obtain ⟨i, hi⟩ : ∃ i : ι, IsUnit (g i) := hξ.right
  obtain ⟨D, z, -, G, -, h_spec⟩ := hξ.exists_universal_chart .refl hi.ne_zero
  -- `z` specialises to `ξ` itself along `φ₀`, so this specialisation lies in `V`
  obtain ⟨φ₀, hφ₀, h_gen⟩ := h_spec .refl hi
  have h_eq : z.map φ₀ = ξ := h_gen.ext hξ
  have hz : z.map φ₀ ∈ V.obj _ := by rwa [h_eq]
  obtain ⟨b, hb, h_open⟩ := hV.exists_basicOpen φ₀ z (Field.toIsField _) hz
  refine ⟨G b * X i, ?_, fun hw h_unit ↦ ?_⟩
  · have h_Gb : aeval g (G b) ≠ 0 := (hφ₀ b).ne_zero_iff.mpr hb
    simpa using mul_ne_zero h_Gb hi.ne_zero
  · rw [map_mul, aeval_X, IsUnit.mul_iff] at h_unit
    obtain ⟨h_Gb_unit, h_wi_unit⟩ := h_unit
    obtain ⟨φ, hφ, h_coord⟩ := h_spec hw h_wi_unit
    exact ⟨z.map φ, h_open _ φ ((hφ b).isUnit h_Gb_unit), h_coord⟩

end New.Variety
end
end

/-!
# Projective space as a functor, and injective pull-back along Noether normalisation

Projective space `ℙ^d` over a field `k` is defined as a functor on `k`-algebras. It is the test
variety on which the Hodge–Tate map is shown not to kill the class of a point.

## Main definitions and results

* `New.Variety.projSpace`: `A ↦` unimodular vectors in `A ^ (d + 1)` modulo units of `A`.
* `New.Variety.projSpace.stdChart`, `New.Variety.projSpace.hasAtlas`: the `d + 1` standard charts
  form an atlas.
* `New.Variety.projSpace.lineProductMap`: a map `ℙ^d × ℙ¹ → ℙ^(d+1)`, used for induction on the
  dimension; `New.Variety.projSpace.isUnit_mul_sum_of_mul_eq_zero` and
  `New.Variety.projSpace.exists_eq_map_affinePoint_of_mul_eq_zero` describe the points where all
  its coordinates but the first vanish.
* `New.Variety.CutsOutLocus.IsNoetherNormalization.pullback_injective`: pull-back along the
  projection to `ℙ^d` of a subfunctor of `Y × ℙ^d` that contains the graph of a Noether
  normalisation is injective on cohomology of `p`-adic tests.

Notions from other files:
* `New.Variety.unimodular`: the subfunctor of affine `d`-space of vectors whose entries generate
  the unit ideal.
* `New.Variety.IsCoordsWithUnit L x v`: `v` is a vector of homogeneous coordinates, for the line
  bundle `L`, of the point `x` of `Y`, and some entry of `v` is a unit.
* `New.Variety.CutsOutLocus.IsHomogeneousSolution k g v`: every homogeneous polynomial over `k` that
  vanishes at `g` vanishes at `v`.
* `New.Variety.CutsOutLocus.IsNoetherNormalization Λ g`: the values at `g` of the linear forms
  `Λ 0, …, Λ d` satisfy no non-zero homogeneous relation, and the cone of `g` is integral over them.
* `New.Variety.IsTest`: a test ring: reduced, absolutely integrally closed, and any `a`, `b`
  admit an idempotent `e` with `a ∣ e * b` and `b ∣ (1 - e) * a`.

## Relation to the literature

Known; see `Lib.Cohomology.PointClass.LinearIndependence` for sources.
-/

@[expose] public section

noncomputable section

/-! ## Projective space as a functor, standard charts and a product map -/

section ProjectiveSpace

open CategoryTheory CommAlgCat Fin Ideal IsLocalRing MvPolynomial MonoidalCategory Subfunctor Set

variable (k : Type) [Field k] (d : ℕ)

/-! ### Points of projective space -/

/-- Projective `d`-space over `k`: the functor sending `A` to the unimodular vectors in
`A ^ (d + 1)` modulo units of `A`. These are the points of the scheme `ℙ^d` whose line bundle is
trivial; no sheafification is made. -/
def New.Variety.projSpace : CommAlg k ⥤ Type 1 where
  -- Unimodular vectors of length `d + 1`, up to scaling by a unit.
  obj A := Quot ((MulAction.orbitRel Aˣ (Fin (d + 1) → A)).comap
    (·.val.down : @unimodular k _ (d + 1) A → Fin (d + 1) → A))
  -- Vectors that differ by the unit `u` are sent to vectors that differ by the unit `f u`.
  map f := ↾Quot.map (unimodular.toFunctor.map f) fun _ _ ⟨u, h⟩ ↦ ⟨u.map f.hom.toMonoidHom, by
    simpa [Units.smul_def, _root_.funext_iff] using! congr(f ∘ $h)⟩
  map_id _ := by
    ext ⟨⟩
    rfl
  map_comp _ _ := by
    ext ⟨⟩
    rfl

namespace New.Variety.projSpace

variable {k d} {A : CommAlg k} {v w : Fin (d + 1) → A} (i : Fin (d + 1))

/-- Over a local ring `A`, a vector whose entries generate the unit ideal has a unit entry. -/
lemma exists_isUnit_of_span_eq_top [IsLocalRing A] (hv : span (Set.range v) = ⊤) :
    ∃ i : Fin (d + 1), IsUnit (v i) := by
  -- Otherwise all entries lie in the maximal ideal, and so does the unit ideal.
  by_contra h_none
  have h_le : span (Set.range v) ≤ maximalIdeal A := by
    simpa [span_le, range_subset_iff] using h_none
  exact (maximalIdeal.isMaximal A).ne_top (eq_top_mono h_le hv)

/-- For `v` in `A ^ (d + 1)` whose entries generate the unit ideal (`h`), the point
`[v 0 : … : v d]` of projective `d`-space. -/
def mk (v : Fin (d + 1) → A) (h : span (Set.range v) = ⊤) : projSpace k d A :=
  Quot.mk _ ⟨{ down := v }, h⟩

/-- The points `[v]` and `[w]` of projective `d`-space agree iff `u • v = w` for a unit `u` of
`A`. -/
lemma mk_eq_mk_iff_exists_unit {hv : span (Set.range v) = ⊤} {hw : span (Set.range w) = ⊤} :
    mk v hv = mk w hw ↔ ∃ u : Aˣ, u • v = w :=
  eq_comm.trans Quotient.eq

/-- For unimodular vectors `v` and `w` in `A ^ (d + 1)`, the points `[v]` and `[w]` of projective
`d`-space are equal iff `v a * w b = w a * v b` for all indices `a` and `b`. In other words, all
2 × 2 minors of the matrix with rows `v` and `w` vanish. -/
lemma mk_eq_mk_iff_cross_mul {hv : span (Set.range v) = ⊤} {hw : span (Set.range w) = ⊤} :
    mk v hv = mk w hw ↔ ∀ a b : Fin (d + 1), v a * w b = w a * v b := by
  rw [mk_eq_mk_iff_exists_unit]
  refine ⟨fun ⟨u, hu⟩ a b ↦ ?_, fun h_minor ↦ ?_⟩
  · simp [← hu, Units.smul_def, mul_assoc, mul_left_comm]
  · -- Write `1 = ∑ i, a i * v i`; the factor of proportionality is `c = ∑ i, a i * w i`.
    obtain ⟨a, ha⟩ : ∃ a : Fin (d + 1) → A, ∑ i, a i * v i = 1 :=
      mem_span_range_iff_exists_fun.mp ((eq_top_iff_one _).mp hv)
    set c : A := ∑ i, a i * w i with hc
    have h_prop (l : Fin (d + 1)) : c * v l = w l :=
      calc c * v l = (∑ i, a i * v i) * w l := by simp only [hc, Finset.sum_mul, mul_assoc, h_minor]
        _ = w l := by rw [ha, one_mul]
    -- `c` divides every entry of the unimodular vector `w`, so it is a unit.
    have h_le : span (Set.range w) ≤ span {c} :=
      span_le.mpr (range_subset_iff.mpr fun l ↦ mem_span_singleton.mpr (Dvd.intro _ (h_prop l)))
    have hc_unit : IsUnit c := span_singleton_eq_top.mp (eq_top_mono h_le hw)
    exact ⟨hc_unit.unit, funext h_prop⟩

/-- For `v` in `A ^ d`, the point of projective `d`-space with coordinate `1` in place `i` and the
entries of `v` in the other places. -/
abbrev affinePoint (v : Fin d → A) : projSpace k d A :=
  mk (i.insertNth 1 v) (span_eq_top_of_isUnit i (by simp))

/-- The point `[v]` lies in the image of the `i`-th standard chart iff `v i` is a unit. The chart
is the point over the polynomial ring with coordinate `1` in place `i` and the variables in
the other places. -/
lemma mk_mem_stdChart_iff {hv : span (Set.range v) = ⊤} :
    mk v hv ∈ Subfunctor.range (pointMap (affinePoint (A := of k (MvPolynomial (Fin d) k)) i X)) A ↔
      IsUnit (v i) := by
  refine ⟨fun ⟨φ, hφ⟩ ↦ ?_, fun ⟨u, hu⟩ ↦ ?_⟩
  · -- A point of the chart has a representative with `i`-th entry `1`, and `v` is `u` times it.
    obtain ⟨u, hu⟩ :
        ∃ u : Aˣ, u • (φ.down.hom ∘ (i.insertNth 1 X : Fin (d + 1) → MvPolynomial (Fin d) k)) = v :=
      mk_eq_mk_iff_exists_unit.mp hφ
    have h_vi : v i = u := by simp [← hu, Units.smul_def]
    simp [h_vi]
  · -- If `v i = u` is a unit, the affine coordinates are the other entries divided by `u`.
    let φ : of k (MvPolynomial (Fin d) k) ⟶ A := ofHom (aeval (u⁻¹ • v ∘ i.succAbove))
    refine ⟨⟨φ⟩, mk_eq_mk_iff_exists_unit.mpr ⟨u, ?_⟩⟩
    simp [φ, i.forall_iff_succAbove, ← hu, Units.smul_def, _root_.funext_iff]

/-! ### The map `ℙ^d × ℙ¹ → ℙ^(d+1)` -/

/-- Let `v`, `u` be unimodular vectors over a local algebra over a field of characteristic `0`, with
`(u 1 - i * u 0) * v i = 0` for all `i`. Then for some `j`, `v j` and `u 0` are units,
`j * u 0 = u 1`, and `v i = 0` for `i ≠ j`. -/
private lemma exists_isUnit_coord_of_mul_eq_zero [CharZero k] [IsLocalRing A] {u : Fin 2 → A}
    (hv : span (Set.range v) = ⊤) (hu : span (Set.range u) = ⊤)
    (h_mul_eq_zero : ∀ i : Fin (d + 1), (u 1 - i * u 0) * v i = 0) :
    ∃ j : Fin (d + 1), IsUnit (v j) ∧ IsUnit (u 0) ∧ j * u 0 = u 1 ∧ ∀ i ≠ j, v i = 0 := by
  -- In a local ring some coordinate `v j` is a unit, which forces `u = [1 : j]`.
  -- As `i - j` is invertible in `k` for `i ≠ j`, all other `v i` vanish.
  obtain ⟨j, hj⟩ := exists_isUnit_of_span_eq_top hv
  have hu1 : j * u 0 = u 1 := (sub_eq_zero.mp (hj.mul_left_eq_zero.mp (h_mul_eq_zero j))).symm
  -- `u 0` divides `u 1 = j * u 0`, so it generates the unit ideal.
  have h_le : span (Set.range u) ≤ span {u 0} := by
    simp [span_le, range_subset_iff, mem_span_singleton, ← hu1]
  have hu0 : IsUnit (u 0) := span_singleton_eq_top.mp (eq_top_mono h_le hu)
  refine ⟨j, hj, hu0, hu1, fun i hij ↦ by_contra fun hi ↦ hij ?_⟩
  -- Put `u 1 = j * u 0` in `h_mul_eq_zero i`; cancel the unit `u 0` and the nonzero `v i`.
  have h_mul : u 0 * ((i : k) • v i) = u 0 * ((j : k) • v i) := by
    have h0 := h_mul_eq_zero i
    rw [← hu1, sub_mul] at h0
    have h1 : (i : A) * u 0 * v i = (j : A) * u 0 * v i := (sub_eq_zero.mp h0).symm
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, nsmul_eq_mul]
    calc u 0 * ((i : A) * v i) = (i : A) * u 0 * v i := by ring
      _ = (j : A) * u 0 * v i := h1
      _ = u 0 * ((j : A) * v i) := by ring
  have h_cast : (i : k) = j := smul_left_injective k hi (hu0.mul_left_cancel h_mul)
  exact Fin.ext (Nat.cast_injective h_cast)

/-- Let `v`, `u` be unimodular vectors over a local algebra over a field of characteristic `0`,
of lengths `d + 1` and `2`, with `(u 1 - i * u 0) * v i = 0` for all `i`. Then the first
coordinate `u 0 * ∑ i, v i` of `New.Variety.projSpace.lineProductMap` at `([v], [u])` is a unit. -/
lemma isUnit_mul_sum_of_mul_eq_zero [CharZero k] [IsLocalRing A] {u : Fin 2 → A}
    (hv : span (Set.range v) = ⊤) (hu : span (Set.range u) = ⊤)
    (h_mul_eq_zero : ∀ i : Fin (d + 1), (u 1 - i * u 0) * v i = 0) :
    IsUnit (u 0 * ∑ i : Fin (d + 1), v i) := by
  -- The sum is `v j`, as the other entries vanish.
  obtain ⟨j, hj, hu0, -, h_zero⟩ := exists_isUnit_coord_of_mul_eq_zero hv hu h_mul_eq_zero
  simpa only [Fintype.sum_eq_single j h_zero] using hu0.mul hj

/-- Let `v`, `u` be unimodular vectors over a local algebra over a field of characteristic `0`, with
`(u 1 - i * u 0) * v i = 0` for all `i`. Then, with the points `affinePoint` taken over `k` and
carried to `A` by `structureMap` (the map `k → A`), for some `j` the point `[v]` is the `j`-th
coordinate point and `[u] = [1 : j]`. -/
lemma exists_eq_map_affinePoint_of_mul_eq_zero [CharZero k] [IsLocalRing A] {u : Fin 2 → A}
    (hv : span (Set.range v) = ⊤) (hu : span (Set.range u) = ⊤)
    (h_mul_eq_zero : ∀ i : Fin (d + 1), (u 1 - i * u 0) * v i = 0) :
    ∃ j : Fin (d + 1),
      (mk v hv, mk u hu) =
        (projSpace k d ⊗ projSpace k 1).map structureMap (affinePoint j 0, affinePoint 0 ![j]) := by
  obtain ⟨j, hj, hu0, hu1, h_zero⟩ := exists_isUnit_coord_of_mul_eq_zero hv hu h_mul_eq_zero
  refine ⟨j, Prod.ext ?_ ?_⟩
  · -- `v` is `v j` times the `j`-th coordinate vector, as its other entries vanish.
    change mk v hv = (projSpace k d).map structureMap (affinePoint j 0)
    refine (mk_eq_mk_iff_exists_unit.mpr ⟨hj.unit, ?_⟩).symm
    simp [_root_.funext_iff, j.forall_iff_succAbove, h_zero]
  · -- `u` is `u 0` times `(1, j)`.
    change mk u hu = (projSpace k 1).map structureMap (affinePoint 0 ![j])
    refine (mk_eq_mk_iff_exists_unit.mpr ⟨hu0.unit, ?_⟩).symm
    simp [_root_.funext_iff, ← hu1, mul_comm]

variable (k d)

/-- For `i : Fin (d + 1)`, the standard chart of projective `d`-space where the `i`-th coordinate is
invertible, on the polynomial ring in `d` variables. The chart point is `affinePoint i X` with
coordinates `X`. It is injective on points, and its image is open: the locus where the `i`-th
coordinate is a unit. -/
def stdChart : EtaleChart d (projSpace k d) where
  coordRing := of k (MvPolynomial (Fin d) k)
  point := affinePoint i X
  coordinate := X
  etale := by simpa [aeval_X_left] using .containsIdentities _
  injective A φ ψ h := by
    -- The `i`-th coordinate is `1`, so the minors that involve it compare the other coordinates.
    ext j
    simpa using mk_eq_mk_iff_cross_mul.1 h (i.succAbove j) i
  isOpenSubfunctor A := by
    -- The chart is the locus where the `i`-th coordinate is a unit.
    rintro ⟨v⟩
    exact ⟨span {v.val.down i}, fun B φ ↦ (mk_mem_stdChart_iff i).trans (by simp [map_span])⟩

/-- Projective `d`-space has an atlas of dimension `d`: finitely many charts whose images contain
every field-valued point, and for any two points an ideal whose vanishing locus is where they agree.
The standard charts `New.Variety.projSpace.stdChart` contain every field-valued point. Two points
`[v]` and `[w]` agree exactly where all `v a * w b - w a * v b` vanish, so the space is
separated. -/
instance hasAtlas : HasAtlas d (projSpace k d) where
  exists_finite_charts := by
    -- Over a field some coordinate of a unimodular vector is a unit.
    refine ⟨d + 1, stdChart k d, fun K hK ↦ ?_⟩
    let fieldK : Field K := hK.toField
    rintro ⟨⟨⟨v⟩, hv⟩⟩
    exact (exists_isUnit_of_span_eq_top hv).imp fun i ↦ (mk_mem_stdChart_iff i).mpr
  exists_ideal := by
    -- Two points agree where the 2 × 2 minors of their representatives vanish.
    rintro A ⟨⟨⟨v⟩, hv⟩⟩ ⟨⟨⟨w⟩, hw⟩⟩
    refine ⟨⨆ (a) (b), span {v a * w b - w a * v b}, fun B φ ↦ mk_eq_mk_iff_cross_mul.trans ?_⟩
    simp [iSup_le_iff, span_le, RingHom.mem_ker, sub_eq_zero]

/-- In characteristic 0: if `v` and `u` are unimodular, so is the vector with entries
`u 0 * ∑ i, v i` and `(u 1 - i * u 0) * v i`. -/
lemma span_range_cons_mul_eq_top [CharZero k] {u : Fin 2 → A} (hv : span (Set.range v) = ⊤)
    (hu : span (Set.range u) = ⊤) :
    span (Set.range
      (cons (u 0 * ∑ i : Fin (d + 1), v i) fun i : Fin (d + 1) ↦ (u 1 - i * u 0) * v i :
        Fin (d + 2) → A)) = ⊤ := by
  -- It suffices that no map `ψ` to a field kills all entries; if it kills the later entries,
  -- `isUnit_mul_sum_of_mul_eq_zero` says that it sends the first one to a unit.
  rw [← (span _).map_id]
  refine (map_eq_top_iff_forall_isField _ (𝟙 A)).mpr fun K ψ hK h_le ↦ ?_
  let fieldK : Field K := hK.toField
  obtain ⟨h_first, h_rest⟩ : ψ (u 0) * ∑ i : Fin (d + 1), ψ (v i) = 0 ∧
      ∀ i : Fin (d + 1), (ψ (u 1) - i * ψ (u 0)) * ψ (v i) = 0 := by
    rw [span_le, range_subset_iff] at h_le
    refine ⟨?_, fun i ↦ ?_⟩
    · have h0 : ψ (u 0 * ∑ i : Fin (d + 1), v i) = 0 := h_le 0
      simpa only [map_mul, map_sum] using h0
    · have hi : ψ ((u 1 - i * u 0) * v i) = 0 := h_le i.succ
      simpa only [map_mul, map_sub, map_natCast] using hi
  have h_unit : IsUnit (ψ (u 0) * ∑ i : Fin (d + 1), ψ (v i)) :=
    isUnit_mul_sum_of_mul_eq_zero
      (unimodular.map ψ (a := ⟨v⟩) hv) (unimodular.map ψ (a := ⟨u⟩) hu) h_rest
  exact h_unit.ne_zero h_first

/-- In characteristic `0`, the map `ℙ^d × ℙ¹ → ℙ^(d+1)` that sends `([v], [w 0 : w 1])` to the
point with coordinates `w 0 * ∑ i, v i` and `(w 1 - i * w 0) * v i` for `i = 0, …, d`. -/
def lineProductMap [CharZero k] : projSpace k d ⊗ projSpace k 1 ⟶ projSpace k d.succ where
  app A := ↾fun x ↦ x.1.liftOn₂ x.2
    (fun ⟨⟨v⟩, hv⟩ ⟨⟨w⟩, hw⟩ ↦
      mk (cons (w 0 * ∑ i : Fin (d + 1), v i) fun i ↦ (w 1 - i * w 0) * v i)
        (span_range_cons_mul_eq_top k d hv hw))
    -- Scaling `w`, or `v`, by a unit scales every coordinate by that unit.
    (by
      rintro ⟨⟨v⟩, hv⟩ ⟨⟨w⟩, hw⟩ ⟨⟨w'⟩, hw'⟩ ⟨c, h⟩
      have hc : ∀ j, (c : A) * w' j = w j := fun j ↦ congrFun h j
      refine (mk_eq_mk_iff_exists_unit.mpr ⟨c, funext fun j ↦ ?_⟩).symm
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, cons_zero, ← hc, mul_assoc]
      · simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, cons_succ, ← hc]
        ring)
    (by
      rintro ⟨⟨v⟩, hv⟩ ⟨⟨v'⟩, hv'⟩ ⟨⟨w⟩, hw⟩ ⟨c, h⟩
      have hc : ∀ j, (c : A) * v' j = v j := fun j ↦ congrFun h j
      refine (mk_eq_mk_iff_exists_unit.mpr ⟨c, funext fun j ↦ ?_⟩).symm
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, cons_zero, ← hc,
          ← Finset.mul_sum, mul_left_comm]
      · simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, cons_succ, ← hc]
        ring)
  naturality A B f := by
    ext ⟨⟨v⟩, ⟨w⟩⟩
    refine mk_eq_mk_iff_exists_unit.mpr ⟨1, funext fun j ↦ ?_⟩
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simp only [one_smul, Function.comp_apply, cons_zero, map_mul, map_sum]
    · simp only [one_smul, Function.comp_apply, cons_succ, map_mul, map_sub, map_natCast]

end New.Variety.projSpace

end ProjectiveSpace

/-!
## Injectivity of pull-back along a Noether normalisation

The proof of `New.Variety.CutsOutLocus.IsNoetherNormalization.pullback_injective` is a transfer
argument (`New.Variety.exists_transfer_map`) over the Galois hull
`New.Variety.CutsOutLocus.IsNoetherNormalization.exists_galois_closure`; its two density conditions
are checked near each maximal ideal of a test ring.
-/

section NormalizationPullback

open MvPolynomial CategoryTheory Ideal Function MonoidalCategory CartesianMonoidalCategory

/-- A test ring `A` over `k` with a prime `m` has a geometric point `κ` that sees `A` near `m`:
finitely many equations that hold under `κ` hold in `A` after multiplication by one element
outside `m`. -/
lemma New.Variety.CutsOutLocus.exists_geometric_point_near_prime {k A : Type} [Field k] [CommRing A]
    [Algebra k A] (hA : IsTest A) (m : Ideal A) [m.IsPrime] :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra k K) (κ : A →ₐ[k] K),
      ∀ {σ : Type} [Finite σ] {r s : σ → A},
      (∀ l : σ, κ (r l) = κ (s l)) → ∃ a ∉ m, ∀ l : σ, a * r l = a * s l := by
  -- the local ring at `m` is a valuation ring of an algebraically closed field `K`
  obtain ⟨-, -, K, _, hK, O, _, h_loc⟩ := hA.exists_valuationSubring_atPrime m
  algebraize [(O.subtype.comp (algebraMap A O)).comp (algebraMap k A)]
  -- `κ` is the map `A → O ⊆ K`
  let κ : A →ₐ[k] K := ⟨O.subtype.comp (algebraMap A O), fun _ ↦ rfl⟩
  refine ⟨K, inferInstance, hK, inferInstance, κ, fun {σ} _ r s h_eq ↦ ?_⟩
  -- `r` and `s` agree in the localisation `O` of `A` at `m`
  obtain ⟨⟨a, ha⟩, h_smul⟩ : ∃ a : m.primeCompl, a • r = a • s :=
    (IsLocalizedModule.pi m.primeCompl fun _ ↦ Algebra.linearMap A O).exists_of_eq
      (funext fun l ↦ Subtype.ext (h_eq l))
  exact ⟨a, ha, fun l ↦ congrFun h_smul l⟩

/-- Let `f : k[X] → B` be finite and injective, `A` a test ring (reduced, absolutely integrally
closed, and any `a`, `b` admit an idempotent `e` with `a ∣ e b` and `b ∣ (1 − e) a`) with a prime
`m`, and `w` a point of affine space over `A`. Near `m` the point lifts to `B`: there are `a ∉ m`
and a map of sets `s : B → A` such that, for each `ψ : A → C` that inverts `a`, `ψ ∘ s` is a
`k`-algebra map `v` with `v ∘ f ∘ X = ψ ∘ w`. -/
lemma New.Variety.CutsOutLocus.exists_lift_near_prime {k A B σ : Type} [Field k] [CommRing A]
    [Algebra k A] [CommRing B] [Algebra k B] [Finite σ] (hA : IsTest A) (m : Ideal A) [m.IsPrime]
    {f : MvPolynomial σ k →ₐ[k] B} (h_fin : f.toRingHom.Finite) (h_inj : Function.Injective f)
    (w : σ → A) :
    ∃ a ∉ m, ∃ s : B → A, ∀ (C : CommAlg k) (ψ : A →ₐ[k] C), IsUnit (ψ a) → ∃ v : B →ₐ[k] C,
      v ∘ f ∘ X = ψ ∘ w ∧ ∀ y : B, v y = ψ (s y) := by
  -- Lift the point to `B` at a geometric point `κ` that sees `A` near `m`. The images of
  -- generators of `B` are integral over `A`, so they come from `A`; the finitely many relations
  -- then hold in `A` after multiplication by some `a ∉ m`.
  obtain ⟨K, _, _, _, κ, h_near⟩ := exists_geometric_point_near_prime (k := k) hA m
  obtain ⟨φ, hφ⟩ : ∃ φ : B →ₐ[k] K, φ.comp f = κ.comp (aeval w) :=
    exists_algHom_comp_eq_of_integral f (κ.comp (aeval w)) h_fin.to_isIntegral
      (comap_bot_le_of_injective _ h_inj)
  -- a finite presentation `π` of `B` over `k[X]`, with finitely many relations `rel`
  obtain ⟨N, π, h_surj, rel, h_ker⟩ :=
    (RingHom.FinitePresentation.of_finiteType.mp h_fin.finiteType).out
  -- `π` is a map of algebras over `k[X]`, for the algebra structure on `B` given by `f`; as a map
  -- of `k`-algebras it is the evaluation `q` at the images `y` of the variables
  let algebraB : Algebra (MvPolynomial σ k) B := f.toRingHom.toAlgebra
  let y : Fin N → B := π ∘ X
  let q : MvPolynomial (Fin N) (MvPolynomial σ k) →ₐ[k] B := aevalTower f y
  have h_q (x : MvPolynomial (Fin N) (MvPolynomial σ k)) : q x = π x := by
    rw [aeval_unique π]
    rfl
  replace h_surj : Surjective q := fun b ↦ (h_surj b).imp fun x hx ↦ (h_q x).trans hx
  replace h_ker : span (rel : Set _) = RingHom.ker q := by
    rw [h_ker]
    ext x
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h_q]
  -- `y i` is integral over `k[X]`, so `φ (y i)` is integral over the image of `φ ∘ f = κ ∘ aeval w`
  have h_int (i : Fin N) : κ.toRingHom.IsIntegralElem (φ (y i)) := by
    have h_comp : (φ.comp f).toRingHom.IsIntegralElem (φ (y i)) :=
      (h_fin.to_isIntegral (y i)).map _
    rw [hφ] at h_comp
    exact .of_comp h_comp
  -- `A` is absolutely integrally closed, so elements integral over `κ` lie in its range
  have h_range (i : Fin N) : ∃ r : A, κ r = φ (y i) := hA.mem_range_of_isIntegralElem (h_int i)
  choose r hr using h_range
  let θ : MvPolynomial (Fin N) (MvPolynomial σ k) →ₐ[k] A := aevalTower (aeval (R := k) w) r
  have h_comm : κ.comp θ = φ.comp q := by
    ext i : 2
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', θ, q, aevalTower_algebraMap]
      exact (AlgHom.congr_fun hφ (X i)).symm
    · simp only [AlgHom.comp_apply, θ, q, aevalTower_X]
      exact hr i
  have h_rel (x : rel) : κ (θ x) = κ 0 := by
    have hqx : q x.val = 0 := RingHom.mem_ker.mp (h_ker.le (subset_span x.prop))
    calc κ (θ x) = φ (q x.val) := AlgHom.congr_fun h_comm x.val
      _ = 0 := by rw [hqx, map_zero]
      _ = κ 0 := (map_zero κ).symm
  obtain ⟨a, ha, h_mul⟩ : ∃ a ∉ m, ∀ l : rel, a * θ l = a * 0 := h_near h_rel
  refine ⟨a, ha, θ ∘ surjInv h_surj, fun C ψ hψ ↦ ?_⟩
  -- `ψ ∘ θ` kills the relations, since `ψ a` is a unit, and so factors through `q`
  have h_kill : RingHom.ker q ≤ RingHom.ker (ψ.comp θ) := by
    rw [← h_ker, span_le]
    intro x hx
    have h_ax : ψ a * ψ (θ x) = 0 := by
      have h0 := congrArg ψ (h_mul ⟨x, hx⟩)
      rw [mul_zero, map_mul, map_zero] at h0
      exact h0
    exact hψ.mul_right_eq_zero.mp h_ax
  let v : B →ₐ[k] C := q.liftOfSurjective h_surj (ψ.comp θ) h_kill
  have h_fac (x : MvPolynomial (Fin N) (MvPolynomial σ k)) : v (q x) = ψ (θ x) :=
    q.liftOfSurjective_apply h_surj (ψ.comp θ) h_kill x
  refine ⟨v, funext fun j ↦ ?_, fun x ↦ ?_⟩
  · simpa only [θ, q, aevalTower_C, aeval_X, Function.comp_apply] using h_fac (.C (X j))
  · simpa only [surjInv_eq h_surj x, Function.comp_apply] using h_fac (surjInv h_surj x)

/-- Suppose that some solution `v` of the homogeneous equations of `g` has `v i ≠ 0`. Then every
solution `u` whose coordinate `u i` is a unit is a coordinate vector of a point of `Y`. -/
lemma New.Variety.CutsOutLocus.exists_point_of_isUnit_coord {k ι F : Type} [Field k] [Field F]
    {R : CommRingCat} [Algebra R k] [Finite ι] [Algebra k F] {Y : Over (AlgebraicGeometry.Spec R)}
    {L : LineBundle Y.left ι} [Fact (L.IsProjEmbedding Y.hom)] {ξ : PointsIn Y (CommAlgCat.of k F)}
    {g : ι → F} (hξ : IsCoordsWithUnit L ξ g) {A C : CommAlg k} {v : ι → A} {u : ι → C} {i : ι}
    (hv : IsHomogeneousSolution k g v) (hi : v i ≠ 0) (hu : IsHomogeneousSolution k g u)
    (h_unit : IsUnit (u i)) :
    ∃ y : PointsIn Y C, IsCoordsWithUnit L y u := by
  -- the point is the image of the universal point of `IsCoordsWithUnit.exists_universal_chart`
  obtain ⟨D, y, j, G, -, h_rep⟩ := hξ.exists_universal_chart hv hi
  obtain ⟨φ, -, hφ⟩ := h_rep hu h_unit
  exact ⟨y.map φ, hφ⟩

/-- The Galois cover of a Noether normalisation, as a functor on `k`-algebras. A point over `A` is
a family `y` of points of `Y` indexed by `G` with a map `v : B → A` of `k`-algebras, such that
`v ∘ b σ` is a coordinate vector of `y σ` with a unit entry for each `σ`, and the values
`v (f (X j))` generate the unit ideal. -/
private def New.Variety.CutsOutLocus.galoisCover {k ι G : Type} [Field k] {R : CommRingCat}
    [Algebra R.carrier k] {Y : Over (AlgebraicGeometry.Spec R)}
    (L : LineBundle Y.left ι) [Fact (L.IsProjEmbedding Y.hom)] {B : CommAlg k} {d : ℕ}
    (f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B) (b : G → ι → B) : CommAlg k ⥤ Type 1 :=
  .mk
    (fun A ↦
      {x : (G → PointsIn Y A) × (B →ₐ[k] A) //
        (∀ σ : G, IsCoordsWithUnit L (x.fst σ) (x.snd ∘ b σ)) ∧
          span (Set.range (x.snd ∘ f ∘ X)) = ⊤})
    fun φ ↦
      ↾fun x ↦
        ⟨(_, φ.hom.comp x.val.snd), fun σ ↦ (x.property.left σ).comp φ,
          unimodular.map φ (a := ⟨_⟩) x.property.right⟩

/-- Let `L` embed `Y` in projective space, and let `ξ` be an `F`-point of `Y` with coordinates `g`,
some `g i` a unit. Take a prime `m` of a test ring `A`, i.e. `A` is reduced and absolutely
integrally closed, and any `a, b` admit an idempotent `e` with `a ∣ e b` and `b ∣ (1 − e) a`. A
point `[w]` of projective space, with `w` generating the unit ideal, lifts near `m` to the Galois
cover of a Noether normalisation. Here `f : k[X₀, …, X_d] → B` is finite and injective, and each
`b σ` solves the homogeneous equations of `g` and is taken by `Λ` to `f ∘ X`. For some `a ∉ m`,
after every `ψ : A → C` that inverts `a`, there are `v : B → C` with `v ∘ f ∘ X = ψ ∘ w` and points
of `Y` with coordinate vectors `v ∘ b σ`. -/
lemma New.Variety.CutsOutLocus.exists_cover_point_near_prime {k ι F G : Type} [Field k] [Field F]
    [Fintype G] {R : CommRingCat} [Algebra R k] [Finite ι] [Algebra k F]
    {Y : Over (AlgebraicGeometry.Spec R)} {L : LineBundle Y.left ι} [Fact (L.IsProjEmbedding Y.hom)]
    {ξ : PointsIn Y (CommAlgCat.of k F)} {g : ι → F} (hξ : IsCoordsWithUnit L ξ g) {d : ℕ}
    {Λ : Fin (d + 1) → ↥(homogeneousSubmodule ι k 1)} {B : CommAlg k}
    {f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B} {b : G → ι → B}
    (hb_hom : ∀ σ : G, IsHomogeneousSolution k g (b σ))
      (hb_forms : ∀ σ : G, evalForms Λ (b σ) = f ∘ X)
    (h_fin : f.toRingHom.Finite) (h_inj : Injective f) {A : CommAlg k} (hA : IsTest A)
    (m : Ideal A) [hm : m.IsPrime] {w : Fin (d + 1) → A} (hw : span (Set.range w) = ⊤) :
    ∃ a ∉ m, ∀ (C : CommAlg k) (ψ : A ⟶ C), IsUnit (ψ a) →
      ∃ (y : G → PointsIn Y C) (v : B →ₐ[k] C),
        (∀ σ : G, IsCoordsWithUnit L (y σ) (v ∘ b σ)) ∧ v ∘ f ∘ X = ψ ∘ w := by
  -- Lift `w` to `B` near `m` through a map of sets `s`. Each `b σ` has an entry `b σ (i σ)` whose
  -- lift does not lie in `m`; where all these lifts are units, each `v ∘ b σ` has a unit entry and
  -- so is a coordinate vector of a point of `Y`.
  obtain ⟨a, ha, s, h_lift⟩ := exists_lift_near_prime hA m h_fin h_inj w
  obtain ⟨v, hv, hv_s⟩ :
      ∃ v : B →ₐ[k] m.ResidueField, v ∘ f ∘ X = algebraMap A m.ResidueField ∘ w ∧
        ∀ y : B, v y = algebraMap A m.ResidueField (s y) :=
    h_lift (.of k m.ResidueField) (IsScalarTower.toAlgHom k A m.ResidueField)
      (isUnit_iff_ne_zero.mpr (mt algebraMap_residueField_eq_zero.mp ha))
  -- In the residue field no `v ∘ b σ` vanishes: otherwise the forms `Λ` vanish there, so the
  -- entries of `w` lie in `m`.
  have h_ne (σ : G) : v ∘ b σ ≠ 0 := by
    intro h_zero
    have h_forms : v ∘ f ∘ X = 0 := by
      rw [← hb_forms σ, ← evalForms_map, h_zero]
      have h0 := evalForms_smul Λ (u := (0 : m.ResidueField)) (v := 0)
      simp only [zero_smul] at h0
      exact h0
    rw [hv] at h_forms
    have h_le : span (Set.range w) ≤ m := by
      rw [span_le, Set.range_subset_iff]
      exact fun j ↦ algebraMap_residueField_eq_zero.mp (congrFun h_forms j)
    exact hm.ne_top (eq_top_mono h_le hw)
  choose i hi using fun σ : G ↦ ne_iff.mp (h_ne σ)
  have h_notMem (σ : G) : s (b σ (i σ)) ∉ m := fun h_mem ↦
    hi σ ((hv_s _).trans (algebraMap_residueField_eq_zero.mpr h_mem))
  refine ⟨a * ∏ σ : G, s (b σ (i σ)), m.primeCompl.mul_mem ha (prod_mem fun σ _ ↦ h_notMem σ),
    fun C ψ h_unit ↦ ?_⟩
  rw [map_mul, map_prod] at h_unit
  obtain ⟨ha_unit, h_prod⟩ := IsUnit.mul_iff.mp h_unit
  have h_unit_s (σ : G) : IsUnit (ψ (s (b σ (i σ)))) :=
    isUnit_of_dvd_unit
      (Finset.dvd_prod_of_mem (fun x ↦ ψ (s (b x (i x)))) (Finset.mem_univ σ)) h_prod
  obtain ⟨v', hv', hv'_s⟩ : ∃ v' : B →ₐ[k] C, v' ∘ f ∘ X = ψ ∘ w ∧ ∀ y : B, v' y = ψ (s y) :=
    h_lift C ψ.hom ha_unit
  have h_unit' (σ : G) : IsUnit (v' (b σ (i σ))) := (hv'_s _).symm ▸ h_unit_s σ
  have h_point (σ : G) : ∃ y : PointsIn Y C, IsCoordsWithUnit L y (v' ∘ b σ) :=
    exists_point_of_isUnit_coord (A := .of k m.ResidueField) (v := v ∘ b σ) (u := v' ∘ b σ) hξ
      ((hb_hom σ).map v) (hi σ) ((hb_hom σ).map v') (h_unit' σ)
  choose y hy using h_point
  exact ⟨y, v', hy, hv'⟩

/-- Near a prime `m` of a test ring `A` (reduced, absolutely integrally closed, and any `a`, `b`
admit an idempotent `e` with `a ∣ e b` and `b ∣ (1 − e) a`), two families of points over one point
of projective space differ by a shift in the finite group `G`, given that `h_conj` says this at
geometric points. If `u • v₀ ∘ f ∘ X = v₁ ∘ f ∘ X` for a unit `u`, and `y₀ σ`, `y₁ σ` are points of
`Y` with coordinate vectors `v₀ ∘ b σ`, `v₁ ∘ b σ`, then for some `a ∉ m` and `τ ∈ G`, `y₀ (τ * ρ)`
and `y₁ ρ` agree after every `ψ : A → C` that inverts `a`. -/
lemma New.Variety.CutsOutLocus.exists_map_mul_eq_map_near_prime {k ι G : Type} [Field k] [Group G]
    [Finite G] {R : CommRingCat} [Algebra R k] [Finite ι] {Y : Over (AlgebraicGeometry.Spec R)}
    {L : LineBundle Y.left ι} [Fact (L.IsProjEmbedding Y.hom)] {d : ℕ} {B : CommAlg k}
    {f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B} {b : G → ι → B}
    (h_conj : ∀ {K : Type} [Field K] [IsAlgClosed K] [Algebra k K] (φ ψ : B →ₐ[k] K) (u : K),
      u • φ ∘ f ∘ X = ψ ∘ f ∘ X → ∃ τ : G, ∀ σ : G, ψ ∘ b σ = u • φ ∘ b (τ * σ))
    {A : CommAlg k} (hA : IsTest A) (m : Ideal A) [m.IsPrime] {y₀ y₁ : G → PointsIn Y A}
    {v₀ v₁ : B →ₐ[k] A} (hy₀ : ∀ σ : G, IsCoordsWithUnit L (y₀ σ) (v₀ ∘ b σ))
    (hy₁ : ∀ σ : G, IsCoordsWithUnit L (y₁ σ) (v₁ ∘ b σ)) {u : Aˣ}
    (hu : u • v₀ ∘ f ∘ X = v₁ ∘ f ∘ X) :
    ∃ a ∉ m, ∃ τ : G, ∀ (C : CommAlg k) (ψ : A ⟶ C), IsUnit (ψ a) → ∀ ρ : G,
      (y₀ (τ * ρ)).map ψ = (y₁ ρ).map ψ := by
  -- At a geometric point `κ` that sees `A` near `m` the coordinate vectors differ by a shift `τ`
  -- (`h_conj`); these finitely many equations then hold in `A` after multiplication by `a ∉ m`.
  obtain ⟨K, _, _, _, κ, h_near⟩ := exists_geometric_point_near_prime (k := k) hA m
  have h_κ : κ u • κ.comp v₀ ∘ f ∘ X = κ.comp v₁ ∘ f ∘ X :=
    funext fun j ↦ by
      simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul, Function.comp_apply,
        map_mul, AlgHom.comp_apply] using congrArg κ (congrFun hu j)
  obtain ⟨τ, hτ⟩ : ∃ τ : G, ∀ σ : G, κ.comp v₁ ∘ b σ = κ u • κ.comp v₀ ∘ b (τ * σ) :=
    h_conj (κ.comp v₀) (κ.comp v₁) (κ u) h_κ
  have h_eq_κ (l : G × ι) : κ (v₁ (b l.fst l.snd)) = κ (u * v₀ (b (τ * l.fst) l.snd)) := by
    simpa only [Function.comp_apply, AlgHom.comp_apply, Pi.smul_apply, smul_eq_mul,
      map_mul] using congrFun (hτ l.fst) l.snd
  obtain ⟨a, ha, h_mul⟩ : ∃ a ∉ m, ∀ l : G × ι,
      a * v₁ (b l.fst l.snd) = a * (u * v₀ (b (τ * l.fst) l.snd)) :=
    h_near h_eq_κ
  refine ⟨a, ha, τ, fun C ψ h_unit ρ ↦ ?_⟩
  -- after inverting `a` the coordinate vectors are proportional, so the points of `Y` agree
  have h_coord : ψ ∘ v₁ ∘ b ρ = u.map ψ.hom.toMonoidHom • ψ ∘ v₀ ∘ b (τ * ρ) := by
    funext l
    have h_l : ψ a * ψ (v₁ (b ρ l)) = ψ a * (ψ u * ψ (v₀ (b (τ * ρ) l))) := by
      simpa only [map_mul] using congrArg ψ (h_mul (ρ, l))
    exact h_unit.mul_left_cancel h_l
  refine ((hy₀ (τ * ρ)).map_unit_smul ψ (u.map ψ.hom.toMonoidHom)).ext ?_
  rw [← h_coord]
  exact (hy₁ ρ).comp ψ

/-- Let `ν ≫ α = n • l` for maps `α : N' ⟶ N`, `ν : Q ⟶ N'` and `l : Q ⟶ N` of abelian functors,
where `n ≠ 0` and `l` is an equivalence for a coefficient functor `F` (`IsCohomEquiv`: each
`H.map F l m`, pull-back on the cohomology `H^m(·, F)`, is bijective) on which the field `k` of
characteristic zero acts. Then pull-back along `α` is injective on `H^m(·, F)`. -/
lemma New.Variety.injective_H_map_of_comp_eq_nsmul {C : Type 1} [Category C] (k : Type) [Field k]
    [CharZero k] {F : AbFunctor C} [CoeffAction k F] {N N' Q : AbFunctor C} {α : N' ⟶ N}
    {ν : Q ⟶ N'} {l : Q ⟶ N} {n : ℕ} (hn : n ≠ 0) (h_comp : ν ≫ α = n • l)
    (h_l : IsCohomEquiv F l) (m : ℕ) :
    Injective (H.map F α m) := by
  -- `H(ν) ∘ H(α) = n • H(l)`, and multiplication by `n` is injective on a vector space over `k`.
  have h_fun : H.map F ν m ∘ H.map F α m = fun x ↦ n • H.map F l m x := by
    funext x
    rw [Function.comp_apply, ← H.map_comp]
    have h_hom : H.mapHom F Q N m (ν ≫ α) = n • H.mapHom F Q N m l := by rw [h_comp, map_nsmul]
    exact DFunLike.congr_fun h_hom x
  have h_torsionFree : HasUniqueDiv (H Q F m) := .of_isTorsionFree k (H Q F m)
  refine Injective.of_comp (f := H.map F ν m) ?_
  rw [h_fun]
  exact (nsmul_right_injective hn).comp (h_l m).injective

/-- Pull-back along a Noether normalisation is injective on cohomology. Let `Y` be embedded in
projective space by `L`, `ξ` a point of `Y` over a field with coordinates `g`, and `Λ` a Noether
normalisation of `g`. Let `O ⊆ Γ ⊆ Y × ℙ^d` contain `(x, [Λ(v)])` for every coordinate vector `v` of
`x` solving the homogeneous equations of `g` (`hO`). Then pull-back along `O → ℙ^d` is injective on
`H^n` on `p`-adic tests with coefficients `genericCoeff` (a test with ring R ↦ R[1/p]), taking the
free abelian groups on points with values in `genericOver` (R ↦ R[1/p] as a `k`-algebra). -/
lemma New.Variety.CutsOutLocus.IsNoetherNormalization.pullback_injective {p : ℕ} {k ι F : Type}
    [Field k] [EmbeddedInQpBar p k] [Field F] {R : CommRingCat} [Algebra R.carrier k] [Finite ι]
    [Algebra k F] {g : ι → CommAlgCat.of k F} {d n : ℕ} {Y : Over (AlgebraicGeometry.Spec R)}
    {Λ : Fin (d + 1) → ↥(homogeneousSubmodule ι k 1)} {L : LineBundle Y.left ι}
    [Fact (L.IsProjEmbedding Y.hom)] {ξ : PointsIn Y (CommAlgCat.of k F)}
    (hξ : IsCoordsWithUnit L ξ g) (hΛ : IsNoetherNormalization (k := k) Λ g)
    {Γ : Subfunctor (algPointsOf k R Y ⊗ projSpace k d)} {O : Subfunctor Γ.toFunctor}
    (hO :
      ∀ {A : CommAlg k} {x : PointsIn Y A} {v : ι → A} {hv : span (Set.range (evalForms Λ v)) = ⊤},
        IsHomogeneousSolution k g v → IsCoordsWithUnit L x v →
          ∃ hΓ : (x, projSpace.mk (evalForms Λ v) hv) ∈ Γ.obj A,
        ⟨(x, projSpace.mk (evalForms Λ v) hv), hΓ⟩ ∈ O A) :
    Function.Injective
      (H.map genericCoeff (genericOver.whiskerLeft
        (freeAb.map (O.ι ≫ Γ.ι ≫ snd (algPointsOf k R Y) (projSpace k d)))) n) := by
  -- Points of `W`, the Galois cover of the cone of `g`, map to `O` once for each `σ ∈ G`, over
  -- one point of `ℙ^d`; `f`, `b` and `h_conj` come from the Galois hull.
  obtain ⟨G, B, _, f, b, hb, h_fin, h_inj, h_conj⟩ := hΛ.exists_galois_closure
  obtain ⟨hb_hom, hb_forms⟩ := forall_and.mp hb
  let T : PadicTest ⥤ CommAlg k := genericOver (p := p)
  let W : PadicTest ⥤ Type 1 := T ⋙ galoisCover L f b
  have h_mem (σ : G) (c : PadicTest) (x : W.obj c) :
      ∃ hΓ, ⟨(x.val.fst σ, projSpace.mk _ x.property.right), hΓ⟩ ∈ O (T.obj c) := by
    have h_vec : evalForms Λ (x.val.snd ∘ b σ) = x.val.snd ∘ f ∘ X := by
      rw [evalForms_map, hb_forms σ]
    have hv : span (Set.range (evalForms Λ (x.val.snd ∘ b σ))) = ⊤ := h_vec.symm ▸ x.property.right
    have h_pt :
        projSpace.mk (evalForms Λ (x.val.snd ∘ b σ)) hv =
          projSpace.mk (x.val.snd ∘ f ∘ X) x.property.right := by
      simp only [h_vec]
    exact h_pt ▸ hO (hv := hv) ((hb_hom σ).map x.val.snd) (x.property.left σ)
  let t (σ : G) : W ⟶ T ⋙ O.toFunctor :=
    { app c := ↾fun x ↦ ⟨_, (h_mem σ c x).snd⟩
      naturality c₁ c₂ φ := rfl }
  let π : T ⋙ O.toFunctor ⟶ T ⋙ projSpace k d :=
    T.whiskerLeft (O.ι ≫ Γ.ι ≫ snd (algPointsOf k R Y) (projSpace k d))
  have h_over (σ : G) : t σ ≫ π = t 1 ≫ π := rfl
  -- The transfer gives `ν ≫ ℤ[π] = card G • l`; by `h_eqv`, `l` is an equivalence once the image
  -- of `W` is dense in `ℙ^d` and the pairs with permuted tuples `(t σ)_σ` are dense in `W ×_ℙ W`.
  obtain ⟨Q, -, l, ν, -, -, h_transfer, h_eqv⟩ := exists_transfer_map h_over
  have h_test (c : PadicTest) : IsTest (T.obj c) := c.isTest.localization
  -- by Zariski descent, density may be checked near each maximal ideal of a test ring
  have h_zar :
      HasZariskiDescent (𝟭 PadicTest ⋙ genericOver ⋙ forget₂ (CommAlg k) CommRingCat)
        genericCoeff := by
    obtain ⟨e, -⟩ := exists_periodAlg_iso_genericAlg (p := p)
    exact hasZariskiDescent_genericOver (k := k) (𝟭 _) (hasPartitions_periodAlg _ e)
  suffices h_l : IsCohomEquiv genericCoeff l by
    exact injective_H_map_of_comp_eq_nsmul k Fintype.card_ne_zero h_transfer h_l n
  refine h_eqv _ (h_zar fun c x (m : Ideal (T.obj c)) hm ↦ ?_)
    (h_zar fun c x (m : Ideal (T.obj c)) hm ↦ ?_)
  · -- near `m`, a point `[w]` of projective space comes from `W`
    obtain ⟨⟨w⟩, hw : span (.range w) = ⊤⟩ := x
    obtain ⟨a, ha, h_cover⟩ :=
      exists_cover_point_near_prime hξ hb_hom hb_forms h_fin h_inj (h_test c) m hw
    refine ⟨a, ha, fun c' φ h_unit ↦ ?_⟩
    obtain ⟨y, v', hy, hv'⟩ :
        ∃ (y : G → PointsIn Y (T.obj c')) (v' : B →ₐ[k] T.obj c'),
          (∀ σ : G, IsCoordsWithUnit L (y σ) (v' ∘ b σ)) ∧ v' ∘ f ∘ X = T.map φ ∘ w :=
      h_cover _ (T.map φ) h_unit
    have h_span_w : span (Set.range (T.map φ ∘ w)) = ⊤ := unimodular.map (T.map φ) (a := ⟨w⟩) hw
    have h_span : span (Set.range (v' ∘ f ∘ X)) = ⊤ := by rwa [hv']
    have h_pt : projSpace.mk (v' ∘ f ∘ X) h_span = projSpace.mk (T.map φ ∘ w) h_span_w := by
      simp only [hv']
    exact ⟨⟨(y, v'), hy, h_span⟩, h_pt⟩
  · -- near `m`, two points of `W` over one point of projective space differ by some `τ : G`
    let x₀ : W.obj c := x.val 0
    let x₁ : W.obj c := x.val 1
    obtain ⟨u, hu⟩ : ∃ u : (T.obj c)ˣ, u • x₀.val.snd ∘ f ∘ X = x₁.val.snd ∘ f ∘ X :=
      projSpace.mk_eq_mk_iff_exists_unit.mp (x.property 0 1)
    obtain ⟨a, ha, τ, h_shift⟩ :=
      exists_map_mul_eq_map_near_prime h_conj (h_test c) m x₀.property.left x₁.property.left hu
    refine ⟨a, ha, fun c' φ h_unit ↦ ⟨.mulLeft τ, fun ρ ↦ ?_⟩⟩
    -- the two points lie over one point of projective space
    have h_base : (t 1 ≫ π).app c' (((cech (t 1 ≫ π) 1).map φ x).val 1) =
        (t 1 ≫ π).app c' (((cech (t 1 ≫ π) 1).map φ x).val 0) :=
      ((cech (t 1 ≫ π) 1).map φ x).property 1 0
    have h_eq : (x₀.val.fst (τ * ρ)).map (T.map φ) = (x₁.val.fst ρ).map (T.map φ) :=
      h_shift _ (T.map φ) h_unit ρ
    -- a point of `O` is determined by its point of `Y` and its point of projective space
    exact Subtype.ext (Subtype.ext (Prod.ext h_eq.symm h_base))

end NormalizationPullback

end
