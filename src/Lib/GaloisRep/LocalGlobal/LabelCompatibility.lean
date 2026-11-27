module

import Mathlib.RingTheory.Frobenius
import Mathlib.Topology.Algebra.Group.Units
import TauCeti.RepresentationTheory.Subrepresentation
public import Lib.GaloisRep.BaseChange.PrimeDegreeTransfer
public import Lib.LocalGL.Shintani.CosetDescent
import Lib.LocalGL.Shintani.LiftingGreenCharacters
import Lib.PadicComparison.Descent.TestCategory
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Tactic.Linter.Style
public import Lib.GaloisRep.LocalGlobal.LocalFormTypes
public import Lib.GaloisRep.Main.AttachedRepresentations
import Lib.ClassField.Global.ArtinMap
import Lib.ClassField.Places.TameInertia
import Lib.GaloisRep.LocalGlobal.IwahoriCompatibility
import Lib.GaloisRep.Main.OddRank
import Lib.General.NumberTheory.FrobeniusOrbits
import Lib.LocalGL.Green.LabelCharacters
import Lib.LocalGL.Iwahori.SortedExponents

section
/-!
# Base change at an inert place carries a label to its Shintani lift

Base change along a step `E'/E` (`New.IsStep E' μ`, which among other things makes `[E' : E]` prime)
at a place `w` of `E` that is split over `E⁺` and inert in `E'`: the local matching comes from
Shintani lifting for `GL n` over the residue fields.

* `New.inflateConj`: the conjugate of a function on `GL n` of the residue field, pulled back along
  reduction to `GL n 𝒪_w` and extended by zero to `GL n` of the completion.
* `New.exists_representation_heckeFun_inflateConj`: on forms of principal level at `w`, its Hecke
  operator is the action of a group algebra element of the finite group.
* `New.isLocalMatching_shintani`: inflated `Ξ` and, for some `φ`, inflated `g ↦ S ⟨g, φ⟩` are
  matching local data, where `S` is a class function on the semidirect product that descends to `Ξ`.
* `New.exists_baseChange_hasLabel`: a form with label `Ξ` at `w` has a weak base change with the
  lift `Ξ'` as label at the place `u` above `w`.

`New.localCongruence n w 0` is the kernel of reduction of `GL n 𝒪_w`; `New.HasLabel f hw χ` says
that this kernel fixes `f` and that `∑ conj (χ x) x` does not kill `f`.

Notions from other files:
* `New.Lift`: F lifts to F' over Z if, for every m, one Z-combination of characters of GL_m(k') ⋊
  Gal(k'/k) descends to both F (over k) and F' (over k').
* `New.IsLocalMatching`: Retracts G, G' of the adelic groups above a finite set of places,
  compatible levels, and bi-invariant functions that form matching pairs at a level where σ-cocycles
  split.

## Relation to the literature

Known; see `Lib.GaloisRep.BaseChange.PrimeDegreeTransfer` for sources.
-/

@[expose] public section

namespace New

open NumberField Representation Function ComplexConjugate FiniteField Module
  SemidirectProduct algebraMap

attribute [local instance low] Fintype.ofFinite

variable {E E' n : Type} [Field E] [CMType E] [Field E'] [Fintype n] [DecidableEq n]
  {w : FinPlace E}

open scoped Classical in
/-- The inflation of `χ`, conjugated: the function on `GL n (LocField w)` that sends `g` in
`GL n 𝒪_w` (`intGL n Valued.v.integer`) to `conj (χ (reduceGL g))`, the complex conjugate of `χ`
at the reduction of `g` modulo `w`, and is `0` outside `GL n 𝒪_w`. -/
noncomputable def inflateConj (χ : GL n (ResField w) → ℂ) (g : GL n (LocField w)) : ℂ :=
  if h : g ∈ intGL n Valued.v.integer then conj (χ (reduceGL ⟨g, h⟩)) else 0

/-- Let `K` be the forms of weight `κ` in `stdSpace E n` that are fixed by the kernel of reduction
at the split place `w`. On `K ⊓ W`, for each subrepresentation `W`, the finite group
`GL n (ResField w)` acts by some `ρ` such that the following holds for every `χ` and `v`, with `x`
the action of `∑ conj (χ g) g` on `v`. (a) The Hecke operator of `inflateConj χ` (which is
`conj (χ (g mod w))` on `GL n 𝒪_w` and `0` elsewhere) sends `v` to `x`. (b) `v` has label `χ`
(`New.HasLabel`: `v` is fixed by the reduction kernel and `∑ conj (χ g)` times the translates of `v`
by lifts of `g` is nonzero) exactly when `x ≠ 0`. -/
lemma exists_representation_heckeFun_inflateConj (hw : w.IsSplit) {κ : Weight E} :
    let π := ((stdSpace E n).formTranslation κ).comp (ofSplitPlace hw)
    let K := levelSpace π (localCongruence n w 0)
    ∀ W : Subrepresentation π, ∃ ρ : Representation ℂ (GL n (ResField w)) ↥(K ⊓ W.toSubmodule),
      ∀ (χ : GL n (ResField w) → ℂ) (v : ↥(K ⊓ W.toSubmodule)),
      let x := ρ.asAlgebraHom (groupAlgElem fun g : GL n (ResField w) ↦ conj (χ g)) v
      -- (a)
      heckeFun π (localCongruence n w 0) (inflateConj χ) v = x ∧
      -- (b)
      (HasLabel v.val.val hw χ ↔ x ≠ 0) := by
  classical
  -- `GL n 𝒪_w` acts on `K ⊓ W` and the kernel of reduction acts trivially, so the action descends
  -- to `ρ`. Both claims unfold to sums over lifts of the elements of `GL n (ResField w)`.
  intro π K W
  let π₀ : Representation ℂ (intGL n Valued.v.integer) _ :=
    π.comp (intGL n Valued.v.integer).subtype
  have hK : K = invariants (π₀.comp reduceGL.ker.subtype) := by
    aesop (add simp mem_localCongruence_zero)
  have h_stable (k : intGL n Valued.v.integer) : K ⊓ W.1 ≤ (K ⊓ W.1).comap (π₀ k) :=
    fun v ⟨hv_K, hv_W⟩ ↦ ⟨hK.ge (le_comap_invariants _ _ k (hK.le hv_K)), W.2 _ hv_W⟩
  let π₁ : intGL n Valued.v.integer →* (↥(K ⊓ W.toSubmodule) →ₗ[ℂ] ↥(K ⊓ W.toSubmodule))ˣ :=
    (subrepresentation π₀ _ h_stable).asGroupHom
  -- the kernel of reduction acts trivially on `K`
  have h_ker : reduceGL.ker ≤ π₁.ker := fun k hk ↦ by
    ext v : 3
    exact hK.le v.property.1 ⟨k, hk⟩
  let ρ : Representation ℂ (GL n (ResField w)) ↥(K ⊓ W.toSubmodule) :=
    (Units.coeHom _).comp (reduceGL.liftOfSurjective reduceGL_surjective ⟨π₁, h_ker⟩)
  let lift : GL n (ResField w) → GL n (LocField w) := Subtype.val ∘ surjInv reduceGL_surjective
  refine ⟨ρ, fun χ v ↦ ?_⟩
  obtain ⟨hv_K, -⟩ := Submodule.mem_inf.mp v.prop
  have h_sum : (ρ.asAlgebraHom (groupAlgElem fun g ↦ conj (χ g)) v).val =
      ∑ x, conj (χ x) • π (lift x) v := by
    simp [asAlgebraHom_eq_sum]
    -- `ρ x v` is `π (lift x) v` by the definition of `ρ`
    rfl
  -- the kernel of reduction fixes `v`, so the first half of `HasLabel` holds
  have h_fixed : ∀ k : intGL n Valued.v.integer, reduceGL k = 1 →
      rightRegular ℂ (Gf E n) (WeylIndex n κ.1 → ℂ) (ofSplitPlace hw k.val) v.val.val = v.val.val :=
    fun k hk ↦ congrArg Subtype.val (hK.le hv_K ⟨k, hk⟩)
  refine ⟨?_, (and_iff_right h_fixed).trans ?_⟩
  · -- The cosets of the lifts modulo `localCongruence n w 0` are distinct and cover `GL n 𝒪_w`,
    -- off which `inflateConj χ` is zero.
    have h_right : ∀ (g : GL n (LocField w)) (k : localCongruence n w 0),
        inflateConj χ (g * k) = inflateConj χ g := by
      simp +contextual [inflateConj, mem_localCongruence_zero, mul_mem_cancel_right,
        ← MulMemClass.mk_mul_mk]
    have h_inj : Set.InjOn (fun x ↦ (lift x : GL n (LocField w) ⧸ localCongruence n w 0))
        (SetLike.coe (⊤ : Finset (GL n (ResField w)))) := by
      simp +contextual [lift, surjInv_eq, Set.InjOn, inv_mul_eq_one, QuotientGroup.eq,
        ← InvMemClass.coe_inv, -Subgroup.coe_inv, mem_localCongruence_zero, ← MulMemClass.mk_mul_mk,
        mul_mem_cancel_left]
    have h_cover : ∀ g : GL n (LocField w), inflateConj χ g ≠ 0 →
        ∃ x ∈ (⊤ : Finset (GL n (ResField w))),
          (lift x : GL n (LocField w) ⧸ localCongruence n w 0) = g := by
      simp +contextual [lift, surjInv_eq, inv_mul_eq_one, QuotientGroup.eq,
        ← InvMemClass.coe_inv, -Subgroup.coe_inv, mem_localCongruence_zero, ← MulMemClass.mk_mul_mk,
        mul_mem_cancel_left, inflateConj]
    obtain ⟨-, h_eq⟩ := heckeFun_eq_sum (r := lift) (s := ⊤) h_right hv_K h_inj h_cover
    simp [h_eq, lift, surjInv_eq, h_sum, inflateConj]
  · simp [Subtype.ext_iff, h_sum, finsum_eq_sum_of_fintype]
    -- `π (lift x)` is right translation by `ofSplitPlace hw (lift x)` (definition of
    -- `formTranslation`)
    rfl

/-- Reduction commutes with the map of completions induced by `ι`, if `ψ` is the map of residue
fields that `ι` induces on global integers. -/
lemma reduceGL_map_locMap [CMType E'] {u : FinPlace E'} {ι : E →+* E'} (he : u.comap ι = w)
    (ψ : ResField w →+* ResField u)
    (hψ : ∀ x : 𝓞 E, ψ (algebraMap (𝓞 E) (ResField w) x) = ↑(RingOfIntegers.mapRingHom ι x : 𝓞 E'))
    (g : GL n (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w))
    (hg : (Matrix.GeneralLinearGroup.map (locMap ι he)) g ∈ intGL n Valued.v.integer) :
    reduceGL ⟨Matrix.GeneralLinearGroup.map (n := n) (locMap ι he) g, hg⟩ =
      (reduceGL ⟨g, (map_locMap_mem_intGL_iff he).mp hg⟩).map ψ := by
  -- Take a global integer `x` congruent to the entry `g i j` at `w`. Both sides are the class of
  -- the image of `x` at `u`, since `locMap` pulls the valuation at `u` back to one equivalent to
  -- the valuation at `w`.
  ext i j
  obtain ⟨x, hx⟩ := algebraMap_ResField_surjective w
    (reduceGL ⟨g, (map_locMap_mem_intGL_iff he).1 hg⟩ i j)
  have h_ψx : ψ (reduceGL ⟨g, (map_locMap_mem_intGL_iff he).1 hg⟩ i j) =
      ↑(RingOfIntegers.mapRingHom ι x : 𝓞 E') := (congrArg ψ hx).symm.trans (hψ x)
  refine (h_ψx.trans ?_).symm
  have h_val := residue_eq_iff_valuation_sub_lt_one.mp hx
  apply residue_eq_iff_valuation_sub_lt_one.mpr
  simpa using! ((isEquiv_comap_locMap ι he).lt_one_iff_lt_one (x := (x : E) - _)).2 h_val

variable [Algebra E E'] [CMTypeOver E E'] {u : FinPlace E'}
  {μ : (𝔸f E)ˣ →* ℂˣ} [hμ : IsStep E' μ]
  (hw : star w ≠ w) (hu : star u ≠ u)
  (h_unique : ∀ u' : FinPlace E', FinPlace.below E u' = w ↔ u' = u)
  (hμ_trivial : ∀ x : (LocField w)ˣ, μ (locIdele w x) = 1) [Algebra (ResField w) (ResField u)]
  (h_residue : ∀ x : 𝓞 E, ((x : ResField w) : ResField u) = (x : 𝓞 E'))
  (h_degree : finrank (ResField w) (ResField u) = finrank E E') {Ξ : Hall (ResField w)}

include h_unique hμ_trivial h_residue h_degree

omit h_unique hμ_trivial h_residue h_degree in
/-- Let `σ` in `Gal(E'/E)` fix the finite place `u` of `E'` and induce `φ` on the residue field of
`u`, where `φ` is an automorphism over the residue field of the place `w` of `E`. Let `a` be an
element of the finite adelic unitary group over `E'` whose component at `u` lies in `GL n 𝒪_u`.
Then the twisted norm `N = a · σ(a) ⋯ σ^{m-1}(a)` also has its component at `u` in `GL n 𝒪_u`, and
in `GL n (ResField u) ⋊ Gal(ResField u/ResField w)` the `m`-th power of (reduction of `a`, `φ`) is
(reduction of `N`, `φ ^ m`). -/
lemma exists_mk_reduceGL_pow_eq_mk_reduceGL_twistedNorm {σ : Gal(E'/E)} (hσ_u : u.comap σ = u)
    {φ : Gal(ResField u/ResField w)}
    (hσ : ∀ x : 𝓞 E', φ (algebraMap (𝓞 E') (ResField u) x) = algebraMap (𝓞 E') (ResField u) (σ • x))
    (a : Gf E' n) (ha : a.atPlace u ∈ intGL n Valued.v.integer) (m : ℕ) :
    ∃ h_norm : (twistedNorm (galoisGf σ) m a).atPlace u ∈ intGL n Valued.v.integer,
      (⟨reduceGL ⟨a.atPlace u, ha⟩, φ⟩ : GalSemidirect (ResField w) (ResField u) n) ^ m =
        ⟨reduceGL ⟨(twistedNorm (galoisGf σ) m a).atPlace u, h_norm⟩, φ ^ m⟩ := by
  -- The norm of length `m + 1` is `a · σ(N)`, with `N` the norm of length `m`. Reduction at `u`
  -- turns `σ` into `φ`, and `⟨x, φ⟩ * ⟨y, φ ^ m⟩ = ⟨x * φ y, φ ^ (m + 1)⟩`.
  induction m with
  | zero =>
    have h_one : (twistedNorm (galoisGf σ) 0 a).atPlace u = 1 := by simp [twistedNorm]
    have h_int : (twistedNorm (galoisGf σ) 0 a).atPlace u ∈ intGL n Valued.v.integer := by
      rw [h_one]
      exact one_mem _
    have h_reduce : reduceGL ⟨(twistedNorm (galoisGf σ) 0 a).atPlace u, h_int⟩ = 1 :=
      (congrArg reduceGL (Subtype.ext h_one)).trans (map_one reduceGL)
    refine ⟨h_int, ?_⟩
    rw [pow_zero, pow_zero, h_reduce]
    rfl
  | succ m ih =>
    obtain ⟨hN_int, h_pow⟩ := ih
    set N : GL n (LocField u) := (twistedNorm (galoisGf σ) m a).atPlace u
    let σN : GL n (LocField u) := Matrix.GeneralLinearGroup.map (locMap σ hσ_u) N
    have hσN_int : σN ∈ intGL n Valued.v.integer := (map_locMap_mem_intGL_iff hσ_u).2 hN_int
    have hσN_reduce : reduceGL ⟨σN, hσN_int⟩ = (reduceGL ⟨N, hN_int⟩).map φ :=
      reduceGL_map_locMap hσ_u φ hσ N hσN_int
    have h_succ : (twistedNorm (galoisGf σ) (m + 1) a).atPlace u = a.atPlace u * σN := by
      rw [twistedNorm_succ', map_mul, atPlace_galoisGf (h := hσ_u)]
    have h_int : (twistedNorm (galoisGf σ) (m + 1) a).atPlace u ∈ intGL n Valued.v.integer := by
      rw [h_succ]
      exact mul_mem ha hσN_int
    have h_reduce : reduceGL ⟨(twistedNorm (galoisGf σ) (m + 1) a).atPlace u, h_int⟩ =
        reduceGL ⟨a.atPlace u, ha⟩ * (reduceGL ⟨N, hN_int⟩).map φ := by
      rw [← hσN_reduce, ← map_mul]
      exact congrArg reduceGL (Subtype.ext h_succ)
    refine ⟨h_int, ?_⟩
    rw [pow_succ', h_pow, h_reduce, pow_succ', SemidirectProduct.mul_def]
    rfl

omit hμ_trivial h_residue h_degree in
include hμ in
/-- Let `u` be the only place of `E'` above `w`, and let `φ`, the Frobenius of the residue
extension at `u`, be nontrivial. Then some `σ ≠ 1` in `Gal(E'/E)` fixes `u`, lies outside the
inertia group of `u`, and induces `φ` on the residue field of `u`. -/
private lemma exists_ne_one_and_frobeniusAlgEquivOfAlgebraic_apply_eq
    {φ : Gal(ResField u/ResField w)}
    (hφ : φ = frobeniusAlgEquivOfAlgebraic (ResField w) (ResField u)) (hφ_ne : φ ≠ 1) :
    ∃ σ : Gal(E'/E), σ ≠ 1 ∧ u.comap σ = u ∧ σ ∉ Ideal.inertia Gal(E'/E) u.asIdeal ∧
      ∀ x : 𝓞 E', φ (algebraMap (𝓞 E') (ResField u) x) =
        algebraMap (𝓞 E') (ResField u) (σ • x) := by
  obtain rfl : FinPlace.below E u = w := (h_unique u).2 rfl
  obtain ⟨σ, h_frob⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) Gal(E'/E) u.asIdeal
  have hσ (x : 𝓞 E') : φ (algebraMap _ _ x) = algebraMap _ _ (σ • x) := by
    rw [hφ, eq_comm]
    simpa [card_ResField, ← Nat.card_eq_fintype_card, ← algebraMap_ResField_eq_zero,
      ← Ideal.absNorm_eq_natCard, sub_eq_zero] using! h_frob x
  -- `φ ≠ 1`, so `σ` moves some residue class
  have h_moves : ∃ x : 𝓞 E', algebraMap _ (ResField u) (σ • x) ≠ algebraMap _ _ x := by
    simpa [hσ, AlgEquiv.ext_iff, (algebraMap_ResField_surjective u).forall] using hφ_ne
  have hσ_ne : σ ≠ 1 := by
    rintro rfl
    simp at h_moves
  have h_inertia : σ ∉ Ideal.inertia Gal(E'/E) u.asIdeal := by
    simpa [sub_eq_zero, ← algebraMap_ResField_eq_zero]
  exact ⟨σ, hσ_ne, (h_unique _).1 (below_comap σ u), h_inertia, hσ⟩

/-- Let `E'/E` be a step with `μ` (`New.IsStep`) and let `w` be split with `μ` trivial on its
ideles. Let `u` be the only place above `w`, split, with residue field of degree `[E' : E]` over
that of `w`, and let `Ξ` be a function on similarity classes of matrices over `ResField w`
(`New.Hall`). If `S` on `GalSemidirect (ResField w) (ResField u) n` is a class function that
descends to `Ξ` (so `S ⟨a, φ⟩ = Ξ.evalGL b` when `φ ≠ 1` and `⟨a, φ⟩ ^ orderOf φ` is `inl` of `b`
mapped to `ResField u`), then for some `φ` in the residue Galois group the inflations of the complex
conjugates of `Ξ` and of `S ⟨·, φ⟩` are matching local data (`New.IsLocalMatching`) above `{w}`.
Here `GL n` at `w` and at `u` is embedded by `New.ofSplitPlace`, at level `≡ 1` mod the maximal
ideal. -/
lemma isLocalMatching_shintani {S : GalSemidirect (ResField w) (ResField u) n → ℂ}
    (hS : IsClassFunction S) (h_lf : DescendsTo S Ξ) :
    ∃ φ : Gal(ResField u/ResField w),
      IsLocalMatching μ {w} (ofSplitPlace hw) (ofSplitPlace hu) (localCongruence n w 0)
        (localCongruence n u 0) {()} (fun _ ↦ inflateConj Ξ.evalGL)
        fun _ ↦ inflateConj fun g : GL n (ResField u) ↦ S ⟨g, φ⟩ := by
  classical
  -- Take for `φ` the Frobenius of the residue extension and for `σ` a Frobenius at `u` lifting
  -- it. Reduction carries twisted conjugation and twisted norms to conjugation and powers in the
  -- coset of `φ`, where `S` is a class function that lifts `Ξ`.
  obtain rfl : FinPlace.below E u = w := (h_unique u).2 rfl
  let φ := frobeniusAlgEquivOfAlgebraic (ResField (u.below E)) (ResField u)
  have h_order : orderOf φ = finrank E E' :=
    (orderOf_frobeniusAlgEquivOfAlgebraic _ _).trans h_degree
  have hφ_ne : φ ≠ 1 := by simpa [← h_order] using hμ.out.ne_one
  obtain ⟨σ, hσ_ne, hσ_u, h_inertia, hσ⟩ :=
    exists_ne_one_and_frobeniusAlgEquivOfAlgebraic_apply_eq h_unique (φ := φ) rfl hφ_ne
  obtain ⟨h_retr, h_retr', h_level⟩ := isLocalRetraction_ofSplitPlace n h_unique hu hw
  -- The place is unramified, so the level `m` of `exists_isBaseChangeLevel` is the maximal level
  -- `K` at `u`. Hence cocycles split at `K` (`h_coh`), and the indicator functions of `K` form a
  -- matching pair (`h_pair`).
  let K : Subgroup (Gf E' n) := (intGL n Valued.v.integer).comap (Gf.atPlace u)
  have h_unram : IsStepUnramifiedAt E' μ (u.below E) := fun u' hu' ↦ by
    obtain rfl : u' = u := (h_unique u').1 hu'
    exact ⟨⟨σ, h_inertia⟩, fun x hx ↦ by simp [hμ_trivial]⟩
  obtain ⟨m, hm⟩ := exists_isBaseChangeLevel (n := n) hσ_ne isOpen_stdLevel
  have hK : K = localLevel n (placesAbove E' {u.below E}) m := by
    refine h_level.symm.trans (Subgroup.ext fun g ↦ forall₂_congr fun u' hu' ↦ ?_)
    rw [hm.eq_localIntGL _ h_unram (by simp) u' hu']
  obtain ⟨-, -, h_coh, -, h_pair⟩ := hm.isMatchingLevel {u.below E}
  rw [← hK] at h_coh h_pair
  refine ⟨φ, σ, hσ_ne, Gf.atPlace _, Gf.atPlace u,
    ⟨fun _ ↦ ?_, h_retr, h_retr', Set.finite_singleton _, ?_⟩, ?_,
    isOpen_localCongruence.preimage_of_continuous, K, ⟨fun _ hk ↦ hk.1, h_level.ge⟩, h_coh,
    fun _ _ ↦ ⟨fun (k : Gf E' n) hk (δ : Gf E' n) ↦ ?_, fun P hP hPσ ↦ ?_⟩⟩
  · -- Inflated functions are bi-invariant under the principal level, with compact support:
    -- `inflateConj` vanishes off the integral matrices.
    constructor <;>
      exact ⟨(finite_quotient_image_of_isCompact isOpen_localCongruence
        (isCompact_localIntGL _)).subset
        fun q hq ↦ ⟨_, by by_contra h; exact hq (dite_eq_right h), q.out_eq⟩,
        by simp +contextual [mem_localCongruence_zero, inflateConj,
          mul_mem_cancel_right, ← MulMemClass.mk_mul_mk, mul_mem_cancel_left]⟩
  · -- The principal level at `u` is stable under `σ`,
    simp +contextual [hσ_u, reduceGL_map_locMap hσ_u φ hσ, EmbeddingLike.map_eq_one_iff, eq_ite_iff,
      Matrix.GeneralLinearGroup.ext_iff, Matrix.one_apply, atPlace_galoisGf,
      mem_localCongruence_zero, map_locMap_mem_intGL_iff]
  · -- and its preimage over `E` is the principal level below.
    simp +contextual [SetLike.ext_iff, reduceGL_map_locMap _ _ h_residue, eq_ite_iff,
      Matrix.GeneralLinearGroup.ext_iff, Matrix.one_apply, atPlace_baseChangeGf,
      mem_localCongruence_zero, map_locMap_mem_intGL_iff]
  · -- Twisted conjugation by `x` is conjugation by `inl x⁻¹` on the coset of `φ`.
    have h_conj (δ x : GL n (ResField u)) : S ⟨x⁻¹ * δ * x.map φ, φ⟩ = S ⟨δ, φ⟩ := hS ⟨δ, φ⟩ (inl _)
    have h_inv (a : GL n (LocField u)) ha : reduceGL ⟨a⁻¹, inv_mem ha⟩ = (reduceGL ⟨a, ha⟩)⁻¹ :=
      reduceGL.map_inv ⟨a, ha⟩
    have hk_int : k.atPlace u ∈ intGL n Valued.v.integer := hk
    change (inflateConj (fun g ↦ S ⟨g, φ⟩) ∘ Gf.atPlace u) (k⁻¹ * δ * galoisGf σ k) = _
    simp +contextual [hk_int, hσ_u, reduceGL_map_locMap hσ_u φ hσ, h_conj, h_inv,
      -SemidirectProduct.mk_eq_inl_mul_inr, inflateConj, atPlace_galoisGf, mul_mem_cancel_left,
      map_locMap_mem_intGL_iff, mul_mem_cancel_right, ← MulMemClass.mk_mul_mk]
  · -- Both functions vanish off `K`, so the root `z` for the indicator functions of `K` serves.
    refine (h_pair P ?_ hPσ).elim fun z ⟨hz, h_root⟩ ↦
      ⟨z, hz, fun γ (a : Gf E' n) hγ h_rt ↦ ⟨fun g hg h_eq ↦ ?_, fun δ hδ h_ne ↦ ?_⟩⟩
    · -- `P` comes from the supports of the indicators of `K`, which contain those of the inflations
      revert hP
      gcongr <;> simp +contextual [K, inflateConj, atPlace_baseChangeGf, map_locMap_mem_intGL_iff]
    · -- The indicator functions of `K` agree at `g` and `a`.
      obtain ⟨h_value_eq, -⟩ := h_root γ a hγ h_rt
      have h_int : g.atPlace (u.below E) ∈ intGL n Valued.v.integer ↔
          a.atPlace u ∈ intGL n Valued.v.integer := by
        simpa [K, atPlace_baseChangeGf, map_locMap_mem_intGL_iff] using congrArg (· ≠ 0)
          (h_value_eq g hg h_eq)
      by_cases ha : a.atPlace u ∈ intGL n Valued.v.integer
      · -- The norm of `a` is `g`, so `⟨a, φ⟩ ^ orderOf φ` is `g` after reduction; `S` lifts `Ξ`.
        have h_pow : (⟨reduceGL ⟨_, ha⟩, φ⟩ : GalSemidirect _ _ n) ^ orderOf φ =
            inl ((reduceGL ⟨_, h_int.mpr ha⟩).map (algebraMap _ _)) := by
          obtain ⟨hm, h_reduce⟩ := exists_mk_reduceGL_pow_eq_mk_reduceGL_twistedNorm hσ_u hσ a ha
            (orderOf φ)
          refine h_reduce.trans ?_
          rw [← h_order, ← hg] at h_eq
          simp [h_eq, reduceGL_map_locMap _ _ h_residue,
            atPlace_baseChangeGf]
        have h_prime : (finrank (ResField (u.below E)) (ResField u)).Prime := by
          simpa [h_degree] using hμ.out
        have h_value : S ⟨reduceGL ⟨_, ha⟩, φ⟩ = Ξ.evalGL (reduceGL ⟨_, h_int.mpr ha⟩) :=
          h_lf φ ((hasFixedField_iff_ne_one h_prime).mpr hφ_ne) _ _ rfl h_pow
        simp [h_int, ha, h_value, -SemidirectProduct.mk_eq_inl_mul_inr, inflateConj]
      · simp [h_int, ha, inflateConj]
    · obtain ⟨-, h_coset⟩ := h_root γ a hγ h_rt
      have hδ_int : Gf.atPlace u δ ∈ intGL n Valued.v.integer := by
        by_contra h_not
        simp [h_not, inflateConj] at h_ne
      exact h_coset δ hδ (by simpa [K] using hδ_int)

/-- Let `E'` contain a primitive 5040th root of unity, `w` be split with `μ` trivial on its ideles,
and `u` the only place above `w`, split, of residue degree `[E' : E]`. If the form `f` has the
character `Ξ` as label at `w` and `Ξ'` is a lift of `Ξ` (`New.Lift ℕ`), then some eigenform `f'`
(nonzero, with polynomials `P` at the places of `E'`) over `E'` of weight `κ.baseChange` is a weak
base change of `f` off `w` and `w̄`, with label `Ξ'` at `u`. -/
lemma exists_baseChange_hasLabel [HasPrimitiveRoot5040 E'] {κ : Weight E}
    {f : Gf E n → WeylIndex n κ.1 → ℂ} (hf : f ∈ (stdSpace E n).forms κ)
    (hΞ : IsChar (Ξ.evalGL (n := n))) {Ξ' : Hall (ResField u)} (h_shintani : Lift ℕ Ξ Ξ')
    (h_label : HasLabel f hw Ξ.evalGL) :
    ∃ f' ∈ (stdSpace E' n).forms κ.baseChange, ∃ P : FinPlace E' → Polynomial ℂ,
      IsEigenform f' P ∧ IsWeakBaseChange μ {w} f f' ∧ HasLabel f' hu Ξ'.evalGL := by
  -- Transfer `f` along the matching functions of `isLocalMatching_shintani`. The label of `f` gives
  -- the non-zero trace that `exists_isWeakBaseChange_of_matching` asks for; the transfer lies in
  -- the image of the operator of `S ⟨·, φ⟩`, which gives its label.
  obtain ⟨S, hS, h_lift, h_lift'⟩ := h_shintani.hasCommonLift n
  have hS_char : IsChar S := isChar_of_mem_virtualChars hS
  obtain ⟨φ, h_match⟩ := isLocalMatching_shintani hw hu h_unique hμ_trivial h_residue h_degree
    hS_char.isClassFunction h_lift
  let π := ((stdSpace E n).formTranslation κ).comp (ofSplitPlace hw)
  let K := levelSpace π (localCongruence n w 0)
  let T := heckeFun π (localCongruence n w 0) (inflateConj Ξ.evalGL)
  -- The trace is `classInner Ξ.evalGL ρ.character` up to a factor; if it vanished, the group
  -- algebra element of `conj Ξ` would kill `f`.
  have h_trace (V : Subrepresentation π) (hV : ⟨f, hf⟩ ∈ V) (_ : Module.Finite ℂ ↥(K ⊓ V.1))
      (h_maps : ∀ x ∈ K ⊓ V.1, T x ∈ K ⊓ V.1) : (T.restrict h_maps).trace ℂ ↥(K ⊓ V.1) ≠ 0 := by
    intro h_zero
    obtain ⟨ρ, hρ⟩ := exists_representation_heckeFun_inflateConj hw V
    have hf_fixed : ⟨f, hf⟩ ∈ K := mem_levelSpace.2 fun k ↦ by
      obtain ⟨hk_int, hk_red⟩ := mem_localCongruence_zero.mp k.prop
      obtain ⟨h_fix, -⟩ := h_label
      simpa [π, Subtype.ext_iff] using h_fix ⟨k, hk_int⟩ hk_red
    have h_op : T.restrict h_maps = ρ.asAlgebraHom (groupAlgElem (conj ∘ Ξ.evalGL)) :=
      LinearMap.ext fun x ↦ Subtype.ext (hρ _ x).1
    have h_orth : classInner Ξ.evalGL ρ.character = 0 := by
      rw [← trace_asAlgebraHom_groupAlgElem_conj Ξ.evalGL, ← h_op, h_zero, zero_div]
    have h_kill : ρ.asAlgebraHom (groupAlgElem (starRingEnd ℂ ∘ Ξ.evalGL)) = 0 :=
      hΞ.asAlgebraHom_groupAlgElem_eq_zero_iff.2 h_orth
    obtain ⟨-, h_label_iff⟩ := hρ _ ⟨_, hf_fixed, hV⟩
    exact h_label_iff.mp h_label (LinearMap.congr_fun h_kill _)
  obtain ⟨f', P, h_eig, h_same, -, y, hy, h_image⟩ :=
    exists_isWeakBaseChange_of_matching ⟨f, hf⟩ h_match ![] 0 () rfl (by simp) nofun (by
      rw [heckeGenEigenspace, iInf_of_empty, inf_top_eq]
      exact h_trace)
  obtain ⟨ρ, hρ⟩ := exists_representation_heckeFun_inflateConj (n := n) hu (κ := κ.baseChange) ⊤
  let x := ρ.asAlgebraHom (groupAlgElem fun g ↦ conj (S ⟨g, φ⟩)) ⟨y, hy, trivial⟩
  obtain rfl : f' = x := h_image.symm.trans (hρ _ ⟨y, hy, trivial⟩).1
  obtain ⟨-, h_label_iff⟩ := hρ Ξ'.evalGL x
  refine ⟨_, x.val.prop, P, h_eig, h_same, h_label_iff.mpr fun h_zero ↦ h_eig.1 ?_⟩
  -- The group algebra element `a` of `conj (S ⟨·, φ⟩)` acts as zero in every representation whose
  -- character is orthogonal to `S ∘ inl`. So `a = c * b * a`, with `b` the element of
  -- `conj (S ∘ inl) = conj Ξ'.evalGL` (`IsClassFunction.exists_eq_mul_groupAlgElem_mul`). If `b`
  -- killed `x = a y`, then `x = 0`.
  obtain ⟨c, hc⟩ := (hS_char.comp inl).star.isClassFunction.exists_eq_mul_groupAlgElem_mul _
    fun _ hV ↦ hS_char.star.asAlgebraHom_groupAlgElem_eq_zero inl (inr φ)
      ((hS_char.comp inl).asAlgebraHom_groupAlgElem_eq_zero_iff.1 hV)
  rw [← DescendsTo.iff_comp_inl_eq_evalGL.1 h_lift'] at h_zero
  simpa [x, ← mk_eq_inl_mul_inr, h_zero] using
    congrArg (fun a ↦ ρ.asAlgebraHom a ⟨y, hy, trivial⟩) hc

end New
end
end

/-!
# Tame exponents of inertia and local-global compatibility for labelled forms

Let `w` be a finite place of `E` whose residue field `k_w` has order `q`, let `A` be a valuation
subring of an algebraic closure `Ω` lying over `w`, and let `T` be an injective complex-valued
multiplicative character of an algebraically closed extension `K` of `k_w`.

## Main definitions and results

* `New.GaloisRep.IsTameExponent w A T f s a`: the inertial element `s` moves a `(q ^ f - 1)`-th root
  of a uniformiser by the root of unity that `T` reads as `exp (2πi a / (q ^ f - 1))`.
* `New.GaloisRep.IsLabelledAt`: for a polynomial `c` over the residue field, the polynomial with
  roots `ιℓ ((T ^ a) x)` satisfies a given condition at each such `s`. Here `x` runs over the roots
  of `c`, `ιℓ` is the fixed map from `ℂ` to `PadicAlgCl ℓ`, and `T ^ a` is the `a`-th power of the
  character `T`.
* `New.GaloisRep.IsTameExponent.pow_apply_charName`: comparison with the local Artin map, for
  characters of `k_wˣ`.
* `New.GaloisRep.exists_isTameExponent`: exponents exist when `f` is a factorial.
* `New.GaloisRep.Attached.isLabelledAt`: if an eigenform has, at a split place `w`, a type for
  `GL n` of the residue field given by a label (`New.HasProductLabel`: a polynomial `c` of degree
  `d` and characters `χ l` with multiplicities `t l`, where `d + ∑ l, t l` is the rank and the roots
  of `c` and the names of the `χ l` are all distinct), then inertia at `w` acts on the attached
  Galois representation through the tame characters given by the roots of the polynomial of the
  label (`New.GaloisRep.IsLabelledAt`, `New.GaloisRep.IsTameExponent`). The proof uses base changes
  of prime degree in which `w` is inert to reduce to the case where `c` splits into linear factors.
  That case follows from `New.GaloisRep.Attached.local_global_of_eigencharacter` applied to local
  units.

Notions from other files:
* `New.IsPlaceOver A w`: the valuation subring `A` of `Ω` lies over `w`, that is, an integer of `E`
  is in the maximal ideal of `A` exactly when it lies in `w`.
* `New.Cohomology.centerPrime Ω A`: the integers of `Ω` that lie in the maximal ideal of `A`.
* `New.charName T χ`: the unit of `k_w` that names the character `χ` of `k_wˣ`; the map `χ ↦ x_χ` is
  an isomorphism from the character group of `k_wˣ` to `k_wˣ` that depends on `T`.
* `New.GaloisRep.PolyKillsAt r A s Q`: the polynomial `Q` kills `r s` if `ℓ` is a unit at `A`, and
  kills the action of `s` on the periods of `r` if `A` lies above `ℓ`.

## Relation to the literature

Known result: Local-global compatibility at tame level, away from ℓ and at ℓ. Here it is proved only
at split places, for depth-zero types induced from a squarefree type and characters of the
determinant. It is stated as polynomials that kill inertia elements, without the local Langlands
correspondence, and it is reduced by cyclic base change to the case of sorted tame Iwahori
eigencharacters. Source: Harris, Taylor, The geometry and cohomology of some simple Shimura
varieties (2001); Taylor, Yoshida, J. Amer. Math. Soc. 20 (2007); Barnet-Lamb, Gee, Geraghty,
Taylor, Local-global compatibility for l = p, II (2014), Thm 1.1.

See also `Lib.ClassField.Local.ArtinMap`.
-/

@[expose] public section

/-! ## Tame exponents of inertial elements and inertia acting through labels -/

namespace New.GaloisRep

open NumberField Polynomial Cohomology Ideal Quotient IsAlgClosed IsLocalRing RingHom algebraMap

variable {E : Type} [Field E] [EmbeddedNumberField E] (w : FinPlace E) (A : ClosurePlace)
  {K : Type} [Field K] [Algebra (ResField w) K] (T : MulChar K ℂ) (f : ℕ) (s : Gal(Ω/E)) (a : ℕ)

/-- A ring homomorphism `g : 𝓞 E →+* R` to a field killing `w` factors through `ResField w`. -/
lemma exists_resField_hom {R : Type*} [Field R] (g : 𝓞 E →+* R) (h_le_ker : w.asIdeal ≤ ker g) :
    ∃ j : ResField w →+* R, ∀ x : 𝓞 E, j (algebraMap (𝓞 E) (ResField w) x) = g x :=
  ⟨liftOfSurjective _ (algebraMap_ResField_surjective w)
    ⟨g, fun _ hx ↦ h_le_ker (algebraMap_ResField_eq_zero.1 hx)⟩, liftOfSurjective_comp_apply _ _ _⟩

/-- Witness data for `New.GaloisRep.IsTameExponent`. -/
structure IsTameWitness (φ : 𝓞 Ω →+* K) (π : E) (z : Ω) (t : 𝓞 Ω) : Prop where
  centrePrime_le_ker : centerPrime Ω A ≤ ker φ
  commutes (x : 𝓞 E) : φ (algebraMap (𝓞 E) (𝓞 Ω) x) =
    algebraMap (ResField w) K (algebraMap (𝓞 E) (ResField w) x)
  isUniformiser : IsUniformizer A π
  pow_eq : z ^ (w.q ^ f - 1) = algebraMap E Ω π
  coe_eq : (t : Ω) = s z / z
  map_eq : T (φ t) = Complex.exp (2 * Real.pi * Complex.I / (w.q ^ f - 1 : ℕ)) ^ a

/-- `s` has tame exponent `a` at level `f`: `A` lies over `w`, `f ≠ 0`, `s` lies in the inertia
group of `A`, and there is a witness (`New.GaloisRep.IsTameWitness`). -/
structure IsTameExponent : Prop where
  isPlaceOver : IsPlaceOver A w
  level_ne_zero : f ≠ 0
  mem_inertiaGroup : s ∈ inertiaGroup Gal(Ω/E) A
  exists_witness : ∃ (φ : 𝓞 Ω →+* K) (π : E) (z : Ω) (t : 𝓞 Ω),
    IsTameWitness w A T f s a φ π z t

variable {w A f s a}

open Nat

/-- Inertia acts through the tame characters of level `f` given by the roots of `c`: whenever `s`
has tame exponent `a`, `P` holds for `s` and `∏ x, (X - ιℓ ((T ^ a) x))` over the roots of `c`. -/
def IsLabelledAt {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] (A : ClosurePlace) (T : MulChar K ℂ) (f : ℕ)
    (P : Gal(Ω/E) → (PadicAlgCl ℓ)[X] → Prop) (c : (ResField w)[X]) : Prop :=
  ∀ ⦃s : Gal(Ω/E)⦄ ⦃a : ℕ⦄,
    IsTameExponent w A T f s a → P s ((c.aroots K).map fun x : K ↦ X - C (ιℓ ((T ^ a) x))).prod

/-- Comparison of `IsTameExponent` with the local Artin map: if `s` has tame exponent `a` and is
the local Artin symbol of a unit `u`, then `(T ^ a) (charName T χ) = χ (residue u)`. -/
lemma IsTameExponent.pow_apply_charName [IsFaithfulMulChar K T]
    {hs_dec : s ∈ decompGroup Gal(Ω/E) A} (h_exp : IsTameExponent w A T f s a)
    {u : (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)ˣ}
    (hu : Valued.v u.val = 1) (h_artin : localArtin Gal(Ω/E) A w u = ⟦⟨s, hs_dec⟩⟧)
    (χ : MulChar (ResField w) ℂ) :
    (T ^ a) ((charName T χ).val : ResField w) = χ (residue (LocInt w) ⟨u, hu.le⟩) := by
  obtain ⟨ρ, hρ⟩ := h_exp.exists_witness
  obtain ⟨π, z, t, hw⟩ := hρ
  obtain ⟨k, hk⟩ : w.q - 1 ∣ w.q ^ f - 1 := w.q.sub_one_dvd_pow_sub_one f
  obtain ⟨x, hx⟩ := algebraMap_ResField_surjective w (residue (LocInt w) ⟨u, hu.le⟩)
  have h_res : ρ t ^ k = algebraMap (ResField w) K (residue (LocInt w) ⟨u, hu.le⟩) := by
    have h_sym : A.valuation (s (z ^ k) / z ^ k - algebraMap E Ω x) < 1 :=
      (h_exp.isPlaceOver.valuation_sub_lt_one_iff_of_localArtin_eq hw.isUniformiser hu h_artin
        (by rw [← pow_mul', ← hk, hw.pow_eq])).1 (residue_eq_iff_valuation_sub_lt_one.1 hx.symm)
    rw [map_pow, ← div_pow, ← hw.coe_eq] at h_sym
    have h_cong : t ^ k - algebraMap (𝓞 E) (𝓞 Ω) x ∈ centerPrime Ω A := mem_centerPrime.2 h_sym
    simpa [← hx, hw.commutes, sub_eq_zero] using hw.centrePrime_le_ker h_cong
  rw [← thetaChar_charName T χ, ← h_res]
  exact (thetaChar_apply_pow T Finite.one_lt_card (algebraMap_pow_card_pred_eq_one _)
    (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow h_exp.level_ne_zero w.one_lt_q))
    (by rwa [card_ResField]) hw.map_eq).symm

/-- Every root `x` in `K` of a label `c` of degree `r` over `k_w` satisfies `x ^ (q ^ r! - 1) = 1`
and `x ^ (q ^ d - 1) = 1` for some `1 ≤ d ≤ r`. -/
lemma _root_.New.IsLabel.root_pow_eq_one {c : (ResField w)[X]} {r : ℕ} (h_label : IsLabel r c)
    {x : K} (hx : aeval x c = 0) :
    x ^ (w.q ^ (r)! - 1) = 1 ∧ ∃ d ∈ Set.Icc (1 : ℕ) r, x ^ (w.q ^ d - 1) = 1 := by
  obtain ⟨hmonic, -, hdeg, hc0⟩ := h_label
  set P : (ResField w)[X] := minpoly (ResField w) x
  have hP : Irreducible P := minpoly.irreducible ⟨c, hmonic, hx⟩
  have hd_le : P.natDegree ≤ r := (natDegree_le_natDegree (minpoly.min _ _ hmonic hx)).trans_eq hdeg
  have h_pow {n : ℕ} (hn : n ≠ 0) (hd : P.natDegree ∣ n) : x ^ (w.q ^ n - 1) = 1 := by
    rw [pow_pred_eq_one_iff (one_lt_pow₀ w.one_lt_q hn), ← card_ResField,
      root_pow_card_pow_eq_self_iff hP (minpoly.aeval _ x)]
    exact ⟨fun h0 ↦ hc0 (by simpa [h0, aeval_def, eval₂_at_zero] using hx), hd⟩
  exact ⟨h_pow r.factorial_ne_zero (dvd_factorial hP.natDegree_pos hd_le),
    P.natDegree, ⟨hP.natDegree_pos, hd_le⟩, h_pow hP.natDegree_pos.ne' dvd_rfl⟩

/-- Extend `ResField w →+* K` to `𝓞 Ω →+* K` killing `centerPrime Ω A` when `K` is alg. closed. -/
private lemma exists_ringHom_centrePrime_le_ker [IsAlgClosed K] (hA : IsPlaceOver A w) :
    ∃ ρ : 𝓞 Ω →+* K, centerPrime Ω A ≤ ker ρ ∧ ∀ x : 𝓞 E,
      ρ (algebraMap (𝓞 E) (𝓞 Ω) x) =
        algebraMap (ResField w) K (algebraMap (𝓞 E) (ResField w) x) := by
  have := hA.centerPrime_liesOver; let := Quotient.field w.asIdeal
  algebraize [(algebraMap (ResField w) K).comp
    (Ideal.Quotient.lift w.asIdeal (algebraMap (𝓞 E) (ResField w)) (by simp))]
  let j : (𝓞 Ω ⧸ centerPrime Ω A) →ₐ[𝓞 E ⧸ w.asIdeal] K := IsAlgClosed.lift
  exact ⟨j.toRingHom.comp (Ideal.Quotient.mk _), fun _ ht ↦ by simp [eq_zero_iff_mem.2 ht],
    fun x ↦ j.commutes (Ideal.Quotient.mk w.asIdeal x)⟩

/-- At level `f !` over `A` above `w` (with `IsFaithfulMulChar K T`): (a) some inertia element has
tame exponent `1`; (b) every inertia element `s` has a tame exponent `a`, coprime to `q ^ f ! - 1`
when `s = hA.tameGenerator`. -/
lemma exists_isTameExponent [IsFaithfulMulChar K T] (hA : IsPlaceOver A w) (f : ℕ) :
    (∃ s : inertiaGroup Gal(Ω/E) A, IsTameExponent w A T (f)! s.val 1) ∧
    ∀ s ∈ inertiaGroup Gal(Ω/E) A, ∃ a : ℕ,
      IsTameExponent w A T (f)! s a ∧ (s = hA.tameGenerator → a.Coprime (w.q ^ (f)! - 1)) := by
  let N : ℕ := w.q ^ f.factorial - 1
  have hN_res : NeZero (N : ResField w) := let := Fintype.ofFinite (ResField w);
    ⟨by simp [N, ← card_ResField, f.factorial_ne_zero, NeZero.pos]⟩
  have : NeZero (N : K) := .of_faithfulSMul (ResField w) K N
  have hN : NeZero N := hN_res.of_neZero_natCast
  have hN_val : A.valuation N = 1 := hA.valuation_natCast_eq_one_iff.2 fun hmem ↦
    hN_res.out (mod_cast algebraMap_ResField_eq_zero.2 hmem)
  obtain ⟨ρ, hρ_cen, hρ_int⟩ := exists_ringHom_centrePrime_le_ker (K := K) hA
  obtain ⟨π, z, hπz⟩ := hA.exists_isPrimitiveRoot_tameGenerator_smul_div hN_val
  obtain ⟨hπ, hz, hζ⟩ := hπz
  have hρζ : IsPrimitiveRoot (ρ hζ.toInteger) N := isRoot_cyclotomic_iff.1 <|
    map_cyclotomic N ρ ▸ (isRoot_cyclotomic_iff.2 hζ.toInteger_isPrimitiveRoot).map ρ
  obtain ⟨j, -, hj, hTj⟩ :
      ∃ j < N, j.Coprime N ∧ T (ρ hζ.toInteger) ^ j = Complex.exp (2 * Real.pi * Complex.I / N) :=
    (hρζ.map_of_injective IsFaithfulMulChar.injective).isPrimitiveRoot_iff.1
      (Complex.isPrimitiveRoot_exp N hN.out)
  have hζj : IsPrimitiveRoot ((hA.tameGenerator • z / z) ^ j) N := hζ.pow_of_coprime j hj
  have tame_of_eq (s : inertiaGroup Gal(Ω/E) A) (a : ℕ)
      (hsa : ((hA.tameGenerator • z / z) ^ j) ^ a = s.val z / z) :
      IsTameExponent w A T f.factorial s a :=
    ⟨hA, f.factorial_ne_zero, s.property, ρ, ⟨π, z, (hζ.toInteger ^ j) ^ a,
      { centrePrime_le_ker := hρ_cen, commutes := hρ_int, isUniformiser := hπ,
        pow_eq := hz, coe_eq := hsa, map_eq := by simp only [map_pow, hTj, N] }⟩⟩
  refine ⟨⟨hA.tameGenerator ^ j, tame_of_eq _ 1 <|
    (pow_one _).trans (inertia_pow_smul_div hA.tameGenerator.2 hN_val hz j).symm⟩, fun s hs ↦ ?_⟩
  obtain ⟨a, -, ha⟩ := hζj.eq_pow_of_pow_eq_one (ξ := s z / z) (by simp [div_pow, ← map_pow, hz])
  refine ⟨a, tame_of_eq ⟨s, hs⟩ a ha, fun hs_gen ↦ (hζj.pow_iff_coprime hN.pos a).1 ?_⟩
  rwa [ha, hs_gen]

/-- Tame exponents after an unramified base change. -/
private lemma IsTameExponent.of_unramified {L : Type} [Field L] [EmbeddedNumberField L]
    [Algebra E L] [IsScalarTower E L Ω] {u : FinPlace L} [Algebra (ResField w) (ResField u)]
    {p g : ℕ} {σ : Gal(Ω/L)} (h_exp : IsTameExponent w A T (p * g) (σ.restrictScalars E) a)
    (h_below : u.below E = w) (hAu : IsPlaceOver A u) (h_ram : u.asIdeal.ramificationIdx (𝓞 E) = 1)
    (hq : w.q ^ p = u.q)
    (hj : ∀ x : 𝓞 E, algebraMap (ResField w) (ResField u) (algebraMap (𝓞 E) (ResField w) x) =
      algebraMap (𝓞 L) (ResField u) (algebraMap (𝓞 E) (𝓞 L) x)) :
    ∃ _ : Algebra (ResField u) K,
      IsScalarTower (ResField w) (ResField u) K ∧ IsTameExponent u A T g σ a := by
  subst h_below
  obtain ⟨ρ, hρ⟩ := h_exp.exists_witness
  obtain ⟨π, z, t, hw⟩ := hρ
  obtain ⟨i, hi⟩ := exists_resField_hom u (ρ.comp (algebraMap (𝓞 L) (𝓞 Ω))) <| by
    rw [hAu.centerPrime_liesOver.over]; exact fun _ hx ↦ hw.centrePrime_le_ker hx
  algebraize [i]
  refine ⟨i.toAlgebra, .of_algebraMap_eq fun y ↦ ?_,
    ⟨hAu, right_ne_zero_of_mul h_exp.level_ne_zero, h_exp.mem_inertiaGroup,
      ρ, ⟨algebraMap E L π, z, t,
        { centrePrime_le_ker := hw.centrePrime_le_ker, commutes := fun x ↦ (hi x).symm,
          isUniformiser := by rw [hAu.isUniformizer_iff, ← (u.below E).valuation_liesOver L,
            h_exp.isPlaceOver.isUniformizer_iff.1 hw.isUniformiser, h_ram, pow_one],
          pow_eq := by rw [← hq, ← pow_mul, hw.pow_eq, IsScalarTower.algebraMap_apply E L Ω],
          coe_eq := hw.coe_eq, map_eq := by rw [← hq, ← pow_mul, hw.map_eq] }⟩⟩⟩
  obtain ⟨x, rfl⟩ := algebraMap_ResField_surjective _ y
  change algebraMap (ResField (u.below E)) K _ = i _
  rw [hj, hi, comp_apply, ← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 L), hw.commutes]

end New.GaloisRep

/-! ## Local-global compatibility at a split place for a labelled form -/

section LabelCompatibility

open NumberField Polynomial Ideal Finset Function Module Fin New QZChar

/-- Mapping `y ↦ X - C (g y)` over the roots in `K` of `∏ i, (X - C (α i)) ^ e i`. -/
private lemma prod_map_aroots_prod_X_sub_C_pow {ι k K L : Type*} [Fintype ι] [Field k] [Field K]
    [Algebra k K] [CommRing L] (α : ι → k) (e : ι → ℕ) (g : K → L) :
    (((∏ i : ι, (X - C (α i)) ^ e i).aroots K).map fun y ↦ X - C (g y)).prod =
      ∏ i : ι, (X - C (g (algebraMap k K (α i)))) ^ e i := by
  rw [aroots, Polynomial.map_prod]
  simp_rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  rw [roots_prod _ _ (prod_ne_zero_iff.2 fun i _ ↦ ((monic_X_sub_C _).pow _).ne_zero)]
  simp [Multiset.map_bind, Multiset.map_nsmul, Multiset.prod_nsmul]

/-- Existence of a prime-degree cyclic base change in which a split place `w` is inert. -/
private lemma exists_inertStep {E : Type} [Field E] [EmbeddedNumberField E] [CMType E] [WeilData E]
    {w : FinPlace E} {A : ClosurePlace} {p : ℕ} (hw : w.IsSplit) (hA : IsPlaceOver A w)
    (hp : p.Prime) :
    ∃ (μ : QZChar Gal(Ω/E)) (u : FinPlace (stepField μ)),
      (∃ η : (LocField w)ˣ →* Multiplicative QZ, GaloisRep.IsStepOfLocalChar A η p μ u) ∧
      inertiaGroup Gal(Ω/E) A ≤ ker (symmetrize μ) ∧
      u.asIdeal.ramificationIdx (𝓞 E) = 1 ∧ w.q ^ p = u.q := by
  have : Fact p.Prime := ⟨hp⟩
  let η : (LocField w)ˣ →* Multiplicative QZ :=
    .mk' (fun x ↦ .ofAdd (.ofZMod p (Valued.v x.val).log)) (by simp)
  have hη_unit (x : (LocField w)ˣ) (hx : Valued.v x.val = 1) : η x = 1 := by simp [η, hx]
  obtain ⟨μ, u, h_step⟩ := GaloisRep.exists_isStepOfLocalChar hw hA hp η
    (DFunLike.ne_iff.2 ⟨uniformizer w, by simp [η, map_eq_zero_iff]⟩)
    (fun x ↦ by simp [η, ← ofAdd_nsmul, ← map_nsmul, ZMod.natCast_self])
    (fun x hx ↦ by rw [map_pow, hη_unit x hx, one_pow])
  have h_unram : inertiaGroup Gal(Ω/E) A ≤ ker (symmetrize μ) :=
    (hA.artinAt_units_trivial_iff_inertiaGroup_le (symmetrize μ)).1
      fun x hx ↦ (h_step.abelianLift_symmetrize_artinAt x).trans (hη_unit x hx)
  have h_ram : u.asIdeal.ramificationIdx (𝓞 E) = 1 :=
    (hA.ramification_in_tower (ker (symmetrize μ)) h_step.isPlaceOver).2.1 h_unram
  refine ⟨μ, u, ⟨η, h_step⟩, ⟨h_unram, h_ram, ?_⟩⟩
  have h_below : u.below E = w := (h_step.below_eq_iff u).2 rfl
  have h_in : u.asIdeal.inertiaDeg (𝓞 E) = p := by
    simpa [h_below, h_step.below_eq_iff, h_ram, h_step.finrank_eq] using
      u.ncard_mul_ramificationIdx_mul_inertiaDeg (K := E)
  simp [← h_below, ← h_in, absNorm_pow_inertiaDeg]

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E n : Type} [Nonempty n] [Field E] [CMType E]
  [EmbeddedNumberField E] [Fintype n] [DecidableEq n] {κ : Weight E}
  {f : Gf E n → WeylIndex n κ.1 → ℂ} {P : FinPlace E → ℂ[X]} {r : GalRep ℓ E n}
  {w : FinPlace E} {A : ValuationSubring Ω} {hw : star w ≠ w} {K : Type} [Field K]
  [Algebra (ResField w) K] {T : MulChar K ℂ} [IsFaithfulMulChar K T] {s d : ℕ}
  {c : (ResField w)[X]} {χ : Fin s → MulChar (ResField w) ℂ} {t : Fin s → ℕ} [WeilData E]

/-- Level-`1` case of `New.GaloisRep.Attached.isLabelledAt`, where `c` splits linearly. -/
private lemma New.GaloisRep.Attached.isLabelledAt_one (hf : f ∈ (stdSpace E n).forms κ)
    (he : IsEigenform f P) (hr : Attached P r) (hA : IsPlaceOver A w)
    (h_prod_label : HasProductLabel f hw T d c χ t)
    (h_roots : ∀ x : K, aeval x c = 0 → x ^ (w.q - 1) = 1) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (Fintype.card n)) ∧
    IsLabelledAt A T 1 (PolyKillsAt r A)
      (c * ∏ l : Fin s, (X - C (charName T (χ l)).val) ^ t l) := by
  obtain ⟨h_label, h_sep, h_deg, h_has⟩ := h_prod_label
  obtain ⟨ψ, rfl⟩ := h_label.exists_eq_prod_charName_of_root_pow_card_eq T fun y hy ↦ by
    rw [card_ResField]; exact ((pow_pred_eq_one_iff w.one_lt_q).1 (h_roots y hy)).2
  have h_inj : Injective (append ψ χ) := .of_comp (f := fun η ↦ (charName T η).val) <| by
    simpa [Function.comp_def, ← separable_prod_X_sub_C_iff, prod_univ_add] using h_sep
  let ρ := Patching.localFormRep (stdSpace E n) κ hw
  have h_act (g : GL n (LocField w)) : (ρ (reindexGL (Fintype.equivFin n) g) ⟨f, hf⟩).val =
      rightRegular ℂ (Gf E n) (WeylIndex n κ.1 → ℂ) (ofSplitPlace hw g) f := by
    simp [ρ, Patching.localFormRep, Patching.embedAtSplit]
  have h_fix : ∀ k, reduceGL (w := w) k = 1 →
      ρ (reindexGL (Fintype.equivFin n) k.val) ⟨f, hf⟩ = ⟨f, hf⟩ :=
    fun k hk ↦ Subtype.ext ((h_act k.val).trans (h_has.1 k hk))
  have h_sum : ∑ᶠ g : GL n (ResField w),
      star ((∏ b, (detChar (append ψ χ b)).rankPart (append 1 t b)).evalGL g) •
        ρ (reindexGL (Fintype.equivFin n) (surjInv reduceGL_surjective g).val) ⟨f, hf⟩ ≠ 0 := by
    intro h0
    have h1 := congrArg ((stdSpace E n).forms κ).subtype h0
    rw [map_finsum _ (Set.toFinite _), map_zero] at h1
    exact h_has.2 (by simpa [h_act, prod_univ_add, labelChar_X_sub_C] using h1)
  obtain ⟨z, hz, ξ, h_z⟩ := exists_sorted_of_detChar (ρ := ρ) (x := ⟨f, hf⟩) (v_uniformizer w)
    isUnitary_localFormRep (Fintype.equivFin n) h_inj (m := append 1 t)
    (by simpa [sum_univ_add] using h_deg) h_fix (s := surjInv (reduceGL_surjective (w := w)))
    (surjInv_eq (reduceGL_surjective (w := w))) h_sum
  obtain ⟨lab, h_eig, h_sorted, h_lab⟩ := h_z
  have hez : IsEigenform z.val P := he.of_mem_cyclicSpan hz h_eig.ne_zero
  obtain ⟨h_fin, h_jump, -⟩ := hr.local_global_of_eigencharacter h_eig hez h_sorted hA 1 1 0
    (by simp [← mem_inertiaGroup_iff]) (by simp) (by simp)
  refine ⟨h_fin, h_jump, fun σ a h_tame ↦ ?_⟩
  have hσ := h_tame.mem_inertiaGroup
  obtain ⟨x, hx, hxσ⟩ := hA.exists_localArtin_eq (inv_mem hσ) 0
  have hx_unit : Valued.v x.val = 1 := by simpa using hx
  rw [show (∏ i : Fin d, (X - C (charName T (ψ i)).val)) *
        ∏ l : Fin s, (X - C (charName T (χ l)).val) ^ t l =
      ∏ b : Fin (d + s), (X - C (charName T (append ψ χ b)).val) ^ append 1 t b by
        simp [prod_univ_add], prod_map_aroots_prod_X_sub_C_pow]
  simp_rw [h_tame.pow_apply_charName T hx_unit hxσ]
  rw [← prod_X_sub_C_eq_prod_pow_of_card_fiber h_lab.1 fun i ↦ congrArg ιℓ (h_lab.2 x hx_unit i)]
  exact (hr.local_global_of_eigencharacter h_eig hez h_sorted hA
    ⟨σ, hσ.1⟩ x 0 (inv_mem hσ) hxσ hx).2.2

/-- Level-`g` case (`g ≠ 0`) of `New.GaloisRep.Attached.isLabelledAt`. -/
private lemma New.GaloisRep.Attached.isLabelledAt_of_root_pow_eq_one {g : ℕ}
    (hf : f ∈ (stdSpace E n).forms κ) (he : IsEigenform f P) (hr : Attached P r)
    (hA : IsPlaceOver A w) (h_prod_label : HasProductLabel f hw T d c χ t) (hg : g ≠ 0)
    (h_roots : ∀ x : K, aeval x c = 0 → x ^ (w.q ^ g - 1) = 1) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (Fintype.card n)) ∧
    IsLabelledAt A T g (PolyKillsAt r A)
      (c * ∏ l : Fin s, (X - C (charName T (χ l)).val) ^ t l) := by
  induction g using induction_on_primes generalizing E with
  | zero => exact absurd rfl hg
  | one => exact hr.isLabelledAt_one hf he hA h_prod_label (by simpa using h_roots)
  | prime_mul p g hp ih =>
    obtain ⟨h_label, h_sep, h_deg, h_has⟩ := h_prod_label
    obtain ⟨μ, u, ⟨_, h_step⟩, h_inert⟩ := exists_inertStep hw hA hp
    obtain ⟨h_unram, h_ram, hq⟩ := h_inert
    obtain ⟨_⟩ := h_step.nonempty_weilData
    have : IsStep (stepField μ) (ideleChar μ) := h_step.isStep
    have hAu : IsPlaceOver A u := h_step.isPlaceOver
    have h_below : u.below E = w := (h_step.below_eq_iff u).2 rfl
    obtain ⟨j₀, h_res⟩ := GaloisRep.exists_resField_hom w
      ((algebraMap (𝓞 (stepField μ)) (ResField u)).comp (algebraMap (𝓞 E) _))
      fun _ hx ↦ algebraMap_ResField_eq_zero.2 (by rwa [← h_below] at hx)
    algebraize [j₀]
    let j : ResField w →+* ResField u := algebraMap (ResField w) (ResField u)
    have h_res_rank : finrank (ResField w) (ResField u) = p := Nat.pow_right_injective w.one_lt_q <|
      by change w.q ^ _ = w.q ^ p; rw [hq, ← card_ResField, ← card_ResField,
        ← natCard_eq_pow_finrank]
    -- Given any `ResField w`-embedding `ResField u → K`, Shintani base change descends to `E`.
    have descend [Algebra (ResField u) K] [IsScalarTower (ResField w) (ResField u) K] :
        (IsFiniteTypeAt r A ∧ HasJumpsAt r A (jumps κ (Fintype.card n))) ∧
        ∃ r' : GalRep ℓ (stepField μ) n, DescendsAt μ r' r A ∧
          IsLabelledAt A T g (PolyKillsAt r' A)
            ((c * ∏ l, (X - C (charName T (χ l)).val) ^ t l).map j) := by
      let χ' (l : Fin s) : MulChar (ResField u) ℂ :=
        (charName T).symm (Units.map j.toMonoidHom (charName T (χ l)))
      have hχ' (l : Fin s) : (charName T (χ' l)).val = j (charName T (χ l)).val := by simp [χ']
      have lift_prod {k' : Type} [Field k'] [Finite k'] [Algebra (ResField w) k'] [Algebra k' K]
          [IsScalarTower (ResField w) k' K] {F : Hall (ResField w)} {F' : Hall k'} (h : Lift ℕ F F')
          {η : Fin s → MulChar k' ℂ}
          (hη : ∀ l, (charName T (η l) : k') = algebraMap (ResField w) k' (charName T (χ l))) :
          Lift ℕ (F * ∏ l, (detChar (χ l)).rankPart (t l))
            (F' * ∏ l, (detChar (η l)).rankPart (t l)) :=
        h.mul (prod_hom_rel .one fun l _ _ h_rest ↦
          .mul (.rankPart_of_hasCommonLift (lift_detChar T (hη l) (t l))) h_rest)
      obtain ⟨f', hf', P', h_f'⟩ := exists_baseChange_hasLabel hw h_step.isSplit
        h_step.below_eq_iff (fun _ ↦ by simp [h_step.abelianLift_artinAt]) h_res
        (h_res_rank.trans h_step.finrank_eq.symm) hf
        (isChar_of_mem_virtualChars
          (lift_prod (lift_labelChar_self T h_label) fun _ ↦ rfl).evalGL_mem_virtualChars)
        (lift_prod (shintani_lift_labelChar (by rwa [h_res_rank]) T h_label) hχ') h_has
      obtain ⟨he', h_bc, h_has'⟩ := h_f'
      obtain ⟨r', hr'⟩ := (sphericalCompat_std u hf' he').1
      have h_sep' : (c.map j * ∏ l, (X - C (charName T (χ' l)).val)).Separable := by
        simpa [hχ', Polynomial.map_prod] using h_sep.map (f := j)
      obtain ⟨h_fin, h_jump, h_lab⟩ := ih hf' he' hr' hAu ⟨h_label.map _, h_sep', h_deg, h_has'⟩
        (right_ne_zero_of_mul hg) fun x hx ↦ by
          rw [← hq, ← pow_mul]
          exact h_roots x ((c.aeval_map_algebraMap (ResField u) x).symm.trans hx)
      have h_down : DescendsAt μ r' r A := h_bc.descendsAt hr' he' he hr A
      refine ⟨⟨h_down.isFiniteTypeAt h_fin, h_down.hasJumpsAt _ h_jump⟩, r', h_down, ?_⟩
      rwa [show c.map j * ∏ l, (X - C (charName T (χ' l)).val) ^ t l =
          (c * ∏ l, (X - C (charName T (χ l)).val) ^ t l).map j by
            simp [hχ', Polynomial.map_prod]] at h_lab
    obtain ⟨h_fin, h_jump⟩ : IsFiniteTypeAt r A ∧ HasJumpsAt r A (jumps κ (Fintype.card n)) := by
      let φ : ResField u →ₐ[ResField w] K := IsAlgClosed.lift
      algebraize [φ.toRingHom]
      have : IsScalarTower (ResField w) (ResField u) K :=
        .of_algebraMap_eq fun y ↦ (φ.commutes y).symm
      exact descend.1
    refine ⟨h_fin, h_jump, fun σ a h_tame ↦ ?_⟩
    have hσ := h_tame.mem_inertiaGroup
    obtain ⟨_, _, h_tame'⟩ := h_tame.of_unramified T
      (σ := { σ with commutes' := fun x ↦ x.property ⟨σ, h_unram hσ⟩ }) h_below hAu h_ram hq h_res
    obtain ⟨-, r', h_down, h_lab⟩ := descend
    exact h_down.polyKillsAt ⟨σ, h_unram hσ,
      (hA.artinAt_trivial_iff_decompGroup_le μ).1 h_step.abelianLift_artinAt hσ.1⟩ _ <| by
        have h_kill := h_lab h_tame'; rwa [aroots_map] at h_kill

/-- Let the Galois representation `r` be attached to the Hecke polynomials `P` of the eigenform `f`
of weight `κ`, which has the label `c` (of degree `d`), `χ l`, `t l` at the split place `w`
(`New.HasProductLabel`), and let `A` lie above `w`. Then (a) `r` is of finite type at `A` (finite on
inertia, or potentially crystalline above `ℓ`), (b) it has the Hodge–Tate jumps of `κ`, and (c) if
`σ` has tame exponent `a` at level `d!` (`New.GaloisRep.IsTameExponent`), then
`∏ x, (X - ιℓ ((T ^ a) x))` kills the action of `σ` (`New.GaloisRep.PolyKillsAt`), the product being
over the roots `x` in `K` of `c * ∏ l, (X - x_l) ^ t l`, where `x_l = New.charName T (χ l)`.

This is local-global compatibility at tame level, away from `ℓ` and at `ℓ`, restricted to inertia at
a split place and to depth-zero types.

Clause (c) is a weak form of what this compatibility (Barnet-Lamb–Gee–Geraghty–Taylor, Caraiani)
gives together with the description of the inertial parameters of depth-zero representations of
`GL_n` (see Emerton–Gee–Herzig). -/
lemma New.GaloisRep.Attached.isLabelledAt (hf : f ∈ (stdSpace E n).forms κ) (he : IsEigenform f P)
    (hr : Attached P r) (h_prod_label : HasProductLabel f hw T d c χ t) (hA : IsPlaceOver A w) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (Fintype.card n)) ∧
    IsLabelledAt A T d.factorial (PolyKillsAt r A)
      (c * ∏ l : Fin s, (X - C (charName T (χ l)).val) ^ t l) :=
  hr.isLabelledAt_of_root_pow_eq_one hf he hA h_prod_label d.factorial_ne_zero
    fun _ hx ↦ (h_prod_label.1.root_pow_eq_one hx).1

end LabelCompatibility
