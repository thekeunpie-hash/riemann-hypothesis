module

import Mathlib.Topology.Algebra.Group.Units
public import Lib.ClassField.GreenbergWiles.RelationsModL
public import Lib.GaloisRep.Main.Defs
public import New.Congruences.FirstOrder.EvenClasses
import Lib.ClassField.GaloisCohomology.TameSelmerCocycles
import Lib.ClassField.Global.AlbertBrauerHasseNoether
import Mathlib.Algebra.Azumaya.Basic
public import Lib.GaloisRep.TaylorWiles
import Lib.Cyclotomic.OddSha
import Lib.GaloisRep.Main.QuadraticStep
import Lib.General.NumberTheory.FrobeniusOrbits

section
/-!
# Kummer maps

Throughout, `ℓ` is a prime and `E` is a CM field in the algebraic closure `Ω` of `ℚ` that contains a
primitive `5040`-th root of unity (`New.CMFieldWithRoot5040`). We pass from `E` to its maximal real
subfield `F`. We write `G = Gal(Ω/E)` and `G_F = Gal(Ω/F)`, `c` for the chosen complex conjugation
and `G_ν` for the elements of `G` that fix the `ℓ ^ ν`-th roots of unity. A Kummer map is the
restriction to `G` of a relation over `F` for the module `ℤ/ℓ^ν` on which `G_F` acts by a power of
`cyc⁺`, the extension to `G_F` of the cyclotomic character of `G` that is `1` at `c`.

* `New.Selmer.IsNuSplitPlace`: a prime of degree one off `ℓ` with a Frobenius element in `G_ν`.
* `New.Selmer.IsKummerMap`, `New.Selmer.IsKummerMap.hasKummerType`: Kummer maps are odd
  homomorphisms on `G_ν`, and conjugation by `g` multiplies those of exponent `e` by
  `cyc(g) ^ (e + 1)`.
* `New.Selmer.IsKummerMap.sum_eq_zero`: the reciprocity law for Kummer maps and even classes;
  `New.Selmer.IsKummerMap.nsmul_apply_tameGenerator_eq_zero` is the case where one term is left.
* `New.Selmer.exists_card_lt_finrank_kummerReductions`: there are many Kummer maps modulo `ℓ`.

Notions from other files:
* `New.FrobeniusDatum`: a prime `w` of `E` of prime norm, a place `valuationSubring` of `Ω` above it
  and a geometric Frobenius element `frob` at that place.
* `New.RelationSetting`: a discrete Galois module with local conditions;
  `New.RelationSetting.relations` is the module of relations off a finite set `T` of primes, in
  place of dual cocycles; `New.Selmer.IsKummerMap` spells the notion out in the case used here.
* `New.Selmer.evenClasses`: for a coefficient ring `O` and a set `S` of primes of `E`, the even
  classes in `(O/ℓ^ν)(-e)` that are unramified off `ℓ`, `S` and `S̄` and vanish on
  `shaLocalSet ℓ E 1`, the elements of `ker cyc` in decomposition groups above `ℓ`.
* `New.cyclotomicCharMod`: the cyclotomic character modulo `N`; `New.cyclotomicChar` is the `ℓ`-adic
  one, written `cyc`.
-/

@[expose] public section

noncomputable section

namespace New.Selmer

open NumberField Cohomology IsCMField Function Fintype PadicInt Subgroup Finset DiscreteModule QZ

variable {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E] [CMFieldWithRoot5040 E]

/-- The datum `x` (a prime of degree one, a place above it and a Frobenius element) is `ν`-split if
its prime does not lie above `ℓ` and its Frobenius element fixes the `ℓ ^ ν`-th roots of unity. -/
def IsNuSplitPlace (ν : ℕ) (x : FrobeniusDatum E) : Prop :=
  (ℓ : 𝓞 E) ∉ x.place.asIdeal ∧ cyclotomicCharMod Ω (ℓ ^ ν) x.frob = 1

/-- The prime of the maximal real subfield `F` below a prime of `E`. -/
abbrev primeBelowPlus (w : FinPlace E) : FinPlace (maximalRealSubfield E) :=
  w.below (maximalRealSubfield E)

lemma primeBelowPlus_star (w : FinPlace E) : primeBelowPlus (star w) = primeBelowPlus w := by
  ext x
  have h_star : star (algebraMap _ (𝓞 E) x) = algebraMap _ (𝓞 E) x :=
    Subtype.ext (mem_maximalRealSubfield_iff_star_eq.1 (x : maximalRealSubfield E).property)
  change algebraMap _ (𝓞 E) x ∈ (star w).asIdeal ↔ algebraMap _ (𝓞 E) x ∈ w.asIdeal
  rw [mem_star_place, h_star]

lemma q_primeBelowPlus (x : FrobeniusDatum E) : (primeBelowPlus x.place).q = x.place.q :=
  (x.prime_q.pow_eq_iff.1
    (Ideal.absNorm_pow_inertiaDeg (primeBelowPlus x.place).asIdeal x.place.asIdeal)).left

/-! ### Passing to the maximal real subfield -/

variable (E) in
/-- The inclusion of `G = Gal(Ω/E)` in `G_F = Gal(Ω/F)`, for `F` the maximal real subfield of
`E`. -/
def toGalPlus : Gal(Ω/E) →* Gal(Ω/maximalRealSubfield E) :=
  AlgEquiv.restrictScalarsHom (maximalRealSubfield E)

variable (E) in
/-- The chosen complex conjugation `c` (`New.cmConj`) as an element of `G_F`. -/
def conjPlus : Gal(Ω/maximalRealSubfield E) :=
  { cmConj with
    commutes' x := by
      change cmConj (algebraMap E Ω x) = algebraMap E Ω x
      rw [cmConj_algebraMap, mem_maximalRealSubfield_iff_star_eq.1 x.property] }

lemma isOpenEmbedding_toGalPlus : Topology.IsOpenEmbedding (toGalPlus E) :=
  isOpenEmbedding_galois_restrict (toGalPlus E) fun _ _ ↦ rfl

lemma index_range_toGalPlus : (toGalPlus E).range.index = 2 := by
  rw [index_range_eq_finrank_of_smul_eq_smul (K := maximalRealSubfield E) (L := E)
    (toGalPlus E) (fun _ _ ↦ rfl), Algebra.IsQuadraticExtension.finrank_eq_two]

lemma isComplexConj_conjPlus : IsComplexConj (conjPlus E) := isComplexConj_cmConj

lemma conjPlus_mul_self : conjPlus E * conjPlus E = 1 := isComplexConj_conjPlus.mul_self

lemma isFrob_toGalPlus_iff {A : ClosurePlace} {q : ℕ} {g : Gal(Ω/E)} :
    IsFrob A q (toGalPlus E g) ↔ IsFrob A q g := Iff.rfl

/-- The inertia group in `G` of a place `A` of `Ω` is the preimage of the one in `G_F`. -/
lemma toGalPlus_mem_inertiaGroup_iff {A : ClosurePlace} {g : Gal(Ω/E)} :
    toGalPlus E g ∈ inertiaGroup Gal(Ω/maximalRealSubfield E) A ↔ g ∈ inertiaGroup Gal(Ω/E) A :=
  Iff.rfl

lemma cyclotomicChar_toGalPlus (g : Gal(Ω/E)) :
    cyclotomicChar Ω ℓ (toGalPlus E g) = cyclotomicChar Ω ℓ g := rfl

lemma toGalPlus_conjGal (g : Gal(Ω/E)) :
    toGalPlus E (conjGal g) = conjPlus E * toGalPlus E g * conjPlus E := rfl

/-- No complex conjugation lies in `Gal(Ω/E)`, because `E` is totally complex. -/
lemma notMem_range_toGalPlus {c : Gal(Ω/maximalRealSubfield E)} (hc : IsComplexConj c) :
    c ∉ (toGalPlus E).range := by
  rintro ⟨s, rfl⟩
  exact hc.false_of_isTotallyComplex (c := s)

open Classical in
/-- Let `F` be the maximal real subfield of `E` and `G_F = Gal(Ω/F)`. For `σ ∈ G_F`, either `σ` or
`σ c` is the image of some `g` in `G = Gal(Ω/E)` under `toGalPlus E`, where `c` (`conjPlus E`) is
the chosen complex conjugation. -/
lemma exists_toGalPlus_eq_ite (σ : Gal(Ω/maximalRealSubfield E)) :
    ∃ g : Gal(Ω/E), toGalPlus E g = if σ ∈ (toGalPlus E).range then σ else σ * conjPlus E := by
  rw [← MonoidHom.mem_range]
  split_ifs with hσ
  · exact hσ
  · rw [mul_mem_iff_of_index_two index_range_toGalPlus]
    exact iff_of_false hσ (notMem_range_toGalPlus isComplexConj_conjPlus)

/-- The map from `G_F = G ∪ G c` to `G = Gal(Ω/E)` that sends `g` and `g c` to `g`, for `g ∈ G` and
`c` the chosen complex conjugation. -/
def ofGalPlus (σ : Gal(Ω/maximalRealSubfield E)) : Gal(Ω/E) := (exists_toGalPlus_eq_ite σ).choose

open Classical in
lemma toGalPlus_ofGalPlus (σ : Gal(Ω/maximalRealSubfield E)) :
    toGalPlus E (ofGalPlus σ) = if σ ∈ (toGalPlus E).range then σ else σ * conjPlus E :=
  (exists_toGalPlus_eq_ite σ).choose_spec

lemma toGalPlus_ofGalPlus_of_mem {σ : Gal(Ω/maximalRealSubfield E)}
    (hσ : σ ∈ (toGalPlus E).range) : toGalPlus E (ofGalPlus σ) = σ :=
  (toGalPlus_ofGalPlus σ).trans (ite_eq_left hσ)

lemma toGalPlus_ofGalPlus_of_notMem {σ : Gal(Ω/maximalRealSubfield E)}
    (hσ : σ ∉ (toGalPlus E).range) : toGalPlus E (ofGalPlus σ) = σ * conjPlus E :=
  (toGalPlus_ofGalPlus σ).trans (ite_eq_right hσ)

@[simp] lemma ofGalPlus_toGalPlus (g : Gal(Ω/E)) : ofGalPlus (toGalPlus E g) = g :=
  isOpenEmbedding_toGalPlus.injective (toGalPlus_ofGalPlus_of_mem ⟨g, rfl⟩)

/-- Let `F` be the maximal real subfield of the CM field `E`, let `Ω` be the algebraic closure of
`ℚ` and `c` the chosen complex conjugation. The map `ofGalPlus : Gal(Ω/F) → Gal(Ω/E)`, which sends
`g` and `g c` to `g` for `g ∈ Gal(Ω/E)`, is continuous. -/
lemma continuous_ofGalPlus : Continuous (ofGalPlus (E := E)) := by
  classical
  -- The two cosets are open and closed, and the map is continuous on each.
  have h_open : IsOpen ((toGalPlus E).range : Set Gal(Ω/maximalRealSubfield E)) :=
    isOpenEmbedding_toGalPlus.isOpen_range
  have h_front : frontier {σ : Gal(Ω/maximalRealSubfield E) | σ ∈ (toGalPlus E).range} = ∅ :=
    IsClopen.frontier_eq ⟨(toGalPlus E).range.isClosed_of_isOpen h_open, h_open⟩
  have h_cont : Continuous fun σ : Gal(Ω/maximalRealSubfield E) ↦
      if σ ∈ (toGalPlus E).range then σ else σ * conjPlus E :=
    continuous_id.if (fun σ hσ ↦ (h_front.subset hσ).elim) (by fun_prop)
  exact isOpenEmbedding_toGalPlus.isInducing.continuous_iff.2
    (h_cont.congr fun σ ↦ (toGalPlus_ofGalPlus σ).symm)

/-- The map `ofGalPlus` from `G_F = G ∪ G c` to `G = Gal(Ω/E)`, which sends `g` and `g c` to `g`,
is multiplicative up to replacing the second factor `s` by `conjGal s = c s c`. Here `c` is the
chosen complex conjugation. -/
lemma ofGalPlus_mul_eq_or (g h : Gal(Ω/maximalRealSubfield E)) :
    ofGalPlus (g * h) = ofGalPlus g * ofGalPlus h ∨
      ofGalPlus (g * h) = ofGalPlus g * conjGal (ofGalPlus h) := by
  classical
  have h_mem : g * h ∈ (toGalPlus E).range ↔
      (g ∈ (toGalPlus E).range ↔ h ∈ (toGalPlus E).range) :=
    mul_mem_iff_of_index_two index_range_toGalPlus
  have h_cancel (σ : Gal(Ω/maximalRealSubfield E)) : conjPlus E * (conjPlus E * σ) = σ := by
    simp [← mul_assoc, conjPlus_mul_self]
  -- The first equation holds for `g ∈ G`, the second one for `g ∈ G c`; we compare in `G_F`.
  by_cases hg : g ∈ (toGalPlus E).range
  · refine .inl (isOpenEmbedding_toGalPlus.injective ?_)
    simp [-MonoidHom.mem_range, toGalPlus_ofGalPlus, h_mem, hg, mul_assoc]
  · refine .inr (isOpenEmbedding_toGalPlus.injective ?_)
    simp [-MonoidHom.mem_range, toGalPlus_conjGal, toGalPlus_ofGalPlus, h_mem, hg, mul_assoc,
      h_cancel, conjPlus_mul_self]

/-- Let `E` be a CM field in the algebraic closure `Ω` of `ℚ` that contains a primitive `5040`-th
root of unity, and let `F` be its maximal real subfield. Then `E / F` is unramified at the finite
places: the inertia group in `Gal(Ω/F)` of a place `A` of `Ω` above a prime `v` of `F` lies in the
image of the inclusion `toGalPlus E` of `Gal(Ω/E)` in `Gal(Ω/F)`. -/
lemma inertiaGroup_le_range_toGalPlus (A : ClosurePlace) {v : FinPlace (maximalRealSubfield E)}
    (hA : IsPlaceOver A v) :
    inertiaGroup Gal(Ω/maximalRealSubfield E) A ≤ (toGalPlus E).range := by
  intro g hg
  by_contra h_notMem
  -- Otherwise `g` acts on `E` as complex conjugation. There is an integer `y` of `E` such that
  -- `y - star y` is a unit, and this unit would lie in the prime below `A`.
  obtain ⟨w, hw, -⟩ := hA.exists_above (L := E)
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, IsUnit (y - star y) := HasPrimitiveRoot5040.exists_isUnit_sub_star
  have g_star : g (algebraMap E Ω (star (y : E))) = algebraMap E Ω y := by
    have h_fix : toGalPlus E (ofGalPlus g) (algebraMap E Ω y) = algebraMap E Ω y :=
      (ofGalPlus g).commutes y
    rw [toGalPlus_ofGalPlus_of_notMem h_notMem] at h_fix
    simpa [conjPlus] using h_fix
  obtain ⟨-, h_inertia : ∀ z : Ω, A.valuation z ≤ 1 → A.valuation (g • z - z ^ 1) < 1⟩ := hg
  have h_val : A.valuation (algebraMap E Ω (y - star y : 𝓞 E)) < 1 := by
    simpa [g_star] using h_inertia (algebraMap E Ω (star (y : E)))
      (A.valuation_le_one ⟨_, algebraMap_ringOfIntegers_mem A (star y)⟩)
  exact w.asIdeal.notMem_of_isUnit hy ((hw (y - star y)).1 h_val)

/-- Let `F` be the maximal real subfield of `E`, `G = Gal(Ω/E)` and `G_F = Gal(Ω/F)`. The map
`ofGalPlus : G_F → G`, a left inverse of the inclusion, sends the inertia groups above a set `W` of
primes of `F` into the inertia groups above the primes of `E` over `W`. -/
lemma ofGalPlus_mem_inertiaAbove {W : Set (FinPlace (maximalRealSubfield E))}
    {g : Gal(Ω/maximalRealSubfield E)} (hg : g ∈ inertiaAbove W) :
    ofGalPlus g ∈ inertiaAbove (primeBelowPlus ⁻¹' W) := by
  obtain ⟨v, hv, A, hA, hgA⟩ := hg
  obtain ⟨s, rfl⟩ : ∃ s : Gal(Ω/E), toGalPlus E s = g := inertiaGroup_le_range_toGalPlus A hA hgA
  obtain ⟨w, hw, rfl⟩ : ∃ w : FinPlace E, IsPlaceOver A w ∧ primeBelowPlus w = v := hA.exists_above
  exact ⟨w, hv, A, hw, by simpa using toGalPlus_mem_inertiaGroup_iff.1 hgA⟩

variable (ℓ E) in
/-- The character `cyc⁺` of `G_F`: the cyclotomic character times the quadratic character that
cuts out `E`. It is `cyc` on `G` and `1` at `c`. -/
def cyclotomicPlus : Gal(Ω/maximalRealSubfield E) →* ℤ_[ℓ]ˣ :=
  .mk' (fun g : Gal(Ω/maximalRealSubfield E) ↦ cyclotomicChar Ω ℓ (ofGalPlus g)) fun g h ↦ by
    rcases ofGalPlus_mul_eq_or g h with h_mul | h_mul <;> simp [h_mul]

lemma cyclotomicPlus_apply (g : Gal(Ω/maximalRealSubfield E)) :
    cyclotomicPlus ℓ E g = cyclotomicChar Ω ℓ (ofGalPlus g) := rfl

lemma continuous_cyclotomicPlus : Continuous (cyclotomicPlus ℓ E) :=
  ((continuous_cyclotomicChar ℓ).comp continuous_ofGalPlus).congr fun g ↦
    (cyclotomicPlus_apply g).symm

/-- The character `cyc⁺` is unramified off `ℓ`: it is `1` on the inertia groups above the primes of
`F` that do not divide `ℓ`. -/
lemma cyclotomicPlus_eq_one_of_mem_inertiaAbove {g : Gal(Ω/maximalRealSubfield E)}
    (hg : g ∈ inertiaAbove (placesDividing (maximalRealSubfield E) ℓ)ᶜ) :
    cyclotomicPlus ℓ E g = 1 := by
  have h_mem : ofGalPlus g ∈ inertiaAbove (placesDividing E ℓ)ᶜ := by
    simpa [placesDividing] using ofGalPlus_mem_inertiaAbove hg
  exact (cyclotomicPlus_apply g).trans (cyclotomicChar_eq_one_of_mem_inertiaAbove h_mem)

/-- The character `cyc⁺` of `G_F` is `1` at every complex conjugation. -/
lemma cyclotomicPlus_eq_one_of_isComplexConj {c : Gal(Ω/maximalRealSubfield E)}
    (hc : IsComplexConj c) : cyclotomicPlus ℓ E c = 1 := by
  rw [cyclotomicPlus_apply, ← cyclotomicChar_toGalPlus,
    toGalPlus_ofGalPlus_of_notMem (notMem_range_toGalPlus hc), map_mul,
    hc.cyclotomicChar_eq_neg_one ℓ, isComplexConj_conjPlus.cyclotomicChar_eq_neg_one ℓ,
    neg_mul_neg, one_mul]

variable (ℓ E) in
/-- The subgroup `G_ν` of the elements of `G` that fix the `ℓ ^ ν`-th roots of unity, as an open
normal subgroup of `G_F`. -/
def cyclotomicKerPlus (ν : ℕ) : OpenNormalSubgroup Gal(Ω/maximalRealSubfield E) :=
  haveI : (toGalPlus E).range.Normal := normal_of_index_eq_two index_range_toGalPlus
  .mk ⟨(toGalPlus E).range ⊓ (cyclotomicCharMod Ω (ℓ ^ ν)).ker,
    isOpenEmbedding_toGalPlus.isOpen_range.inter isOpen_ker_cyclotomicCharMod.out⟩

@[simp] lemma toGalPlus_mem_cyclotomicKerPlus_iff {ν : ℕ} {g : Gal(Ω/E)} :
    toGalPlus E g ∈ cyclotomicKerPlus ℓ E ν ↔ cyclotomicCharMod Ω (ℓ ^ ν) g = 1 :=
  and_iff_right ⟨g, rfl⟩

variable (ℓ E) in
/-- The character `cyc⁺` of `G_F` modulo `ℓ ^ ν`. -/
def cyclotomicPlusMod (ν : ℕ) : Gal(Ω/maximalRealSubfield E) →* (ZMod (ℓ ^ ν))ˣ :=
  (Units.map (toZModPow ν).toMonoidHom).comp (cyclotomicPlus ℓ E)

lemma cyclotomicPlusMod_apply (ν : ℕ) (g : Gal(Ω/maximalRealSubfield E)) :
    cyclotomicPlusMod ℓ E ν g = cyclotomicCharMod Ω (ℓ ^ ν) (ofGalPlus g) := by
  simp [cyclotomicPlusMod, cyclotomicCharMod_prime_pow_eq, cyclotomicPlus_apply]

lemma cyclotomicKerPlus_le_ker (ν : ℕ) :
    (cyclotomicKerPlus ℓ E ν).toSubgroup ≤ (cyclotomicPlusMod ℓ E ν).ker := by
  intro g hg
  obtain ⟨s, rfl⟩ := (mem_inf.1 hg).left
  simpa [cyclotomicPlusMod_apply] using toGalPlus_mem_cyclotomicKerPlus_iff.1 hg

lemma isOpen_ker_cyclotomicPlusMod (ν : ℕ) :
    IsOpen ((cyclotomicPlusMod ℓ E ν).ker : Set Gal(Ω/maximalRealSubfield E)) :=
  isOpen_mono (cyclotomicKerPlus_le_ker ν) (cyclotomicKerPlus ℓ E ν).isOpen

variable (ℓ E) in
/-- The module `ℤ/ℓ^ν` with `G_F` acting by `(cyc⁺) ^ (-e)`. -/
abbrev tateTwistPlus (ν e : ℕ) : DiscreteModule (ZMod (ℓ ^ ν)) Gal(Ω/maximalRealSubfield E) :=
  .of (charRep (ZMod (ℓ ^ ν)) (cyclotomicPlusMod ℓ E ν ^ e)⁻¹)
    (((Continuous.of_isOpen_ker _ (isOpen_ker_cyclotomicPlusMod ν)).pow e).inv.fst'.smul
      continuous_snd)

lemma tateTwistPlus_ρ (ν e : ℕ) (g : Gal(Ω/maximalRealSubfield E)) (a : ZMod (ℓ ^ ν)) :
    (tateTwistPlus ℓ E ν e).ρ g a = ((cyclotomicPlusMod ℓ E ν g ^ e)⁻¹).val * a := rfl

/-- An element of the kernel of `cyc⁺` modulo `ℓ ^ ν` acts trivially on `ℤ/ℓ^ν` twisted by
`(cyc⁺) ^ (-e)`. -/
lemma tateTwistPlus_ρ_eq_one {ν : ℕ} (e : ℕ) {g : Gal(Ω/maximalRealSubfield E)}
    (hg : cyclotomicPlusMod ℓ E ν g = 1) : (tateTwistPlus ℓ E ν e).ρ g = 1 :=
  LinearMap.ext fun a ↦ (tateTwistPlus_ρ ν e g a).trans (by simp [hg])

lemma cyclotomicPlusMod_eq_one (ν : ℕ) {g : Gal(Ω/maximalRealSubfield E)}
    (hg : cyclotomicPlus ℓ E g = 1) : cyclotomicPlusMod ℓ E ν g = 1 := by
  simp [cyclotomicPlusMod, hg]

section Kummer

variable {ν : ℕ} (e : ℕ) {I : Type}

open Classical in
/-- A place of `Ω` above each prime `u` of `F`; if `u` lies below a member of the family `x`, it is
the place of such a member. -/
def familyPlace (x : I → FrobeniusDatum E) (u : FinPlace (maximalRealSubfield E)) : ClosurePlace :=
  if h : ∃ i : I, primeBelowPlus (x i).place = u then (x h.choose).valuationSubring else placeOver u

/-- If the prime `u` of `F` lies below a member of the family `x`, then `familyPlace x u` is the
place of such a member. -/
lemma exists_familyPlace_eq {x : I → FrobeniusDatum E} {u : FinPlace (maximalRealSubfield E)}
    (hu : ∃ i : I, primeBelowPlus (x i).place = u) :
    ∃ i : I, primeBelowPlus (x i).place = u ∧ familyPlace x u = (x i).valuationSubring :=
  ⟨hu.choose, hu.choose_spec, dite_eq_left hu⟩

/-- The place `familyPlace x u` of `Ω` lies above the prime `u` of `F`. -/
lemma isPlaceOver_familyPlace {x : I → FrobeniusDatum E} (u : FinPlace (maximalRealSubfield E)) :
    IsPlaceOver (familyPlace x u) u := by
  by_cases hu : ∃ i : I, primeBelowPlus (x i).place = u
  · obtain ⟨i, rfl, h_place⟩ := exists_familyPlace_eq hu
    simpa [h_place] using (x i).isPlaceOver.isPlaceOver_below
  · simpa [familyPlace, hu] using u.isPlaceOver_placeOver

/-- If the prime `u` of `F` lies below a member of the family `x`, then for some `i` the inverse of
the geometric Frobenius element of `x i` is an arithmetic Frobenius element of `G_F` (for the norm
`u.q` of `u`) at `familyPlace x u`, the chosen place of `Ω` above `u`. -/
lemma exists_isFrob_familyPlace {x : I → FrobeniusDatum E} {u : FinPlace (maximalRealSubfield E)}
    (hu : ∃ i : I, primeBelowPlus (x i).place = u) :
    ∃ i : I, IsFrob (familyPlace x u) u.q (toGalPlus E (x i).frob⁻¹) := by
  obtain ⟨i, rfl, h_place⟩ := exists_familyPlace_eq hu
  exact ⟨i, by simpa [h_place, q_primeBelowPlus, isFrob_toGalPlus_iff, -map_inv]
    using (x i).isFrob_inv⟩

variable (ℓ) in
/-- The set `S₀` of the primes of `F` above `ℓ` or below a member of the finite family `x`. -/
def familyPrimes [Finite I] (x : I → FrobeniusDatum E) :
    Finset (FinPlace (maximalRealSubfield E)) :=
  (Set.toFinite (placesDividing (maximalRealSubfield E) ℓ ∪
    Set.range fun i : I ↦ primeBelowPlus (x i).place)).toFinset

lemma mem_familyPrimes [Finite I] {x : I → FrobeniusDatum E}
    {u : FinPlace (maximalRealSubfield E)} :
    u ∈ familyPrimes ℓ x ↔
      (ℓ : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal ∨ ∃ i : I, primeBelowPlus (x i).place = u :=
  Set.Finite.mem_toFinset _

/-- Let `F` be the maximal real subfield of `E`, `x` a finite family of `ν`-split places and `u` a
prime of `F` off `ℓ` below a member of `x`. Then the decomposition group of `familyPlace x u`, the
chosen place above `u`, lies in the kernel of `cyc⁺` modulo `ℓ ^ ν`, because inertia and a Frobenius
element do. -/
lemma cyclotomicPlusMod_eq_one_of_mem_decompGroup {x : I → FrobeniusDatum E}
    (hx : ∀ i : I, IsNuSplitPlace ν (x i)) {u : FinPlace (maximalRealSubfield E)}
    (hu : ∃ i : I, primeBelowPlus (x i).place = u)
    (hℓ : (ℓ : 𝓞 (maximalRealSubfield E)) ∉ u.asIdeal) {g : Gal(Ω/maximalRealSubfield E)}
    (hg : g ∈ decompGroup Gal(Ω/maximalRealSubfield E) (familyPlace x u)) :
    cyclotomicPlusMod ℓ E ν g = 1 := by
  have h_place : IsPlaceOver (familyPlace x u) u := isPlaceOver_familyPlace u
  obtain ⟨i, hi⟩ : ∃ i : I, IsFrob (familyPlace x u) u.q (toGalPlus E (x i).frob⁻¹) :=
    exists_isFrob_familyPlace hu
  obtain ⟨-, h_cyc : cyclotomicCharMod Ω (ℓ ^ ν) (x i).frob = 1⟩ := hx i
  have h_frob : toGalPlus E (x i).frob⁻¹ ∈ (cyclotomicPlusMod ℓ E ν).ker := by
    rw [MonoidHom.mem_ker, cyclotomicPlusMod_apply, ofGalPlus_toGalPlus, map_inv, h_cyc, inv_one]
  have h_inertia :
      inertiaGroup Gal(Ω/maximalRealSubfield E) (familyPlace x u) ≤ (cyclotomicPlusMod ℓ E ν).ker :=
    fun a ha ↦ cyclotomicPlusMod_eq_one ν
      (cyclotomicPlus_eq_one_of_mem_inertiaAbove ⟨u, hℓ, _, h_place, ha⟩)
  exact h_place.decompGroup_le hi (isOpen_ker_cyclotomicPlusMod ν) h_inertia h_frob hg

/-- The setting over `F` for the exponent `e` and a finite family `x` of `ν`-split places: the
module `ℤ/ℓ^ν` with the action `(cyc⁺) ^ (-e)`, the subgroup `G_ν`, and the set `S₀` of the primes
of `F` above `ℓ` or below `x`. The local condition at a prime `u` consists of the functions on the
decomposition group of `familyPlace x u` that vanish on its part in `ker cyc⁺` if `u` lies above
`ℓ`, and that vanish everywhere otherwise. -/
def kummerSetting [Finite I] {x : I → FrobeniusDatum E} (hx : ∀ i : I, IsNuSplitPlace ν (x i)) :
    RelationSetting (tateTwistPlus ℓ E ν e) (ℓ ^ ν) where
  nsmul_eq_zero a := by simp [CharP.cast_eq_zero]
  subgroup := cyclotomicKerPlus ℓ E ν
  apply_eq_of_mem g hg a := LinearMap.congr_fun
    (tateTwistPlus_ρ_eq_one e (cyclotomicKerPlus_le_ker ν hg)) a
  cyclotomicCharMod_eq_one _ hg := (mem_inf.1 hg).right
  notMem_of_isComplexConj hc hc_mem := notMem_range_toGalPlus hc (mem_inf.1 hc_mem).left
  ρ_eq_one_of_isComplexConj hc :=
    tateTwistPlus_ρ_eq_one e (cyclotomicPlusMod_eq_one ν
      (cyclotomicPlus_eq_one_of_isComplexConj hc))
  localPrimes := familyPrimes ℓ x
  unramified := by
    rintro g ⟨u, hu, hg⟩
    exact tateTwistPlus_ρ_eq_one e (cyclotomicPlusMod_eq_one ν
      (cyclotomicPlus_eq_one_of_mem_inertiaAbove
      ⟨u, fun hℓ ↦ hu (mem_familyPrimes.2 (.inl hℓ)), hg⟩))
  place := familyPlace x
  isPlaceOver := isPlaceOver_familyPlace
  allowed u := .pi {g | (ℓ : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal → cyclotomicPlus ℓ E g = 1} ⊥
  coboundary_le u hu := by
    rintro _ ⟨a, rfl⟩ g hg
    have g_triv : cyclotomicPlusMod ℓ E ν g = 1 := by
      by_cases hℓ : (ℓ : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
      exacts [cyclotomicPlusMod_eq_one ν (hg hℓ), cyclotomicPlusMod_eq_one_of_mem_decompGroup hx
        ((mem_familyPrimes.1 hu).resolve_left hℓ) hℓ g.property]
    change (tateTwistPlus ℓ E ν e).ρ g a - a = 0
    simp [tateTwistPlus_ρ_eq_one e g_triv]

/-- A Kummer map of exponent `e` off `T` for the family `x` of `ν`-split places: the restriction to
`G` of a relation off `T` in `kummerSetting e hx`, where `n ∈ ℤ/ℓ^ν` stands for the character
`a ↦ a n / ℓ ^ ν` of `ℤ/ℓ^ν`. It vanishes outside `G_ν`.

Let `M` be `ℤ/ℓ^ν` with the action `(cyc⁺) ^ (-e)`. A relation off `T`
(`New.RelationSetting.IsRelation`) is a locally constant homomorphism `y : G_ν → Hom(M, ℚ/ℤ)`,
extended by zero to `G_F`, with `y (g u g⁻¹) = cyc(g) · y u ∘ g⁻¹`, zero on inertia at the primes
outside `T`, and such that `∑ p, y(φ_p)(z(γ_p)) = 0`. This sum runs over any finite family of
distinct primes `p ∉ T` of `F` with Frobenius elements `φ_p ∈ G_ν` and tame generators `γ_p`, and
`z` is any cocycle in `M` that satisfies the local conditions at `S₀`, vanishes at complex
conjugations and is unramified off `S₀` and the `p`. These are properties of the restriction to
`G_ν` of a dual cocycle, with ramification allowed at the possibly larger set `T`. -/
def IsKummerMap [Finite I] {x : I → FrobeniusDatum E} (hx : ∀ i : I, IsNuSplitPlace ν (x i))
    (T : Finset (FinPlace (maximalRealSubfield E))) (ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)) : Prop :=
  ∃ y ∈ (kummerSetting e hx).relations T,
    ∀ (g : Gal(Ω/E)) (a : ZMod (ℓ ^ ν)), y (toGalPlus E g) a = ofZMod (ℓ ^ ν) (a * ψ g)

end Kummer

/-- A function `ψ : G → ℤ/ℓ^ν` has the Kummer type of exponent `e` if it is locally constant and, on
the kernel `G_ν` of the cyclotomic character modulo `ℓ ^ ν`, it is a homomorphism that complex
conjugation negates and that conjugation by `g ∈ G` multiplies by `cyc(g) ^ (e + 1)`. -/
structure HasKummerType (ν e : ℕ) (ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)) : Prop where
  /-- `ψ` is continuous for the discrete topology. -/
  isLocallyConstant : IsLocallyConstant ψ
  /-- `ψ` is a homomorphism on `G_ν`. -/
  map_mul {a b : Gal(Ω/E)} : cyclotomicCharMod Ω (ℓ ^ ν) a = 1 → cyclotomicCharMod Ω (ℓ ^ ν) b = 1 →
    ψ (a * b) = ψ a + ψ b
  /-- `ψᶜ = -ψ` on `G_ν`. -/
  map_conjGal {a : Gal(Ω/E)} : cyclotomicCharMod Ω (ℓ ^ ν) a = 1 → ψ (conjGal a) = -ψ a
  /-- `ψ (g a g⁻¹) = cyc(g) ^ (e + 1) ψ a` for `a ∈ G_ν`. -/
  map_conj (g : Gal(Ω/E)) {a : Gal(Ω/E)} : cyclotomicCharMod Ω (ℓ ^ ν) a = 1 →
    ψ (g * a * g⁻¹) = cyclotomicCharMod Ω (ℓ ^ ν) g ^ (e + 1) * ψ a

namespace HasKummerType

lemma map_one {ν e : ℕ} {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : HasKummerType ν e ψ) : ψ 1 = 0 := by
  simpa using hψ.map_mul (a := 1) (b := 1) (_root_.map_one _) (_root_.map_one _)

/-- A function of Kummer type takes inverses to negatives on the elements that fix the
`ℓ ^ ν`-th roots of unity. -/
lemma map_inv {ν e : ℕ} {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : HasKummerType ν e ψ) {a : Gal(Ω/E)}
    (ha : cyclotomicCharMod Ω (ℓ ^ ν) a = 1) : ψ a⁻¹ = -ψ a := by
  rw [eq_neg_iff_add_eq_zero, ← hψ.map_mul (by simp [ha]) ha, inv_mul_cancel, hψ.map_one]

/-- A function of Kummer type takes powers to multiples on the elements that fix the `ℓ ^ ν`-th
roots of unity. -/
lemma map_pow {ν e : ℕ} {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : HasKummerType ν e ψ) {a : Gal(Ω/E)}
    (ha : cyclotomicCharMod Ω (ℓ ^ ν) a = 1) (n : ℕ) : ψ (a ^ n) = n * ψ a := by
  induction n with
  | zero => simp [hψ.map_one]
  | succ n ih => rw [pow_succ, hψ.map_mul (by simp [ha]) ha, ih, Nat.cast_succ, add_one_mul]

end HasKummerType

/-- Let `ψ` be a Kummer map of exponent `e` off `T`: the value at `g ∈ G` of a relation `y` is the
character `a ↦ a ψ(g) / ℓ ^ ν` of `ℤ/ℓ^ν`. Then `ψ` is locally constant, and on `G_ν` it is a
homomorphism that complex conjugation negates and that conjugation by `g ∈ G` multiplies by
`cyc(g) ^ (e + 1)`. -/
theorem IsKummerMap.hasKummerType {ν e : ℕ} {I : Type} [Finite I] {x : I → FrobeniusDatum E}
    {hx : ∀ i : I, IsNuSplitPlace ν (x i)} {T : Finset (FinPlace (maximalRealSubfield E))}
    {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : IsKummerMap e hx T ψ) : HasKummerType ν e ψ := by
  obtain ⟨y, (hy : (kummerSetting e hx).IsRelation T y), hyψ⟩ := hψ
  have h_val (g : Gal(Ω/E)) : ofZMod (ℓ ^ ν) (ψ g) = y (toGalPlus E g) 1 := by rw [hyψ, one_mul]
  -- Conjugation by `g ∈ G_F` multiplies `ψ` by `cyc(g) cyc⁺(g) ^ e`.
  have h_conj (g : Gal(Ω/maximalRealSubfield E)) {a : Gal(Ω/E)}
      (ha : cyclotomicCharMod Ω (ℓ ^ ν) a = 1) : y (g * toGalPlus E a * g⁻¹) 1 =
        ofZMod (ℓ ^ ν) (cyclotomicCharMod Ω (ℓ ^ ν) g * cyclotomicPlusMod ℓ E ν g ^ e * ψ a) := by
    rw [hy.map_conj g _ (toGalPlus_mem_cyclotomicKerPlus_iff.2 ha), hyψ, tateTwistPlus_ρ]
    exact (map_nsmul (ofZMod (ℓ ^ ν)) _ _).symm.trans (congrArg _ (by simp [mul_assoc]))
  refine ⟨?_, fun {a b} ha hb ↦ ?_, fun {a} ha ↦ ?_, fun g a ha ↦ ?_⟩
  · refine .desc ψ (ofZMod (ℓ ^ ν)) ?_ ofZMod_injective
    rw [comp_def, funext h_val]
    exact (hy.isLocallyConstant.comp_continuous isOpenEmbedding_toGalPlus.continuous).comp (· 1)
  · apply ofZMod_injective
    rw [map_add, h_val, h_val, h_val, map_mul,
      hy.map_mul _ (toGalPlus_mem_cyclotomicKerPlus_iff.2 ha) _
        (toGalPlus_mem_cyclotomicKerPlus_iff.2 hb)]
    exact AddMonoidHom.add_apply _ _ _
  · -- At `c` the factor is `-1`.
    have h_cyc : cyclotomicPlusMod ℓ E ν (conjPlus E) = 1 :=
      cyclotomicPlusMod_eq_one ν (cyclotomicPlus_eq_one_of_isComplexConj isComplexConj_conjPlus)
    have h_conj_c : y (toGalPlus E (conjGal a)) 1 = ofZMod (ℓ ^ ν) (-ψ a) := by
      simpa [toGalPlus_conjGal, inv_eq_of_mul_eq_one_right conjPlus_mul_self, h_cyc,
        isComplexConj_conjPlus.cyclotomicCharMod_eq_neg_one] using h_conj (conjPlus E) ha
    exact ofZMod_injective ((h_val _).trans h_conj_c)
  · -- On `G` the factor is `cyc(g) ^ (e + 1)`.
    apply ofZMod_injective
    rw [h_val, map_mul, map_mul, map_inv, h_conj _ ha, cyclotomicPlusMod_apply, ofGalPlus_toGalPlus,
      show cyclotomicCharMod Ω (ℓ ^ ν) (toGalPlus E g) = cyclotomicCharMod Ω (ℓ ^ ν) g from rfl,
        pow_succ']

/-- Let `z` be a cocycle of `G` for `cyc ^ (-e)` modulo `ℓ ^ ν` that is invariant under complex
conjugation. Its extension `z⁺` to `G_F`, given by `z⁺ (g c) = z g`, is a cocycle for
`(cyc⁺) ^ (-e)`. -/
lemma comp_ofGalPlus_mem_Z1 {ν e : ℕ} {z : Gal(Ω/E) → ZMod (ℓ ^ ν)}
    (hz : z ∈ Z1 (charRep (ZMod (ℓ ^ ν)) (cyclotomicCharMod Ω (ℓ ^ ν) ^ e)⁻¹))
    (h_even : ∀ g : Gal(Ω/E), z (conjGal g) = z g) :
    z ∘ ofGalPlus ∈ Z1 (tateTwistPlus ℓ E ν e).ρ := by
  refine ⟨hz.1.comp continuous_ofGalPlus, fun g h ↦ ?_⟩
  obtain h_mul | h_mul := ofGalPlus_mul_eq_or g h <;>
    simp [h_mul, hz.2, h_even, charRep, cyclotomicPlusMod_apply]

/-- Let `Ω` be the algebraic closure of `ℚ`, `F` the maximal real subfield of the CM field `E`, `x`
a finite family of `ν`-split places, `S₀` the set of primes of `F` above `ℓ` or below `x`, and `P` a
set of primes of `F` disjoint from `S₀`. Let `z : Gal(Ω/E) → ℤ/ℓ^ν` be a cocycle for `cyc ^ (-e)`
that is invariant under complex conjugation `c`, unramified off `ℓ` and the primes above `P`, zero
on the part in `ker cyc` of the decomposition groups above `ℓ`, and zero at the Frobenius elements
of `x`. Extend `z` to `z⁺ = z ∘ ofGalPlus` on `G_F = Gal(Ω/F)` by `z⁺ (g c) = z g`, and `cyc` to
`cyc⁺` by `cyc⁺ c = 1`. Then `2 z⁺` lies in `(kummerSetting e hx).cocycles P`: it is a cocycle of
`G_F` in `ℤ/ℓ^ν` for `(cyc⁺) ^ (-e)`, is unramified off `S₀ ∪ P`, vanishes at complex conjugations,
and for `u ∈ S₀` vanishes on the decomposition group of the chosen place `familyPlace x u` (only on
its part in `ker cyc⁺` if `u` lies above `ℓ`). -/
lemma two_nsmul_comp_ofGalPlus_mem_cocycles {ν e : ℕ} {I : Type} [Finite I]
    {x : I → FrobeniusDatum E} {hx : ∀ i : I, IsNuSplitPlace ν (x i)} {z : Gal(Ω/E) → ZMod (ℓ ^ ν)}
    (hz : z ∈ Z1 (charRep (ZMod (ℓ ^ ν)) (cyclotomicCharMod Ω (ℓ ^ ν) ^ e)⁻¹))
    (h_even : ∀ g : Gal(Ω/E), z (conjGal g) = z g) {P : Set (FinPlace (maximalRealSubfield E))}
    (hP : ∀ u ∈ familyPrimes ℓ x, u ∉ P)
    (h_unr : ∀ g ∈ inertiaAbove (primeBelowPlus ⁻¹'
      (placesDividing (maximalRealSubfield E) ℓ ∪ P)ᶜ), z g = 0)
    (h_loc : ∀ g ∈ shaLocalSet ℓ E 1, z g = 0) (h_frob : ∀ i : I, z (x i).frob = 0) :
    2 • (z ∘ ofGalPlus) ∈ (kummerSetting e hx).cocycles P := by
  -- `X` is `z⁺` as a cocycle.
  let X : Z1 (tateTwistPlus ℓ E ν e).ρ := ⟨z ∘ ofGalPlus, comp_ofGalPlus_mem_Z1 hz h_even⟩
  obtain ⟨-, h_coc⟩ := X.property
  have h_ine (g : Gal(Ω/maximalRealSubfield E))
      (hg : g ∈ inertiaAbove (placesDividing _ ℓ ∪ P)ᶜ) : (2 • X).val g = 0 := by
    simp [X, h_unr _ (ofGalPlus_mem_inertiaAbove hg)]
  -- For `g ∈ ker cyc⁺` we have `2 z⁺ g = z⁺ (g ^ 2)`.
  have h_sq (g : Gal(Ω/maximalRealSubfield E)) (hg : cyclotomicPlus ℓ E g = 1) :
      (2 • X).val g = X.val (g * g) := by
    rw [h_coc g g, tateTwistPlus_ρ_eq_one e (cyclotomicPlusMod_eq_one ν hg)]
    exact two_nsmul _
  have h_complex (c : Gal(Ω/maximalRealSubfield E)) (hc : IsComplexConj c) : (2 • X).val c = 0 := by
    rw [h_sq c (cyclotomicPlus_eq_one_of_isComplexConj hc), hc.mul_self]
    simpa using h_coc 1 1
  -- Above `ℓ`: `g ^ 2` lies in `G`, in the decomposition group and in the kernel of `cyc`.
  have h_above {u : FinPlace (maximalRealSubfield E)}
      (hℓ : (ℓ : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal) {g : Gal(Ω/maximalRealSubfield E)}
      (hg : g ∈ decompGroup Gal(Ω/maximalRealSubfield E) (familyPlace x u))
      (hg_cyc : cyclotomicPlus ℓ E g = 1) : (2 • X).val g = 0 := by
    obtain ⟨s, hs⟩ := mul_self_mem_of_index_two index_range_toGalPlus g
    have hs_dec : toGalPlus E s ∈ decompGroup Gal(Ω/maximalRealSubfield E) (familyPlace x u) := by
      simpa only [hs] using mul_mem hg hg
    have hs_cyc : cyclotomicChar Ω ℓ s = 1 := by
      rw [← ofGalPlus_toGalPlus s, ← cyclotomicPlus_apply, hs, map_mul, hg_cyc, one_mul]
    have hs_zero : z s = 0 :=
      h_loc s ⟨_, (isPlaceOver_familyPlace u).valuation_natCast_lt_one_iff.2 hℓ, hs_dec, hs_cyc⟩
    rw [h_sq g hg_cyc, ← hs]
    simpa [X] using hs_zero
  -- Below `x`: inertia and a Frobenius element topologically generate the decomposition group.
  have h_below {u : FinPlace (maximalRealSubfield E)} (hu : u ∈ familyPrimes ℓ x)
      (hℓ : (ℓ : 𝓞 (maximalRealSubfield E)) ∉ u.asIdeal) {g : Gal(Ω/maximalRealSubfield E)}
      (hg : g ∈ decompGroup Gal(Ω/maximalRealSubfield E) (familyPlace x u)) :
      (2 • X).val g = 0 := by
    have h_place : IsPlaceOver (familyPlace x u) u := isPlaceOver_familyPlace u
    obtain ⟨i, hi⟩ := exists_isFrob_familyPlace ((mem_familyPrimes.1 hu).resolve_left hℓ)
    refine Z1.eq_zero_on_decompGroup (2 • X) h_place hi
      (fun a ha ↦ h_ine a ⟨u, not_or.2 ⟨hℓ, hP u hu⟩, _, h_place, ha⟩) ?_ g hg
    -- `map_inv` would move the inverse outside `toGalPlus`, hiding `ofGalPlus_toGalPlus`.
    simp [X, -map_inv, show z (x i).frob⁻¹ = 0 from (cocycleKer _ hz.2).inv_mem (h_frob i)]
  refine ⟨⟨(2 • X).property, ?_⟩, ?_, h_complex⟩
  · -- Off `S₀ ∪ P` the prime lies in particular off `ℓ` and `P`.
    rintro g ⟨u, hu, hg⟩
    exact h_ine g ⟨u, fun h ↦ hu (h.imp_left fun hℓ ↦ mem_familyPrimes.2 (.inl hℓ)), hg⟩
  rintro u hu ⟨g, hg⟩ hg_cyc
  by_cases hℓ : (ℓ : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
  exacts [h_above hℓ hg (hg_cyc hℓ), h_below hu hℓ hg]

omit [ThePrime ℓ] in
/-- Let `F` be the maximal real subfield of `E`. If a prime `t` of `E` lies above `ℓ`, or is the
place of one of the `w j` or a complex conjugate of one, then the prime of `F` below `t`
(`primeBelowPlus t`) lies above `ℓ` or is below the place of one of the `w j`. -/
lemma primeBelowPlus_mem_of_mem_conjClosure {J : Type} {w : J → FrobeniusDatum E} {t : FinPlace E}
    (ht : t ∈ placesDividing E ℓ ∪ Set.conjClosure (Set.range fun j : J ↦ (w j).place)) :
    primeBelowPlus t ∈ placesDividing (maximalRealSubfield E) ℓ ∪
      Set.range fun j : J ↦ primeBelowPlus (w j).place := by
  obtain hℓ | ⟨j, hj⟩ | ⟨j, hj⟩ : (ℓ : 𝓞 E) ∈ t.asIdeal ∨ (∃ j : J, (w j).place = t) ∨
      ∃ j : J, (w j).place = star t := by
    simpa [placesDividing] using ht
  · exact .inl (by simpa [placesDividing] using hℓ)
  · exact .inr ⟨j, by simp [hj]⟩
  · exact .inr ⟨j, by simp [hj, primeBelowPlus_star]⟩

/-- Let `x` and `w` be finite families of `ν`-split places and `T` a finite set of primes of `F`
containing those above `ℓ` or below `x`, such that the `w j` lie above distinct primes of `F`
outside `T`. Let `γ j` be tame generators at the `w j` normalised over `F`. Let `ψ` be a Kummer map
off `T`: it comes from an equivariant homomorphism from `G_ν` to the Cartier dual of a twist of
`ℤ/ℓ^ν` over `F`, unramified outside `T`, that satisfies reciprocity against the `ℤ/ℓ^ν`-valued
cocycles of `Gal(Ω/F)` in `(kummerSetting e hx).cocycles`. Let `z` be an even class of exponent `e`
for `w` that vanishes at the Frobenius elements of `x`. Then `∑ j, ψ(φ_j) · 2 z(γ_j) = 0`, where
`φ_j` is the Frobenius element of `w j`. -/
theorem IsKummerMap.sum_eq_zero {ν e : ℕ} {I : Type} [Finite I] {x : I → FrobeniusDatum E}
    {hx : ∀ i : I, IsNuSplitPlace ν (x i)} {T : Finset (FinPlace (maximalRealSubfield E))}
    {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : IsKummerMap e hx T ψ) (hT : familyPrimes ℓ x ⊆ T)
    {J : Type} [Fintype J] {w : J → FrobeniusDatum E} (hw : ∀ j : J, IsNuSplitPlace ν (w j))
    (w_inj : Injective fun j : J ↦ primeBelowPlus (w j).place)
    (w_notMem : ∀ j : J, primeBelowPlus (w j).place ∉ T) {γ : J → Gal(Ω/E)}
    (hγ : ∀ j : J, IsTameGeneratorFor (K := maximalRealSubfield E) (ℓ ^ ν) (w j).valuationSubring
      (toGalPlus E (γ j)))
    {O : CoeffRing ℓ} {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)}
    (hz : z ∈ evenClasses O (Set.range fun j : J ↦ (w j).place) ν e)
    (h_frob : ∀ i : I, z (x i).frob = 0) :
    ∑ j : J, (ψ (w j).frob).val • 2 • z (γ j) = 0 := by
  -- The additive maps `f` to `ℤ/ℓ^ν` separate points, so we may replace `z` by `f ∘ z`.
  refine eq_zero_of_forall_mem_Z1_of_mem_evenClasses hz fun f hf ↦ ?_
  obtain ⟨⟨-, h_unr, -⟩, h_even, h_loc⟩ := hz.imp_left mem_selmerModule_iff.1
  have h_mem : 2 • ((fun g ↦ f (z g)) ∘ ofGalPlus) ∈
      (kummerSetting e hx).cocycles (Set.range fun j ↦ primeBelowPlus (w j).place) := by
    refine two_nsmul_comp_ofGalPlus_mem_cocycles hf (by simp [h_even]) ?_
      (fun g ⟨t, ht, h_inertia⟩ ↦ ?_) (fun g hg ↦ by simp [h_loc g hg]) (by simp [h_frob])
    · rintro u hu ⟨j, rfl⟩
      exact w_notMem j (hT hu)
    · simp [h_unr g ⟨t, fun h ↦ ht (primeBelowPlus_mem_of_mem_conjClosure h), h_inertia⟩]
  -- The primes below the `w j` are split, with the arithmetic Frobenius elements `φ_j⁻¹`.
  let p (j : J) : SplitPrime (ℓ ^ ν) (kummerSetting e hx).subgroup :=
    { prime := primeBelowPlus (w j).place
      place := (w j).valuationSubring
      isPlaceOver := (w j).isPlaceOver.isPlaceOver_below
      frob := toGalPlus E (w j).frob⁻¹
      isFrob := by simpa [q_primeBelowPlus, isFrob_toGalPlus_iff, -map_inv] using (w j).isFrob_inv
      frob_mem := toGalPlus_mem_cyclotomicKerPlus_iff.2 (by simpa using (hw j).2)
      tameGenerator := toGalPlus E (γ j)
      isTameGeneratorFor := hγ j }
  have h_inv (j : J) : ψ (w j).frob⁻¹ = -ψ (w j).frob := hψ.hasKummerType.map_inv (hw j).2
  obtain ⟨y, (hy : (kummerSetting e hx).IsRelation T y), hyψ⟩ := hψ
  have h_term (j : J) : y (p j).frob ((2 • (fun g ↦ f (z g)) ∘ ofGalPlus) (p j).tameGenerator) =
      ofZMod (ℓ ^ ν) (2 • f (z (γ j)) * ψ (w j).frob⁻¹) := by
    change y (toGalPlus E (w j).frob⁻¹) (2 • f (z (ofGalPlus (toGalPlus E (γ j))))) = _
    rw [ofGalPlus_toGalPlus, hyψ]
  have h_sum : ∑ j, 2 • f (z (γ j)) * ψ (w j).frob⁻¹ = 0 := by
    apply ofZMod_injective
    rw [map_sum, map_zero]
    exact (sum_congr rfl fun j _ ↦ (h_term j).symm).trans
      (hy.sum_eq_zero p w_inj w_notMem _ h_mem)
  suffices h_image : ∑ j, (ψ (w j).frob).val • 2 • f (z (γ j)) = 0 by
    simpa only [map_sum, map_nsmul] using h_image
  simpa [h_inv, mul_comm] using h_sum

/-- At a prime of degree one of `E` there is a tame generator in `G` normalised over `F`: an element
of inertia that moves an `m`-th root of a uniformiser of `F` by the fixed root of unity. -/
lemma exists_isTameGeneratorFor_toGalPlus (m : ℕ) [NeZero m] (w : FrobeniusDatum E) :
    ∃ γ : Gal(Ω/E),
      IsTameGeneratorFor (K := maximalRealSubfield E) m w.valuationSubring (toGalPlus E γ) := by
  have h_place := w.isPlaceOver.isPlaceOver_below (K := maximalRealSubfield E)
  obtain ⟨δ, hδ⟩ := exists_isTameGeneratorFor Gal(Ω/maximalRealSubfield E) m h_place
  obtain ⟨γ, rfl⟩ := inertiaGroup_le_range_toGalPlus _ h_place hδ.1
  exact ⟨γ, hδ⟩

/-- Let `w` consist of a prime of `E` of prime norm not above `ℓ`, a place of `Ω` above it and a
Frobenius element, and let `γ ∈ G` be a tame generator at that place, normalised over `F`. Let `O`
be the ring of integers of a finite Galois extension of `ℚ_ℓ` and `z` an even class for `S`: a
locally constant cocycle of `G` in `(O/ℓ^ν)(-e)`, invariant under complex conjugation, unramified
off `ℓ`, `S` and `S̄`, and zero on the elements of `ker cyc` in decomposition groups above `ℓ`; its
values are vectors of length one (indexed by `Unit`) over `QuotSpan (ℓ ^ ν) = O/ℓ^ν`. Then the value
of `z` at an element `τ` of the inertia group at that place is a multiple of `z γ`. -/
lemma exists_apply_eq_nsmul_of_mem_evenClasses {ν e : ℕ} {w : FrobeniusDatum E}
    (hℓ : (ℓ : 𝓞 E) ∉ w.place.asIdeal) {γ τ : Gal(Ω/E)}
    (hγ : IsTameGeneratorFor (K := maximalRealSubfield E) (ℓ ^ ν) w.valuationSubring
      (toGalPlus E γ))
    (hτ : τ ∈ inertiaGroup Gal(Ω/E) w.valuationSubring) {O : CoeffRing ℓ} {S : Set (FinPlace E)}
    {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)} (hz : z ∈ evenClasses O S ν e) :
    ∃ n : ℕ, z τ = n • z γ := by
  have h_place : IsPlaceOver w.valuationSubring (primeBelowPlus w.place) :=
    w.isPlaceOver.isPlaceOver_below
  have h_notMem : ↑(ℓ ^ ν) ∉ (primeBelowPlus w.place).asIdeal :=
    fun h ↦ hℓ (w.place.isPrime.mem_of_pow_mem ν (by simpa using h))
  let : Module (ZMod (ℓ ^ ν)) (Unit → QuotSpan (ℓ ^ ν : ↑O)) :=
    AddCommGroup.zmodModule fun _ ↦ funext fun _ ↦ nsmul_quot_eq_zero rfl.dvd _
  obtain ⟨h_coc, -, -, h_locallyConstant⟩ := mem_selmerModule_iff.1 hz.1
  have h_add : ∀ g ∈ inertiaGroup Gal(Ω/maximalRealSubfield E) w.valuationSubring,
      ∀ k ∈ inertiaGroup Gal(Ω/maximalRealSubfield E) w.valuationSubring,
      z (ofGalPlus (g * k)) = z (ofGalPlus g) + z (ofGalPlus k) := by
    intro g hg k hk
    obtain ⟨a, rfl⟩ := inertiaGroup_le_range_toGalPlus _ h_place hg
    obtain ⟨b, rfl⟩ := inertiaGroup_le_range_toGalPlus _ h_place hk
    simp [← map_mul, h_coc, tateTwist, cyclotomicInv,
      cyclotomicChar_eq_one_of_mem_inertiaAbove ⟨w.place, hℓ, _, w.isPlaceOver, hg⟩]
  simpa using hγ.exists_apply_eq_nsmul h_place h_notMem (τ := toGalPlus E τ) hτ
    (fun g ↦ z (ofGalPlus g)) (h_locallyConstant.comp_continuous continuous_ofGalPlus) h_add

/-- The reciprocity law `New.Selmer.IsKummerMap.sum_eq_zero` with one term left. Let `x` and `w` be
finite families of `ν`-split places. Let `T` contain the primes of `F` above `ℓ` or below `x`, and
let the `w i` lie above distinct primes of `F` outside `T`. Let `ψ` be a Kummer map off `T` that
vanishes at the Frobenius elements of `w` except at `w j`. Let `O` be the ring of integers of a
finite Galois extension of `ℚ_ℓ` and `z` an even class: a cocycle in `(O/ℓ^ν)(-e)` that is invariant
under complex conjugation, unramified off `ℓ`, the `w i` and their conjugates, and zero on the
elements of `ker cyc` in decomposition groups above `ℓ`. Suppose that `z` vanishes at the Frobenius
elements of `x`. Then every `n` divisible by `2 ψ(φ_j)` in `ℤ/ℓ^ν`, with `φ_j` the Frobenius element
at `w j`, kills the value of `z` at the chosen generator `(w j).isPlaceOver.tameGenerator` of tame
inertia at `w j`. -/
theorem IsKummerMap.nsmul_apply_tameGenerator_eq_zero {ν e : ℕ} {I : Type} [Finite I]
    {x : I → FrobeniusDatum E} {hx : ∀ i : I, IsNuSplitPlace ν (x i)}
    {T : Finset (FinPlace (maximalRealSubfield E))}
    {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : IsKummerMap e hx T ψ) (hT : familyPrimes ℓ x ⊆ T)
    {J : Type} [Fintype J] {w : J → FrobeniusDatum E} (hw : ∀ i : J, IsNuSplitPlace ν (w i))
    (w_inj : Injective fun i : J ↦ primeBelowPlus (w i).place)
    (w_notMem : ∀ i : J, primeBelowPlus (w i).place ∉ T)
    {j : J} (h_zero : ∀ i : J, i ≠ j → ψ (w i).frob = 0)
    {O : CoeffRing ℓ} {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)}
    (hz : z ∈ evenClasses O (Set.range fun i : J ↦ (w i).place) ν e)
    (h_frob : ∀ i : I, z (x i).frob = 0)
    {n : ℕ} (hn : 2 * ψ (w j).frob ∣ n) : n • z (w j).isPlaceOver.tameGenerator = 0 := by
  choose γ hγ using fun i : J ↦ exists_isTameGeneratorFor_toGalPlus (ℓ ^ ν) (w i)
  have h_term : (ψ (w j).frob).val • 2 • z (γ j) = 0 := by
    rw [← hψ.sum_eq_zero hT hw w_inj w_notMem hγ hz h_frob, Fintype.sum_eq_single j]
    exact fun i hi ↦ by simp [h_zero i hi]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, z (w j).isPlaceOver.tameGenerator = m • z (γ j) :=
    exists_apply_eq_nsmul_of_mem_evenClasses (hw j).1 (hγ j) (w j).isPlaceOver.tameGenerator.2 hz
  -- The values of `z` form a module over `ℤ/ℓ^ν`, in which `n = 2 ψ(φ_j) a`.
  let : Module (ZMod (ℓ ^ ν)) (Unit → QuotSpan (ℓ ^ ν : ↑O)) :=
    AddCommGroup.zmodModule fun _ ↦ funext fun _ ↦ nsmul_quot_eq_zero rfl.dvd _
  obtain ⟨a, ha⟩ : ∃ a : ZMod (ℓ ^ ν), (n : ZMod (ℓ ^ ν)) = 2 * ψ (w j).frob * a := hn
  have h_kill : (2 * ψ (w j).frob) • z (γ j) = 0 := by
    rwa [← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ ν)), ZMod.natCast_zmod_val,
      ← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ ν)), smul_smul, Nat.cast_ofNat, mul_comm] at h_term
  rw [hm, smul_comm, ← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ ν)) n, ha, mul_comm, mul_smul, h_kill,
    smul_zero, smul_zero]

/-- The reduction `G_ν → 𝔽_ℓ` of a map to `ℤ/ℓ^ν`. -/
def reductionModL {ν : ℕ} (ψ : Gal(Ω/E) → ZMod (ℓ ^ ν))
    (g : (cyclotomicCharMod (Γ := Gal(Ω/E)) Ω (ℓ ^ ν)).ker) : ZMod ℓ :=
  (ψ g).cast

/-- The space spanned by the reductions `G_ν → 𝔽_ℓ` of the Kummer maps of exponent `e` for the
family `x`, off `T`. -/
def kummerReductions {ν : ℕ} (e : ℕ) {I : Type} [Finite I] {x : I → FrobeniusDatum E}
    (hx : ∀ i : I, IsNuSplitPlace ν (x i)) (T : Finset (FinPlace (maximalRealSubfield E))) :
    Submodule (ZMod ℓ) ((cyclotomicCharMod (Γ := Gal(Ω/E)) Ω (ℓ ^ ν)).ker → ZMod ℓ) :=
  Submodule.span (ZMod ℓ) (reductionModL '' {ψ | IsKummerMap e hx T ψ})

/-- Elements of `ℤ/ℓ^ν` with the same image in `ℤ/ℓ` differ by a multiple of `ℓ`. -/
lemma natCast_dvd_sub_of_cast_eq {ν : ℕ} {a b : ZMod (ℓ ^ ν)}
    (h : (a.cast : ZMod ℓ) = b.cast) : (ℓ : ZMod (ℓ ^ ν)) ∣ a - b := by
  rw [← ZMod.natCast_val, ← ZMod.natCast_val, ZMod.natCast_eq_natCast_iff] at h
  simpa using map_dvd (Int.castRingHom (ZMod (ℓ ^ ν))) h.symm.dvd

/-- Let `x` be a finite family of `ν`-split places, and let `y` be a relation off the finite set `T`
of primes of the maximal real subfield `F`: an equivariant homomorphism from `G_ν` to the characters
`ℤ/ℓ^ν → ℚ/ℤ`, extended by zero to `G_F = Gal(Ω/F)`, unramified outside `T` and subject to a
reciprocity law. There is a function `ψ : G → ℤ/ℓ^ν` such that the value of `y` at each `g ∈ G` is
the character `a ↦ a ψ(g) / ℓ ^ ν`. -/
lemma exists_apply_toGalPlus_eq_ofZMod {ν : ℕ} (e : ℕ) {I : Type} [Finite I]
    {x : I → FrobeniusDatum E} (hx : ∀ i : I, IsNuSplitPlace ν (x i))
    (T : Finset (FinPlace (maximalRealSubfield E))) (y : (kummerSetting e hx).relations T) :
    ∃ ψ : Gal(Ω/E) → ZMod (ℓ ^ ν), ∀ (g : Gal(Ω/E)) (a : ZMod (ℓ ^ ν)),
      y.val (toGalPlus E g) a = ofZMod (ℓ ^ ν) (a * ψ g) := by
  have h_tors (g : Gal(Ω/E)) : ℓ ^ ν • y.val (toGalPlus E g) 1 = 0 := by
    simp [← map_nsmul, CharP.cast_eq_zero]
  choose ψ hψ using fun g ↦ exists_ofZMod (h_tors g)
  refine ⟨ψ, fun g a ↦ ?_⟩
  -- Both sides are additive in `a` and agree at `1`.
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [← nsmul_eq_mul, map_nsmul, hψ, ← nsmul_one, map_nsmul]
  rfl

/-- Let `ℓ` be a prime, `E` a CM field that contains a primitive `5040`-th root of unity, `G_ν` the
subgroup of `Gal(Ω/E)` that fixes the `ℓ ^ ν`-th roots of unity, `x` a finite family of `ν`-split
places and `T` a finite set of primes of the maximal real subfield `F`. The Kummer maps
`ψ : Gal(Ω/E) → ℤ/ℓ^ν` of exponent `e` off `T` come from the equivariant homomorphisms from `G_ν` to
the Cartier dual of a twist of `ℤ/ℓ^ν` over `F` that are unramified outside `T` and satisfy a
reciprocity law. Then `kummerReductions e hx T`, the span over `𝔽_ℓ` of the functions
`ψ mod ℓ : G_ν → 𝔽_ℓ`, is finite. -/
lemma finite_kummerReductions {ν : ℕ} (e : ℕ) {I : Type} [Finite I]
    {x : I → FrobeniusDatum E} (hx : ∀ i : I, IsNuSplitPlace ν (x i))
    (T : Finset (FinPlace (maximalRealSubfield E))) : Finite (kummerReductions e hx T) := by
  -- A relation determines its Kummer map, and there are finitely many relations.
  choose ψ hψ using exists_apply_toGalPlus_eq_ofZMod e hx T
  have h_fin : {ψ' | IsKummerMap e hx T ψ'}.Finite := by
    refine (Set.finite_range ψ).subset ?_
    rintro ψ' ⟨y, hy, hyψ⟩
    refine ⟨⟨y, hy⟩, funext fun g ↦ ofZMod_injective ?_⟩
    rw [← one_mul (ψ _ g), ← one_mul (ψ' g)]
    exact (hψ ⟨y, hy⟩ g 1).symm.trans (hyψ g 1)
  have : Module.Finite (ZMod ℓ) (kummerReductions e hx T) := .span_of_finite _ (h_fin.image _)
  exact Module.finite_of_finite (ZMod ℓ)

/-- Let `G_ν` be the subgroup of `G = Gal(Ω/E)` that fixes the `ℓ ^ ν`-th roots of unity, `x` a
finite family of `ν`-split places and `T` a finite set of primes of the maximal real subfield `F`.
Let `M*` be the group of characters `ℤ/ℓ^ν → ℚ/ℤ`. A relation off `T` is an equivariant homomorphism
`y : G_ν → M*`, extended by zero to `Gal(Ω/F)`, unramified outside `T` and subject to a reciprocity
law; its Kummer map `ψ : G → ℤ/ℓ^ν` is given by `y g a = a ψ(g) / ℓ ^ ν`. There are no more
reductions `Gal(Ω/F) → M* / ℓ M*` of relations than elements in the `𝔽_ℓ`-span of the reductions
`G_ν → 𝔽_ℓ` of Kummer maps, because the reduction of `y` is determined by that of `ψ`. -/
lemma card_reductions_le {ν : ℕ} (e : ℕ) {I : Type} [Finite I]
    {x : I → FrobeniusDatum E} (hx : ∀ i : I, IsNuSplitPlace ν (x i))
    (T : Finset (FinPlace (maximalRealSubfield E))) :
    Nat.card ((kummerSetting e hx).reductions ℓ T) ≤ Nat.card (kummerReductions e hx T) := by
  have : Finite (kummerReductions e hx T) := finite_kummerReductions e hx T
  choose ψ hψ using exists_apply_toGalPlus_eq_ofZMod e hx T
  -- Choose a relation for each reduction; taking the reduction of its Kummer map is injective.
  have h_lift (f : (kummerSetting e hx).reductions ℓ T) :
      ∃ y : (kummerSetting e hx).relations T, ∀ σ, Submodule.Quotient.mk (y.val σ) = f.val σ := by
    obtain ⟨y, hy, h_red⟩ := Submodule.mem_map.1 f.property
    exact ⟨⟨y, hy⟩, congr_fun h_red⟩
  choose y h_red using h_lift
  have h_kummer (f : (kummerSetting e hx).reductions ℓ T) : IsKummerMap e hx T (ψ (y f)) :=
    ⟨(y f).val, (y f).property, hψ (y f)⟩
  let reduction (f : (kummerSetting e hx).reductions ℓ T) : kummerReductions e hx T :=
    ⟨reductionModL (ψ (y f)), Submodule.subset_span (Set.mem_image_of_mem _ (h_kummer f))⟩
  refine Nat.card_le_card_of_injective reduction fun f f' h ↦ Subtype.ext (funext fun σ ↦ ?_)
  rw [← h_red f σ, ← h_red f' σ, Submodule.Quotient.eq]
  by_cases hσ : σ ∈ (kummerSetting e hx).subgroup
  · -- On `G_ν` the two Kummer maps differ by `ℓ t`.
    obtain ⟨g, rfl⟩ := hσ.1
    have h_cast : ((ψ (y f) g).cast : ZMod ℓ) = (ψ (y f') g).cast :=
      congr_fun (congr_arg Subtype.val h) ⟨g, toGalPlus_mem_cyclotomicKerPlus_iff.1 hσ⟩
    obtain ⟨t, ht⟩ := natCast_dvd_sub_of_cast_eq h_cast
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨(ofZMod (ℓ ^ ν)).comp (.mulRight t), Submodule.mem_top, CharacterModule.ext _ fun a ↦ ?_⟩
    change ofZMod (ℓ ^ ν) (ℓ * a * t) = (y f).val (toGalPlus E g) a - (y f').val (toGalPlus E g) a
    rw [hψ (y f), hψ (y f'), mul_comm _ a, mul_assoc, ← ht, mul_sub, map_sub]
    rfl
  · simp [(y f).property.eq_zero_of_notMem σ hσ, (y f').property.eq_zero_of_notMem σ hσ]

/-- Let `ℓ` be a prime, `ν > 0`, `E` a CM field in the algebraic closure `Ω` of `ℚ` that contains a
primitive `5040`-th root of unity, `F` its maximal real subfield and `G_ν` the subgroup of
`G = Gal(Ω/E)` that fixes the `ℓ ^ ν`-th roots of unity. Let the `x i` be finitely many `ν`-split
places above distinct primes of `F`, and let `E` have at least four infinite places. A Kummer map
`ψ : G → ℤ/ℓ^ν` of exponent `e` off `T` comes from an equivariant homomorphism from `G_ν` to the
Cartier dual of a twist of `ℤ/ℓ^ν` over `F`, unramified outside `T` and subject to a reciprocity
law; conjugation by `g ∈ G` multiplies it by `cyc(g) ^ (e + 1)`. Then there is a finite set `T` of
primes of `F`, containing those above `ℓ` or below the `x i`, such that the functions
`ψ mod ℓ : G_ν → 𝔽_ℓ` span a space of dimension greater than the number of the `x i`. -/
theorem exists_card_lt_finrank_kummerReductions {ν : ℕ} (hν : 0 < ν) (e : ℕ)
    (h_places : 4 ≤ card (InfinitePlace E)) {I : Type} [Fintype I] {x : I → FrobeniusDatum E}
    (hx : ∀ i : I, IsNuSplitPlace ν (x i))
    (x_inj : Injective fun i : I ↦ primeBelowPlus (x i).place) :
    ∃ T : Finset (FinPlace (maximalRealSubfield E)), familyPrimes ℓ x ⊆ T ∧
      card I < Module.finrank (ZMod ℓ) (kummerReductions e hx T) := by
  classical
  let D := kummerSetting e hx
  have hℓ_dvd : ℓ ∣ ℓ ^ ν := dvd_pow_self ℓ hν.ne'
  -- The kernel of `cyc⁺` lies in `G_ν ∪ G_ν c`.
  have h_ker (g : Gal(Ω/maximalRealSubfield E)) (hg : cyclotomicPlus ℓ E g = 1) :
      g ∈ D.subgroup ∨ g * conjPlus E ∈ D.subgroup := by
    have h_mem : toGalPlus E (ofGalPlus g) ∈ D.subgroup :=
      toGalPlus_mem_cyclotomicKerPlus_iff.2
        ((cyclotomicPlusMod_apply ν g).symm.trans (cyclotomicPlusMod_eq_one ν hg))
    rw [toGalPlus_ofGalPlus] at h_mem
    split at h_mem <;> simp [h_mem]
  have h_torsion : Nat.card {a : tateTwistPlus ℓ E ν e // ℓ • a = 0} = ℓ :=
    (IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod (ℓ ^ ν)) ℓ).trans
      (by simp [Nat.gcd_eq_right hℓ_dvd])
  -- The last argument is the definition of the local conditions above `ℓ` in `kummerSetting`.
  obtain ⟨T, hT, h_count⟩ :=
    D.exists_pow_le_card_reductions hℓ_dvd (by rwa [card_infinitePlace_eq_card_infinitePlace E])
      continuous_cyclotomicPlus (fun g ↦ four_dvd_cyclotomicChar_sub_one _) h_ker h_torsion fun _ ↦
        rfl
  refine ⟨T, hT, ?_⟩
  have h_primes : card I ≤ #{u ∈ D.localPrimes | ↑ℓ ∉ u.asIdeal} :=
    card_le_card_of_injOn (fun i ↦ primeBelowPlus (x i).place)
      (by simp [D, kummerSetting, mem_familyPrimes, (hx _).1]) x_inj.injOn
  have h_pow : ℓ ^ (card I + 1) ≤ ℓ ^ Module.finrank (ZMod ℓ) (kummerReductions e hx T) := calc
    _ ≤ ℓ ^ (#{u ∈ D.localPrimes | ↑ℓ ∉ u.1} + 1) := Nat.pow_le_pow_right NeZero.one_le (by gcongr)
    _ ≤ Nat.card (D.reductions ℓ T) := h_count
    _ ≤ Nat.card (kummerReductions e hx T) := card_reductions_le e hx T
    _ = _ := have := finite_kummerReductions e hx T
      by simp [Module.natCard_eq_pow_finrank (K := ZMod ℓ)]
  exact (Nat.pow_le_pow_iff_right (Fact.out : ℓ.Prime).one_lt).1 h_pow

end New.Selmer

end
end
end

/-!
# Taylor–Wiles places in a triangle for the even classes, with prescribed Frobenii

Auxiliary (Taylor–Wiles) places that cut down the even classes of the Tate twists, with Frobenius
data in a prescribed set.

The places are indexed by an exponent e > 0 and a test point, and are chosen one after another. Step
1 finds a new Kummer map (`New.Selmer.IsKummerMap`) and an element that the earlier maps kill and at
which the value of the new map is a given product. Step 2 gets from Chebotarev's theorem a place
whose Frobenius element has twice these values under the maps, and at which even classes take twice
their value at the test point. Step 3 applies the reciprocity law of each Kummer map at its own
place and the later ones.

Throughout, ℓ is a prime, Ω is the algebraic closure of ℚ, and E is a CM field embedded in Ω that
contains a primitive 5040-th root of unity (`New.CMFieldWithRoot5040`); F is its maximal real
subfield, and `New.Selmer.primeBelowPlus` w is the prime of F below a prime w of E.
`New.cyclotomicChar` (written cyc) is the ℓ-adic cyclotomic character; G_ν is the kernel of its
reduction `New.cyclotomicCharMod` modulo ℓ^ν, and `New.conjGal` is the conjugation of Galois
elements by complex conjugation. The letter γ denotes a Galois element that separates the exponents;
in `New.Selmer.exists_isPrimeTriangle` it generates the Galois group modulo the kernel of cyc, and
the triangle is stated for γ⁻¹.

* `New.Selmer.exists_isPrimeTriangle`: for each ν > 0 there are Taylor–Wiles places of level ℓ^ν,
  indexed by one finite ordered set, that satisfy `New.Selmer.IsPrimeTriangle` and have their
  Frobenius data in a prescribed set.

Notions from other files:
* `New.CoeffRing`: The coefficient rings: rings of integers of the finite Galois extensions of ℚ_ℓ
  inside its algebraic closure.
* `New.Selmer.evenClasses`: The even classes: cocycles c in (O/ℓ^ν)(−e), O a coefficient ring,
  unramified off ℓ and a given set of places with their conjugates, with c(`conjGal` g) = c(g), that
  vanish on the elements of trivial cyc in the decomposition groups above ℓ.
* `New.Selmer.IsNuSplitPlace`: A condition on Frobenius data (w, A, σ), which consist of w of prime
  norm, A a place of Ω above w and σ a geometric Frobenius at A: w is not above ℓ, σ fixes μ_{ℓ^ν}.
* `New.Selmer.HasKummerType`: A continuous map to ℤ/ℓ^ν, an odd homomorphism on G_ν, that
  conjugation by a multiplies by cyc(a)^(e + 1); Kummer maps of exponent e have it.
* `New.Selmer.IsKummerMap`: A Kummer map of exponent e for a finite family x of split places, off a
  finite set T of primes of F: the restriction to Gal(Ω/E) of a relation over F. It has the Kummer
  type of exponent e and is unramified off T. For a finite family w of split places above distinct
  primes of F outside T it satisfies a reciprocity law: a linear relation among the values of a
  cocycle over F at the tame generators of w, with the values of the map at the Frobenius elements
  of w as coefficients. The cocycle must satisfy local conditions at the primes above ℓ and below
  the places of x.
* `New.Selmer.IsPrimeTriangle`: Ordered places whose tame generators and Frobenius elements cut down
  the even classes one after another, up to given powers of ℓ.
* `New.mostFrobenii`: The filter of most Frobenii. A set X of data (w, A, σ) belongs to it if each
  nonempty open set of Galois elements has a nonempty open part U such that, for almost all w, X
  contains every datum with σ ∈ U.
* `New.mostFrobeniiAt`: The filter of most Frobenii near g: the same filter, refined by the
  condition that σ lies near g.

## Relation to the literature

Taylor–Wiles primes, equally many at every ℓ-power level, are chosen in triangular form by means of
a count over the real subfield, which gives reciprocity laws for even classes in Tate twists. Each
new Frobenius kills the earlier Kummer maps but not the new one, and their reciprocity laws remove
the even classes. No bound for the even classes is needed; for small ℓ congruences between the
twists cost a power of ℓ for each prime. Tame ramification governed by Frobenius in the Kummer field
of units and the inductive choice of primes at every level are known. Related work: Gras–Munnier,
Extensions cycliques T-totalement ramifiées, 1998; Hajir–Maire–Ramakrishna, Tame Z/pZ-extensions
with prescribed ramification, 2022; Taylor–Wiles, Ring-theoretic properties of certain Hecke
algebras, 1995; Darmon–Diamond–Taylor, Fermat's Last Theorem (2.19), 1995; Dotto–Thorne, Residually
reducible representations of rank 2, 2026.
-/

@[expose] public section

open New Patching Function Finset Fintype Filter PadicInt WellFoundedLT OddPart

/-- Let `u` be a unit of `ℤ_ℓ` such that every `u ^ a - 1` with `0 < a < t` divides `ℓ ^ h`, and
let `t + 2 ≤ y`. If `n` divides `ℓ ^ (3 * h)`, then `n` times the product of the `u ^ a - u ^ k`
over the `k < t` other than a given `a < t` divides `ℓ ^ (y * h)`. -/
lemma New.Selmer.mul_prod_pow_sub_pow_dvd {ℓ : ℕ} [ThePrime ℓ] {t y h : ℕ} {u : ℤ_[ℓ]ˣ}
    (hy : t + 2 ≤ y) (hu : ∀ a ∈ Set.Ioo 0 t, (u ^ a).val - 1 ∣ ℓ ^ h) (a : Fin t) {n : ℤ_[ℓ]}
    (hn : n ∣ ℓ ^ (3 * h)) :
    n * ∏ k ∈ {a}ᶜ, ((u ^ a.val).val - (u ^ k.val).val) ∣ ℓ ^ (y * h) := by
  have h_lt (b k : Fin t) (hkb : k < b) : (u ^ b.val).val - (u ^ k.val).val ∣ ℓ ^ h := by
    have h_eq : (u ^ b.val).val - (u ^ k.val).val =
        ((u ^ (b.val - k.val)).val - 1) * (u ^ k.val).val := by
      rw [sub_one_mul, ← Units.val_mul, ← pow_add, Nat.sub_add_cancel hkb.le]
    rw [h_eq, Units.mul_right_dvd]
    exact hu _ ⟨Nat.sub_pos_of_lt hkb, by omega⟩
  have h_ne (k : Fin t) (hk : k ∈ ({a}ᶜ : Finset (Fin t))) :
      (u ^ a.val).val - (u ^ k.val).val ∣ ℓ ^ h := by
    rcases (show k ≠ a by simpa using hk).lt_or_gt with hlt | hgt
    · exact h_lt a k hlt
    · simpa using (h_lt k a hgt).neg_left
  calc
    n * ∏ k ∈ {a}ᶜ, ((u ^ a.val).val - (u ^ k.val).val) ∣
      ℓ ^ (3 * h) * ∏ _k ∈ ({a}ᶜ : Finset (Fin t)), (ℓ ^ h : ℤ_[ℓ]) :=
      mul_dvd_mul hn (prod_dvd_prod_of_dvd _ _ h_ne)
    _ = ℓ ^ ((3 + (t - 1)) * h) := by simp [card_compl, pow_add, add_mul, pow_mul']
    _ ∣ ℓ ^ (y * h) := pow_dvd_pow _ (Nat.mul_le_mul_right h (by grind [a.isLt]))

/-- A family of vectors, none of which lies in the span of the earlier ones, is linearly
independent. -/
lemma New.Selmer.linearIndependent_of_notMem_span_Iio {F V J : Type} [Field F] [AddCommGroup V]
    [Module F V] [LinearOrder J] {v : J → V}
    (hv : ∀ j : J, v j ∉ Submodule.span F (v '' Set.Iio j)) : LinearIndependent F v := by
  refine linearIndependent_iff_finset_linearIndependent.2 fun s ↦ (?_ : LinearIndepOn F v s)
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert j s h_lt ih =>
    rw [coe_insert]
    exact ih.insert fun h ↦ hv j (Submodule.span_mono
      (Set.image_mono (s := (s : Set J)) (t := Set.Iio j) fun x hx ↦ h_lt x hx) h)

/-- Let `ν > 0`, and let the maps `ψ i` from a group to `ℤ/ℓ^ν` send products to sums. If their
reductions modulo `ℓ` are linearly independent, then together they take every family of values (by
Nakayama's lemma). -/
lemma New.Selmer.surjective_of_linearIndependent_cast {ℓ ν : ℕ} [Fact ℓ.Prime] (hν : 0 < ν)
    {A ι : Type} [Group A] [Fintype ι] {ψ : ι → A → ZMod (ℓ ^ ν)}
    (h_mul : ∀ (i : ι) (a b : A), ψ i (a * b) = ψ i a + ψ i b)
    (h_indep : LinearIndependent (ZMod ℓ) fun (i : ι) (a : A) ↦ ((ψ i a).cast : ZMod ℓ)) :
    Surjective fun (a : A) (i : ι) ↦ ψ i a := by
  -- The image spans modulo `ℓ`, so by Nakayama's lemma it is everything.
  let red : ZMod (ℓ ^ ν) →+* ZMod ℓ := ZMod.castHom (dvd_pow_self ℓ hν.ne') (ZMod ℓ)
  let Ψ : Additive A →+ ι → ZMod (ℓ ^ ν) :=
    .mk' (fun a i ↦ ψ i a.toMul) fun a b ↦ funext fun i ↦ h_mul i _ _
  let Ψ₁ : Additive A →+ ι → ZMod ℓ := (red.toAddMonoidHom.compLeft ι).comp Ψ
  have h_span : (⊤ : Submodule (ZMod ℓ) (ι → ZMod ℓ)) ≤ Ψ₁.range.toZModSubmodule ℓ := by
    rw [← span_flip_eq_top_iff_linearIndependent.2 h_indep, Submodule.span_le]
    exact fun _ ⟨a, ha⟩ ↦ ⟨.ofMul a, ha⟩
  -- So the image and the multiples of `ℓ` generate everything.
  let N : Submodule (ZMod (ℓ ^ ν)) (ι → ZMod (ℓ ^ ν)) := Ψ.range.toZModSubmodule (ℓ ^ ν)
  let 𝔪 : Ideal (ZMod (ℓ ^ ν)) := .span {(ℓ : ZMod (ℓ ^ ν))}
  have h_sup : ⊤ ≤ N ⊔ 𝔪 • ⊤ := fun v _ ↦ by
    obtain ⟨a, ha⟩ : ∃ a, Ψ₁ a = fun i ↦ red (v i) := h_span Submodule.mem_top
    have h_dvd (i : ι) : (ℓ : ZMod (ℓ ^ ν)) ∣ v i - Ψ a i := by
      simpa using map_dvd (Int.castRingHom (ZMod (ℓ ^ ν)))
        ((ZMod.natCast_eq_natCast_iff (Ψ a i).val (v i).val ℓ).1
          (by simpa [Ψ₁, red] using congrFun ha i)).dvd
    choose t ht using h_dvd
    rw [show v = Ψ a + (ℓ : ZMod (ℓ ^ ν)) • t from funext fun i ↦ by simp [← ht i]]
    exact Submodule.add_mem_sup ⟨a, rfl⟩
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)
  have h_jacobson : 𝔪 ≤ Ring.jacobson (ZMod (ℓ ^ ν)) := by
    rw [← Ideal.jacobson_bot]
    exact (Ideal.span_singleton_le_iff_mem _).2
      (Ideal.radical_le_jacobson ⟨ν, (Nat.cast_pow ℓ ν).symm.trans (ZMod.natCast_self _)⟩)
  intro v
  obtain ⟨a, ha⟩ : v ∈ N := Submodule.le_of_le_smul_of_le_jacobson Module.Finite.fg_top
    h_jacobson h_sup Submodule.mem_top
  exact ⟨a.toMul, ha⟩

/-- Let `ℓ` be a prime, `Ω` the algebraic closure of `ℚ`, and `E ⊆ Ω` a CM field with a primitive
`5040`-th root of unity and at least four infinite places. Let `ν > 0`, and let `G_ν ≤ Gal(Ω/E)` be
the subgroup that fixes the `ℓ ^ ν`-th roots of unity. Let `x` be a finite family of split places
above distinct primes of the real subfield `F`, and let `v i : G_ν → ℤ/ℓ` be any maps with the same
indices. Then for some finite set `T` of primes of `F` that contains `familyPrimes ℓ x` (the primes
above `ℓ` or below the `x i`), some Kummer map `ψ` of exponent `e` for `x` off `T` has its reduction
`G_ν → ℤ/ℓ` outside the span of the `v i`. -/
lemma New.Selmer.exists_isKummerMap_notMem_span {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν : ℕ} (hν : 0 < ν) (e : ℕ) (h_inf_places : 4 ≤ Core.numInfPlaces E)
    {I : Type} [Fintype I] {x : I → FrobeniusDatum E} (hx : ∀ i : I, IsNuSplitPlace ν (x i))
    (primeBelow_inj : Injective fun i : I ↦ primeBelowPlus (x i).place)
    (v : I → (cyclotomicCharMod (Γ := Gal(Ω/E)) Ω (ℓ ^ ν)).ker → ZMod ℓ) :
    ∃ (T : Finset (FinPlace (NumberField.maximalRealSubfield E))) (ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)),
      familyPrimes ℓ x ⊆ T ∧ IsKummerMap e hx T ψ ∧
        reductionModL ψ ∉ Submodule.span (ZMod ℓ) (Set.range v) := by
  obtain ⟨T, hT, h_dim⟩ : ∃ T, familyPrimes ℓ x ⊆ T ∧
      Fintype.card I < Module.finrank (ZMod ℓ) (kummerReductions e hx T) :=
    exists_card_lt_finrank_kummerReductions hν e h_inf_places hx primeBelow_inj
  by_contra! h_mem
  -- Otherwise the Kummer reductions would span at most as many dimensions as there are maps `v`.
  have h_le : kummerReductions e hx T ≤ Submodule.span (ZMod ℓ) (Set.range v) :=
    Submodule.span_le.2 <| Set.image_subset_iff.2 fun ψ hψ ↦ h_mem T ψ hT hψ
  have : Module.Finite (ZMod ℓ) (Submodule.span (ZMod ℓ) (Set.range v)) :=
    .span_of_finite _ (Set.finite_range v)
  exact h_dim.not_ge ((Submodule.finrank_mono h_le).trans (finrank_range_le_card v))

/-- Conjugation separates the exponents. Let `cyc` be `cyclotomicCharMod Ω (ℓ ^ ν)`, with `Ω` the
algebraic closure of `ℚ`, and let `G_ν` be its kernel. For a finite set `s` of exponents below `t`
and `g ∈ G_ν` there is `g' ∈ G_ν` at which every map `ψ` of exponent `d` takes the value
`∏_{a ∈ s} (cyc γ ^ d - cyc γ ^ a) · ψ g`. -/
lemma New.Selmer.exists_apply_eq_prod_mul {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν t : ℕ} (γ : Gal(Ω/E)) {g : Gal(Ω/E)}
    (hg : cyclotomicCharMod Ω (ℓ ^ ν) g = 1) (s : Finset (Fin t)) :
    ∃ g' : Gal(Ω/E), cyclotomicCharMod Ω (ℓ ^ ν) g' = 1 ∧
      ∀ {d : ℕ} {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)}, HasKummerType ν d ψ → ψ g' =
        (∏ a ∈ s, ((cyclotomicCharMod Ω (ℓ ^ ν) γ).val ^ d -
          (cyclotomicCharMod Ω (ℓ ^ ν) γ).val ^ a.val)) * ψ g := by
  set c : (ZMod (ℓ ^ ν))ˣ := cyclotomicCharMod Ω (ℓ ^ ν) γ with hc
  induction s using Finset.induction with
  | empty => exact ⟨g, hg, by simp⟩
  | insert a s ha ih =>
    -- Conjugation by `γ` followed by the power `c⁻¹` multiplies a map of exponent `d` by `c ^ d`.
    obtain ⟨b, hb, hbψ⟩ := ih
    refine ⟨(γ * b * γ⁻¹) ^ (c⁻¹).val.val * b ^ (-c.val ^ a.val).val, by simp [hb],
      fun {d ψ} hψ ↦ ?_⟩
    calc ψ ((γ * b * γ⁻¹) ^ (c⁻¹).val.val * b ^ (-c.val ^ a.val).val)
        = (c⁻¹).val * (c.val ^ (d + 1) * ψ b) + -c.val ^ a.val * ψ b := by
          rw [hψ.map_mul (by simp [hb]) (by simp [hb]), hψ.map_pow (by simp [hb]), hψ.map_pow hb,
            hψ.map_conj γ hb, ← hc, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      _ = (c.val ^ d - c.val ^ a.val) * ψ b := by
          linear_combination (c.val ^ d * ψ b) * c.inv_mul
      _ = (∏ a' ∈ insert a s, (c.val ^ d - c.val ^ a'.val)) * ψ g := by
          rw [hbψ hψ, prod_insert ha, mul_assoc]

/-- The separating element for the auxiliary places. Let `ν > 0`, let `ψ i` be maps of exponent
`ty i` and `ψ₀` a map of exponent `e`. Suppose the reductions modulo `ℓ` (`reductionModL`) of the
`ψ i` with `ty i = e` are linearly independent, and the reduction of `ψ₀` is not in their span. Then
some `u` with `cyclotomicCharMod Ω (ℓ ^ ν) u = 1` has `ψ i u = 0` for all `i` and
`ψ₀ u = ∏_{k ≠ e} (cyc γ ^ e - cyc γ ^ k)` over the `k < t`. Here `cyc` is
`cyclotomicCharMod Ω (ℓ ^ ν)` and `Ω` is the algebraic closure of `ℚ`. -/
lemma New.Selmer.exists_separating_element {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν t : ℕ} (hν : 0 < ν) (γ : Gal(Ω/E)) (e : Fin t) {I : Type} [Fintype I]
    (ty : I → Fin t) {ψ : I → Gal(Ω/E) → ZMod (ℓ ^ ν)}
    (hψ : ∀ i : I, HasKummerType ν (ty i) (ψ i))
    (h_indep : LinearIndependent (ZMod ℓ) fun i : {i : I | ty i = e} ↦ reductionModL (ψ i))
    {ψ₀ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ₀ : HasKummerType ν e ψ₀)
    (h_notMem : reductionModL ψ₀ ∉
      Submodule.span (ZMod ℓ) (Set.range fun i : {i : I | ty i = e} ↦ reductionModL (ψ i))) :
    ∃ u : Gal(Ω/E), cyclotomicCharMod Ω (ℓ ^ ν) u = 1 ∧ (∀ i : I, ψ i u = 0) ∧
      ψ₀ u = ∏ k ∈ {e}ᶜ, ((cyclotomicCharMod Ω (ℓ ^ ν) γ).val ^ e.val -
        (cyclotomicCharMod Ω (ℓ ^ ν) γ).val ^ k.val) := by
  -- `ψ₀` and the maps of exponent `e` together are onto; let `g` go to `1` under `ψ₀` and to `0`
  -- under the others.
  let Ψ (o : Option {i : I | ty i = e}) (g : (cyclotomicCharMod (Γ := Gal(Ω/E)) Ω (ℓ ^ ν)).ker) :
      ZMod (ℓ ^ ν) := o.elim (ψ₀ g) fun i ↦ ψ i g
  have h_onto : Surjective fun g o ↦ Ψ o g := by
    refine surjective_of_linearIndependent_cast hν ?_ ?_
    · rintro (_ | i) a b
      exacts [hψ₀.map_mul a.property b.property, (hψ i).map_mul a.property b.property]
    · have h_eq : (fun o g ↦ ((Ψ o g).cast : ZMod ℓ)) =
          fun o ↦ o.casesOn' (reductionModL ψ₀) fun i ↦ reductionModL (ψ i) := by
        funext o
        cases o <;> rfl
      simpa only [h_eq] using h_indep.option h_notMem
  obtain ⟨g, hg⟩ := h_onto fun o ↦ o.elim 1 fun _ ↦ 0
  have hg₀ : ψ₀ g = 1 := congrFun hg none
  have hg_zero (i : I) (hi : ty i = e) : ψ i g = 0 := congrFun hg (some ⟨i, hi⟩)
  -- Remove the other exponents by conjugation.
  obtain ⟨u, hu, huψ⟩ := exists_apply_eq_prod_mul γ g.property {e}ᶜ
  refine ⟨u, hu, fun i ↦ ?_, ?_⟩
  · rw [huψ (hψ i)]
    by_cases hi : ty i = e
    · exact mul_eq_zero_of_right _ (hg_zero i hi)
    · exact mul_eq_zero_of_left (prod_eq_zero (i := ty i) (by simpa using hi) (sub_self _)) _
  · rw [huψ hψ₀, hg₀, mul_one]

/-- Let `δ, g` have trivial cyclotomic character, let `u` fix `μ_{ℓ^ν}`, and let `f`, with values in
`ℤ/ℓ^ν`, satisfy `f (a * b) = f a + f b` whenever `a` has trivial cyclotomic character and `b` fixes
`μ_{ℓ^ν}`. In its value at `δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))` the first factor
contributes `ℓ ^ ν • f δ = 0`, which leaves a signed sum of the values at
`g, conjGal g, u, conjGal u`. -/
lemma New.Selmer.additive_apply_pow_mul_conj {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν : ℕ} {δ g u : Gal(Ω/E)} (hδ : cyclotomicChar Ω ℓ δ = 1)
    (hg : cyclotomicChar Ω ℓ g = 1) (hu : cyclotomicCharMod Ω (ℓ ^ ν) u = 1)
    {f : Gal(Ω/E) → ZMod (ℓ ^ ν)}
    (hf : ∀ a b : Gal(Ω/E), cyclotomicChar Ω ℓ a = 1 →
      cyclotomicCharMod Ω (ℓ ^ ν) b = 1 → f (a * b) = f a + f b) :
    f (δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))) =
      f g + f (conjGal g) + (f u - f (conjGal u)) := by
  have h_div : f u = f (u / conjGal u) + f (conjGal u) := by
    -- `conjGal` preserves the cyclotomic character.
    simpa using hf (u / conjGal u) (conjGal u) (by simp)
      (by simpa [cyclotomicCharMod_prime_pow_eq] using hu)
  have h_pow (n : ℕ) :
      f (δ ^ n * (g * conjGal g * (u / conjGal u))) =
        n • f δ + (f g + f (conjGal g) + f (u / conjGal u)) := by
    induction n with
    | zero => simp [hf, hg, cyclotomicCharMod_prime_pow_eq]
    | succ n ih =>
      rw [pow_succ', mul_assoc, hf δ _ hδ (by simp [cyclotomicCharMod_prime_pow_eq, hδ, hg]), ih,
        succ_nsmul]
      ring
  simp [h_pow, h_div, CharP.cast_eq_zero]

/-- Let `Ω` be the algebraic closure of `ℚ`, let `δ, g : Gal(Ω/E)` have trivial `ℓ`-adic cyclotomic
character `cyc`, and let `u` lie in the group `G_ν` that fixes `μ_{ℓ^ν}`. Near
`δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))`, where `conjGal` is conjugation by complex
conjugation, a map `ψ` of exponent `e` takes the value `2 * ψ u`. -/
lemma New.Selmer.HasKummerType.eventually_eq_two_mul {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν e : ℕ} {ψ : Gal(Ω/E) → ZMod (ℓ ^ ν)} (hψ : HasKummerType ν e ψ)
    {δ g u : Gal(Ω/E)} (hδ : cyclotomicChar Ω ℓ δ = 1) (hg : cyclotomicChar Ω ℓ g = 1)
    (hu : cyclotomicCharMod Ω (ℓ ^ ν) u = 1) :
    ∀ᶠ s in nhds (δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))), ψ s = 2 * ψ u := by
  have h_val : ψ (δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))) = 2 * ψ u := by
    rw [additive_apply_pow_mul_conj hδ hg hu fun a b ha hb ↦
        hψ.map_mul (by simp [cyclotomicCharMod_prime_pow_eq, ha]) hb,
      hψ.map_conjGal hu, hψ.map_conjGal (a := g) (by simp [cyclotomicCharMod_prime_pow_eq, hg])]
    ring
  rw [← h_val]
  exact hψ.isLocallyConstant.eventually_eq _

/-- Let `Ω` be the algebraic closure of `ℚ`, let `δ, g : Gal(Ω/E)` have trivial cyclotomic character
and let `u` fix `μ_{ℓ^ν}`; let `conjGal` be conjugation by complex conjugation. Near
`δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))` all even classes `c` of exponent `e` unramified off
`ℓ`, for all coefficient rings `O`, take the value `2 • c g`. -/
lemma New.Selmer.evenClasses_eventually_eq_two_nsmul {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν : ℕ} (e : ℕ) {δ g u : Gal(Ω/E)} (hδ : cyclotomicChar Ω ℓ δ = 1)
    (hg : cyclotomicChar Ω ℓ g = 1) (hu : cyclotomicCharMod Ω (ℓ ^ ν) u = 1) :
    ∀ᶠ s in nhds (δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))),
      ∀ O : CoeffRing ℓ, ∀ c ∈ evenClasses O ∅ ν e, c s = 2 • c g := by
  set σ : Gal(Ω/E) := δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u))
  -- There are finitely many cocycles in `ℤ/ℓ^ν(-e)` unramified off `ℓ`; all are constant near `σ`.
  let χ : Gal(Ω/E) →* (ZMod (ℓ ^ ν))ˣ := cyclotomicCharMod Ω (ℓ ^ ν)
  let V : DiscreteModule (ZMod (ℓ ^ ν)) Gal(Ω/E) :=
    .of (charRep (ZMod (ℓ ^ ν)) (χ ^ e)⁻¹)
      ((((Continuous.of_isOpen_ker χ Fact.out).pow e).inv).fst'.smul continuous_snd)
  have h_const : ∀ᶠ s in nhds σ,
      ∀ c ∈ Z1 V.ρ ⊓ .pi (inertiaAbove (placesDividing E ℓ)ᶜ) ⊥, c s = c σ :=
    (selmerZ1.finite_unramified_cocycles V (placesDividing E ℓ).toFinite).eventually_all.mpr
      fun c ⟨⟨hc_cont, _⟩, _⟩ ↦ (continuous_discrete_rng.mp hc_cont (c σ)).mem_nhds rfl
  filter_upwards [h_const] with s hs O c hc
  -- It is enough to test against the additive maps `φ` to `ℤ/ℓ^ν` that make `φ ∘ c` a continuous
  -- cocycle for `V`.
  have ⟨hc_sel, hc_even, _⟩ := hc
  obtain ⟨hc_coc, hc_unr, -, -⟩ := mem_selmerModule_iff.mp hc_sel
  refine sub_eq_zero.mp (eq_zero_of_forall_mem_Z1_of_mem_evenClasses hc fun φ hφ ↦ ?_)
  have h_mem :
      (fun a : Gal(Ω/E) ↦ φ (c a)) ∈ Z1 V.ρ ⊓ .pi (inertiaAbove (placesDividing E ℓ)ᶜ) ⊥ :=
    ⟨hφ, by simp +contextual [hc_unr]⟩
  have h_add (a b : Gal(Ω/E)) (ha : cyclotomicChar Ω ℓ a = 1)
    (_ : cyclotomicCharMod Ω (ℓ ^ ν) b = 1) :
      φ (c (a * b)) = φ (c a) + φ (c b) := by simp [hc_coc, tateTwist, cyclotomicInv, ha]
  have h_val : φ (c s) = φ (c g) + φ (c (conjGal g)) + (φ (c u) - φ (c (conjGal u))) :=
    (hs _ h_mem).trans (additive_apply_pow_mul_conj (f := fun a ↦ φ (c a)) hδ hg hu h_add)
  -- As `c` is even, the values at `g, conjGal g` add up and those at `u, conjGal u` cancel.
  have h_two : φ (c s) = φ (c g) + φ (c g) := by simpa [hc_even] using h_val
  rw [map_sub, h_two, map_nsmul, two_nsmul, sub_self]

/-- Choice along a well-founded order: if, for every `f` whose values before `j` satisfy `P` with
their predecessors, some value satisfies `P j` with the values of `f` before `j`, then some function
satisfies `P` at every index with its values at the earlier ones. -/
lemma New.Selmer.exists_forall_of_wellFoundedLT {J X : Type} [Preorder J] [WellFoundedLT J]
    [Nonempty X] {P : ∀ j : J, (Set.Iio j → X) → X → Prop}
    (h_step : ∀ (f : J → X) (j : J),
      (∀ i : J, i < j → P i (fun k : Set.Iio i ↦ f k) (f i)) →
        ∃ x : X, P j (fun k : Set.Iio j ↦ f k) x) :
    ∃ f : J → X, ∀ j : J, P j (fun i : Set.Iio j ↦ f i) (f j) := by
  let f : J → X := fix fun j g ↦ Classical.epsilon (P j fun i ↦ g i i.prop)
  refine ⟨f, fun j ↦ ?_⟩
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    rw [show f j = Classical.epsilon (P j fun i : Set.Iio j ↦ f i) from fix_eq _ j]
    exact Classical.epsilon_spec (h_step f j ih)

/-- What is chosen at one index of the triangle: a split place of `E`, a map from `Gal(Ω/E)` to
`ℤ/ℓ^ν` (`Ω` is the algebraic closure of `ℚ`), and a finite set of primes of the real subfield that
this place and the later ones have to avoid. -/
structure New.Selmer.TriangleEntry (ℓ : ℕ) (E : Type) [ThePrime ℓ] [Field E] [CMFieldWithRoot5040 E]
    (ν : ℕ) where
  /-- The place with its Frobenius element. -/
  frobeniusDatum : FrobeniusDatum E
  /-- The place is not above `ℓ` and its Frobenius element fixes the `ℓ^ν`-th roots of unity. -/
  isNuSplitPlace : IsNuSplitPlace (ℓ := ℓ) ν frobeniusDatum
  /-- The primes to avoid. -/
  avoidedPrimes : Finset (FinPlace (NumberField.maximalRealSubfield E))
  /-- The map, a Kummer map once the entry follows earlier ones. -/
  kummerCandidate : Gal(Ω/E) → ZMod (ℓ ^ ν)

/-- The entry `q` of exponent `e` may follow the entries `f i` of exponents `ty i`: its map is a
Kummer map for the earlier places of exponent `e` and new modulo `ℓ`, and its place is a new one in
`W`, at whose Frobenius element the earlier maps vanish, twice the value of the new map divides the
loss `n`, and the even classes of exponent `e` unramified off `ℓ` take twice their value at the test
element `g`. -/
structure New.Selmer.TriangleEntry.MayFollow {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν t : ℕ} {K : Type} [Finite K] (ty : K → Fin t)
    (f : K → TriangleEntry ℓ E ν) (e : Fin t) (g : Gal(Ω/E)) (n : ℕ) (W : Set (FrobeniusDatum E))
    (q : TriangleEntry ℓ E ν) : Prop where
  /-- The new map is a Kummer map of exponent `e` off `q.avoidedPrimes`: the restriction of a
  relation over the real subfield that is unramified off `q.avoidedPrimes` and whose reciprocity law
  holds at split primes off `q.avoidedPrimes`, for cocycles with local conditions above `ℓ` and
  below the earlier places of exponent `e`. -/
  isKummerMap : IsKummerMap e (fun i : {i : K | ty i = e} ↦ (f i).isNuSplitPlace) q.avoidedPrimes
    q.kummerCandidate
  /-- The primes to avoid include the primes of the real subfield above `ℓ` or below an earlier
  place of exponent `e`. -/
  familyPrimes_subset : familyPrimes ℓ (fun i : {i : K | ty i = e} ↦ (f i).frobeniusDatum) ⊆
    q.avoidedPrimes
  /-- Modulo `ℓ` the new map is independent of the earlier maps of exponent `e`. -/
  notMem_span : reductionModL q.kummerCandidate ∉
    Submodule.span (ZMod ℓ) (Set.range fun i : {i : K | ty i = e} ↦
      reductionModL (f i).kummerCandidate)
  /-- At the new Frobenius element the new map is nearly a unit: twice its value divides `n`. -/
  two_mul_dvd : 2 * q.kummerCandidate q.frobeniusDatum.frob ∣ n
  /-- At the new Frobenius element the earlier maps vanish. -/
  apply_eq_zero (i : K) : (f i).kummerCandidate q.frobeniusDatum.frob = 0
  /-- At the new Frobenius element the even classes of exponent `e` unramified off `ℓ` take twice
  their value at `g`. -/
  even_apply (O : CoeffRing ℓ) : ∀ z ∈ evenClasses O ∅ ν e, z q.frobeniusDatum.frob = 2 • z g
  /-- The new place lies above a new prime of the real subfield. -/
  primeBelowPlus_ne (i : K) : primeBelowPlus (f i).frobeniusDatum.place ≠ primeBelowPlus
    q.frobeniusDatum.place
  /-- It avoids the primes excluded by the earlier maps. -/
  notMem_earlier (i : K) : primeBelowPlus q.frobeniusDatum.place ∉ (f i).avoidedPrimes
  /-- It avoids the primes excluded by the new map. -/
  notMem : primeBelowPlus q.frobeniusDatum.place ∉ q.avoidedPrimes
  /-- The new place, with its Frobenius element, is allowed. -/
  mem : q.frobeniusDatum ∈ W

/-- Almost all places of `E` lie neither above `ℓ` nor above a prime in a given finite set `T` of
primes of the real subfield. -/
lemma New.Selmer.eventually_primeBelowPlus_notMem {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {T : Set (FinPlace (NumberField.maximalRealSubfield E))}
    (hT : T.Finite) :
    ∀ᶠ w : FinPlace E in cofinite, ↑ℓ ∉ w.asIdeal ∧ primeBelowPlus w ∉ T := by
  filter_upwards [GaloisRep.eventually_notMem_star_notMem ℓ ∅, tendsto_place_comap_cofinite
    (algebraMap (NumberField.maximalRealSubfield E) E) hT.compl_mem_cofinite]
    with w ⟨_, _, h_off⟩ h_avoid using ⟨h_off, h_avoid⟩

/-- Let `ℓ` be a prime and `E` a CM field with a primitive `5040`-th root of unity and at least four
infinite places. Let `ν > 0`, `t + 2 ≤ y` and `4 ∣ ℓ ^ (3 h)`, let `cyc γ ^ a - 1` divide `ℓ ^ h`
for `0 < a < t`, let `g` have trivial cyclotomic character `cyc`, and, for every `g'`, let `W`
contain most Frobenii near `δ ^ ℓ ^ ν * g'` for some `δ` with trivial cyclotomic character. Let
finitely many entries `f i` lie above distinct primes of `F`, let their maps have exponents `ty i`,
and let those of exponent `e` be independent as maps `G_ν → ℤ/ℓ` (`reductionModL`). Then some entry
`q` may follow them (`MayFollow`): its map is a Kummer map of exponent `e` for the earlier places of
exponent `e`, off a set `q.avoidedPrimes` that contains the primes above `ℓ` and below these places,
and is outside the span modulo `ℓ` of the earlier maps of exponent `e`; the prime of `F` below its
place is none of the earlier ones and lies in none of the sets of primes to avoid; its datum lies in
`W`; at its Frobenius element the earlier maps vanish, twice the value of the new map divides the
loss `ℓ ^ (y * h)`, and the even classes of exponent `e` unramified off `ℓ` take twice their value
at `g`. -/
lemma New.Selmer.TriangleEntry.exists_mayFollow {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν t y h : ℕ} {γ g : Gal(Ω/E)} (hν : 0 < ν)
    (h_inf_places : 4 ≤ Core.numInfPlaces E) (hty : t + 2 ≤ y)
    (hγ_dvd : ∀ a ∈ Set.Ioo 0 t, (cyclotomicChar Ω ℓ γ ^ a).val - 1 ∣ ℓ ^ h) (e : Fin t)
    (h_four : (4 : ℤ_[ℓ]) ∣ ℓ ^ (3 * h)) (hg : cyclotomicChar Ω ℓ g = 1)
    {W : Set (FrobeniusDatum E)} (hW : ∀ g' : Gal(Ω/E),
      ∃ δ : Gal(Ω/E), cyclotomicChar Ω ℓ δ = 1 ∧ W ∈ mostFrobeniiAt E (δ ^ ℓ ^ ν * g'))
    {I : Type} [Fintype I] (ty : I → Fin t) {f : I → TriangleEntry ℓ E ν}
    (primeBelow_inj : Injective fun i : I ↦ primeBelowPlus (f i).frobeniusDatum.place)
    (h_type : ∀ i : I, HasKummerType ν (ty i) (f i).kummerCandidate)
    (h_indep : LinearIndependent (ZMod ℓ) fun i : {i : I | ty i = e} ↦
      reductionModL (f i).kummerCandidate) :
    ∃ q : TriangleEntry ℓ E ν, MayFollow ty f e g (ℓ ^ (y * h)) W q := by
  -- Take a new map `ψ₀`, a point `u` where the earlier maps vanish while `ψ₀ u` is
  -- `∏_{k ≠ e} (cyc γ ^ e - cyc γ ^ k)`, and a Frobenius element near a suitable `σ`.
  obtain ⟨T₀, ψ₀, hT₀, hψ₀, h_notMem⟩ := exists_isKummerMap_notMem_span hν e h_inf_places
    (fun i : {i : I | ty i = e} ↦ (f i).isNuSplitPlace) (primeBelow_inj.comp Subtype.val_injective)
    fun i ↦ reductionModL (f i).kummerCandidate
  obtain ⟨u, hu, hψu, hψ₀u⟩ :=
    exists_separating_element hν γ e ty h_type h_indep hψ₀.hasKummerType h_notMem
  obtain ⟨δ, hδ, hσW⟩ := hW (g * conjGal g * (u / conjGal u))
  set σ : Gal(Ω/E) := δ ^ ℓ ^ ν * (g * conjGal g * (u / conjGal u)) with hσ
  have hσ_cyc : σ ∈ (cyclotomicCharMod Ω (ℓ ^ ν)).ker := by
    simp [hσ, cyclotomicCharMod_prime_pow_eq, hδ, hg]
  have h_near : ∀ᶠ s in nhds σ, ψ₀ s = 2 * ψ₀ u ∧
    (∀ i, (f i).kummerCandidate s = 2 * (f i).kummerCandidate u) ∧
      (∀ O, ∀ z ∈ evenClasses O ∅ ν e, z s = 2 • z g) ∧ cyclotomicCharMod Ω (ℓ ^ ν) s = 1 :=
    (hψ₀.hasKummerType.eventually_eq_two_mul hδ hg hu).and <|
      (eventually_all.2 fun i ↦ (h_type i).eventually_eq_two_mul hδ hg hu).and <|
      (evenClasses_eventually_eq_two_nsmul e hδ hg hu).and
        (isOpen_ker_cyclotomicCharMod.out.mem_nhds hσ_cyc)
  let T' : Set (FinPlace (NumberField.maximalRealSubfield E)) :=
    T₀ ∪ ⋃ i, insert (primeBelowPlus (f i).frobeniusDatum.place) (f i).avoidedPrimes
  have h_most : ∀ᶠ x : FrobeniusDatum E in mostFrobenii E,
      ↑ℓ ∉ x.place.asIdeal ∧ primeBelowPlus x.place ∉ T' :=
    eventually_mostFrobenii (eventually_primeBelowPlus_notMem (Set.toFinite T')) fun _ ↦ id
  -- The filter `mostFrobeniiAt E σ` is proper (Chebotarev): some `x₀` has all this.
  obtain ⟨x₀, hW₀, ⟨h_off, hT'⟩, hψ₀x, hψx, h_even, h_cyc⟩ :=
    nonempty_of_mem (inter_mem hσW (inter_mem_inf h_most (preimage_mem_comap h_near)))
  have h_dvd : 2 * ψ₀ x₀.frob ∣ ↑(ℓ ^ (y * h)) := by
    have h_int : (4 : ℤ_[ℓ]) * ∏ k ∈ {e}ᶜ,
        ((cyclotomicChar Ω ℓ γ ^ e.val).val - (cyclotomicChar Ω ℓ γ ^ k.val).val) ∣ ℓ ^ (y * h) :=
      mul_prod_pow_sub_pow_dvd hty hγ_dvd e h_four
    rw [hψ₀x, hψ₀u, ← mul_assoc, show (2 * 2 : ZMod (ℓ ^ ν)) = 4 by norm_num]
    -- This is the divisibility `h_int` reduced modulo `ℓ ^ ν`.
    simpa [cyclotomicCharMod_prime_pow_eq, map_ofNat] using map_dvd (toZModPow ν) h_int
  obtain ⟨h_notMem₀, h_avoid⟩ : primeBelowPlus x₀.place ∉ T₀ ∧ ∀ i : I,
      primeBelowPlus (f i).frobeniusDatum.place ≠ primeBelowPlus x₀.place ∧
        primeBelowPlus x₀.place ∉ (f i).avoidedPrimes := by simpa [T', eq_comm] using hT'
  exact ⟨⟨x₀, ⟨h_off, h_cyc⟩, T₀, ψ₀⟩,
    { isKummerMap := hψ₀, familyPrimes_subset := hT₀, notMem_span := h_notMem
      two_mul_dvd := h_dvd
      apply_eq_zero := fun i ↦ by rw [hψx i, hψu i, mul_zero]
      even_apply := h_even
      primeBelowPlus_ne := fun i ↦ (h_avoid i).1, notMem_earlier := fun i ↦ (h_avoid i).2
      notMem := h_notMem₀, mem := hW₀ }⟩

/-- Some entry exists: at a split place, with the zero map and no primes to avoid. -/
instance New.Selmer.TriangleEntry.nonempty {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν : ℕ} : Nonempty (TriangleEntry ℓ E ν) := by
  have h_near : ∀ᶠ s : Gal(Ω/E) in nhds 1, cyclotomicCharMod Ω (ℓ ^ ν) s = 1 :=
    isOpen_ker_cyclotomicCharMod.out.mem_nhds (map_one _)
  obtain ⟨x, ⟨h_off, -⟩, h_cyc⟩ := nonempty_of_mem (f := mostFrobeniiAt E 1) (inter_mem_inf
    (eventually_mostFrobenii (eventually_primeBelowPlus_notMem (ℓ := ℓ) Set.finite_empty)
      fun _ ↦ id) (preimage_mem_comap h_near))
  exact ⟨x, ⟨h_off, h_cyc⟩, ∅, 0⟩

/-- Let `ℓ` be a prime, `E` a CM field with a primitive `5040`-th root of unity and at least four
infinite places, inside the algebraic closure `Ω` of `ℚ`, and `cyc` the `ℓ`-adic cyclotomic
character. Along a finite linear order `J`, with exponents `ty j` and test elements `g j` of trivial
`cyc`, entries `f j` can be chosen so that each may follow the earlier ones (`MayFollow`): its map
is a Kummer map of exponent `ty j` for the earlier places of this exponent, off its set of primes to
avoid, and is independent of their maps modulo `ℓ` on the elements fixing `μ_{ℓ^ν}`; the prime of
`F` below its place is new and avoided by none of the maps up to it; its Frobenius datum is in `W`;
at its Frobenius element the earlier maps vanish, twice the value of its map divides the loss
`ℓ ^ (y * h)`, and the even classes of exponent `ty j` unramified off `ℓ` take twice their value at
`g j`. As in `New.Selmer.TriangleEntry.exists_mayFollow`, it is assumed that `ν > 0`, that
`t + 2 ≤ y`, that `cyc γ ^ a - 1` divides `ℓ ^ h` for `0 < a < t`, that `4 ∣ ℓ ^ (3 h)` unless `J`
is empty, and that for every `g'` there is a `δ` of trivial `cyc` such that `W` contains most
Frobenii near `δ ^ ℓ ^ ν * g'` (`mostFrobeniiAt`). -/
lemma New.Selmer.TriangleEntry.exists_forall_mayFollow {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν t y h : ℕ} {γ : Gal(Ω/E)} (hν : 0 < ν)
    (h_inf_places : 4 ≤ Core.numInfPlaces E) (hty : t + 2 ≤ y)
    (hγ_dvd : ∀ a ∈ Set.Ioo 0 t, (cyclotomicChar Ω ℓ γ ^ a).val - 1 ∣ ℓ ^ h)
    {W : Set (FrobeniusDatum E)} (hW : ∀ g' : Gal(Ω/E),
      ∃ δ : Gal(Ω/E), cyclotomicChar Ω ℓ δ = 1 ∧ W ∈ mostFrobeniiAt E (δ ^ ℓ ^ ν * g'))
    {J : Type} [Fintype J] [LinearOrder J] (ty : J → Fin t) {g : J → Gal(Ω/E)}
    (hg : ∀ j : J, cyclotomicChar Ω ℓ (g j) = 1) (h_four : Nonempty J → (4 : ℤ_[ℓ]) ∣ ℓ ^ (3 * h)) :
    ∃ f : J → TriangleEntry ℓ E ν, ∀ j : J, MayFollow (fun i : Set.Iio j ↦ ty i)
      (fun i : Set.Iio j ↦ f i) (ty j) (g j) (ℓ ^ (y * h)) W (f j) := by
  refine exists_forall_of_wellFoundedLT (P := fun j f ↦
    MayFollow (fun i : Set.Iio j ↦ ty i) f (ty j) (g j) (ℓ ^ (y * h)) W) fun f j h_prev ↦ ?_
  have h_inj : Injective fun i : Set.Iio j ↦ primeBelowPlus (f i).frobeniusDatum.place :=
    .of_lt_imp_ne fun a b hab ↦ (h_prev b b.property).primeBelowPlus_ne ⟨a, hab⟩
  have h_type (i : Set.Iio j) : HasKummerType ν (ty i) (f i).kummerCandidate :=
    (h_prev i i.property).isKummerMap.hasKummerType
  -- By induction the earlier maps of the exponent of `j` are independent modulo `ℓ`.
  have h_indep : LinearIndependent (ZMod ℓ)
      fun i : {i : Set.Iio j | ty i = ty j} ↦ reductionModL (f i.val).kummerCandidate := by
    refine linearIndependent_of_notMem_span_Iio fun i h_mem ↦
      (h_prev i i.val.property).notMem_span (Submodule.span_mono ?_ h_mem)
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨⟨⟨k, hk⟩, k.property.trans i.property.symm⟩, rfl⟩
  exact exists_mayFollow hν h_inf_places hty hγ_dvd (ty j) (h_four ⟨j⟩) (hg j) hW _ h_inj h_type
    h_indep

/-- If the entries `f j` are indexed by a finite linear order and each may follow the earlier ones
(`MayFollow`), then their places lie above distinct primes of the real subfield. -/
lemma New.Selmer.TriangleEntry.primeBelowPlus_injective_of_mayFollow {ℓ : ℕ} {E : Type} [ThePrime ℓ]
    [Field E] [CMFieldWithRoot5040 E] {ν t n : ℕ} {W : Set (FrobeniusDatum E)}
    {J : Type} [Fintype J] [LinearOrder J] {ty : J → Fin t}
    {g : J → Gal(Ω/E)} {f : J → TriangleEntry ℓ E ν} (hf : ∀ j : J,
      MayFollow (fun i : Set.Iio j ↦ ty i) (fun i : Set.Iio j ↦ f i) (ty j) (g j) n W (f j)) :
    Injective fun j : J ↦ primeBelowPlus (f j).frobeniusDatum.place :=
  .of_lt_imp_ne fun a b hab ↦ (hf b).primeBelowPlus_ne ⟨a, hab⟩

/-- The places of entries, with their tame generators and Frobenius elements, form a tame generator
family (`New.Selmer.IsTameGeneratorFamily`): they are not above `ℓ`, the Frobenius elements fix
`μ_{ℓ^ν}`, and the tame generators are the chosen ones at places of `Ω` above them. -/
lemma New.Selmer.TriangleEntry.isTameGeneratorFamily {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν : ℕ} {J : Type} (f : J → TriangleEntry ℓ E ν) :
    IsTameGeneratorFamily ν (fun j : J ↦ (f j).frobeniusDatum.place)
      (fun j : J ↦ (f j).frobeniusDatum.isPlaceOver.tameGenerator)
      fun j : J ↦ (f j).frobeniusDatum.frob := fun j ↦
  ⟨(f j).isNuSplitPlace.1, (f j).isNuSplitPlace.2, _, (f j).frobeniusDatum.isPlaceOver, rfl⟩

/-- Let the entries `f j`, of exponents `ty j`, be indexed by a finite linear order `J`, and suppose
that each may follow the earlier ones with test element `g j`, loss `n` and Frobenius data in `W`.
Let `z` be an even class of exponent `ty j`: a cocycle on `Gal(Ω/E)` in `(O/ℓ^ν)(-ty j)`, written as
a function with values in `Unit → O/ℓ^ν`, invariant under complex conjugation and trivial on the
elements of trivial cyclotomic character in the decomposition groups above `ℓ`, here allowed to
ramify at `ℓ`, at the places of the entries and at their conjugates. Let it vanish at the tame
generators of the places before `j` and at the Frobenius elements of those among them of exponent
`ty j`. Then `n` kills the value of `z` at the tame generator of the `j`-th place. -/
lemma New.Selmer.TriangleEntry.nsmul_tameGenerator_eq_zero_of_mayFollow {ℓ : ℕ} {E : Type}
    [ThePrime ℓ] [Field E] [CMFieldWithRoot5040 E] {ν t n : ℕ} {W : Set (FrobeniusDatum E)}
    {J : Type} [Fintype J] [LinearOrder J] {ty : J → Fin t} {g : J → Gal(Ω/E)}
    {f : J → TriangleEntry ℓ E ν} (hf : ∀ j : J,
      MayFollow (fun i : Set.Iio j ↦ ty i) (fun i : Set.Iio j ↦ f i) (ty j) (g j) n W (f j))
    {O : CoeffRing ℓ} {j : J} {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)}
    (hz : z ∈ evenClasses O (Set.range fun i : J ↦ (f i).frobeniusDatum.place) ν (ty j))
    (hz_tame : ∀ i : J, i < j → z (f i).frobeniusDatum.isPlaceOver.tameGenerator = 0)
    (hz_frob : ∀ i : J, i < j → ty i = ty j → z (f i).frobeniusDatum.frob = 0) :
    n • z (f j).frobeniusDatum.isPlaceOver.tameGenerator = 0 := by
  -- As `z` kills the earlier tame generators, it is unramified at the earlier places, so the
  -- reciprocity law of the `j`-th Kummer map applies at the places from `j` on.
  have h_range : (Set.range fun i : J ↦ (f i).frobeniusDatum.place) =
      (Set.range fun i : Set.Ici j ↦ (f i).frobeniusDatum.place) ∪ .range fun i : Set.Iio j ↦
        (f i).frobeniusDatum.place := by
    simp [← Set.image_eq_range fun i : J ↦ (f i).frobeniusDatum.place, ← Set.image_union,
      Set.union_comm (.Ici j)]
  have h_subset : placesDividing E ℓ ∪ Set.conjClosure
    (.range fun i : J ↦ (f i).frobeniusDatum.place) ⊆
      placesDividing E ℓ ∪ Set.conjClosure (.range fun i : Set.Ici j ↦ (f i).frobeniusDatum.place) ∪
        Set.conjClosure (.range fun i : Set.Iio j ↦ (f i).frobeniusDatum.place) := by
    simp only [h_range, Set.conjClosure, Set.preimage_union, Set.subset_def, Set.mem_union]
    tauto
  obtain ⟨hz_mem, hz_even⟩ := hz
  have h_tame : ∀ i : Set.Iio j × Bool,
      z (withConjInv (fun i : Set.Iio j ↦ (f i).frobeniusDatum.isPlaceOver.tameGenerator.val) i) =
        0 := by
    simp +contextual [idOrConjInv, cocycle_apply_inv (mem_selmerModule_iff.1 hz_mem).1,
      hz_even.1, hz_tame, -smul_eq_zero]
  have hz_later : z ∈ evenClasses O (.range fun i : Set.Ici j ↦ (f i).frobeniusDatum.place) ν
    (ty j) :=
    ⟨(isTameGeneratorFamily fun i : Set.Iio j ↦ f i).mem_selmerModule_of_tame_eq_zero hz_mem h_tame
      h_subset
      fun _ _ ↦ tateTwist_eq_one_of_cyclotomicChar_eq_one, hz_even⟩
  have h_allowed : ∀ i : Set.Ici j, primeBelowPlus (f i).frobeniusDatum.place ∉
    (f j).avoidedPrimes := fun ⟨i, hji⟩ ↦ by
    obtain rfl | hlt := eq_or_lt_of_le (α := J) hji
    · exact (hf j).notMem
    · exact (hf i).notMem_earlier ⟨j, hlt⟩
  -- The `j`-th map vanishes at the later Frobenius elements.
  have h_zero (i : Set.Ici j) (hi : i ≠ ⊥) : (f j).kummerCandidate (f i).frobeniusDatum.frob = 0 :=
    (hf i).apply_eq_zero ⟨j, hi.bot_lt⟩
  have h_inj : Injective fun i : Set.Ici j ↦ primeBelowPlus (f i).frobeniusDatum.place :=
    (primeBelowPlus_injective_of_mayFollow hf).injOn.injective
  have h_frob : ∀ i : {i : Set.Iio j | ty i = ty j}, z (f i).frobeniusDatum.frob = 0 :=
    fun ⟨⟨i, hi⟩, hty⟩ ↦ hz_frob i hi hty
  -- So the reciprocity law of the `j`-th map applies, with `j` as the least of the later indices.
  exact (hf j).isKummerMap.nsmul_apply_tameGenerator_eq_zero (hf j).familyPrimes_subset
    (w := fun i : Set.Ici j ↦ (f i).frobeniusDatum) (fun i ↦ (f i).isNuSplitPlace) h_inj h_allowed
      (j := ⊥)
    h_zero hz_later h_frob (hf j).two_mul_dvd

/-- If the datum `x` is `ν`-split (`IsNuSplitPlace`: its prime is not above `ℓ` and its Frobenius
element fixes `μ_{ℓ^ν}`), then `ℓ ^ ν` divides `x.place.q - 1`, i.e. the norm `q` of its place is
`1` modulo `ℓ ^ ν`. -/
lemma New.Selmer.IsNuSplitPlace.prime_pow_dvd_q_sub_one {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] {ν : ℕ} {x : FrobeniusDatum E} (hx : IsNuSplitPlace (ℓ := ℓ) ν x) :
    ℓ ^ ν ∣ x.place.q - 1 :=
  have h_modEq : x.place.q ≡ 1 [MOD ℓ ^ ν] := (x.isFrob_inv.mem_ker_cyclotomicCharMod_iff
    (by simp [x.isPlaceOver.valuation_natCast_eq_one_iff, hx.1])).1 (inv_mem hx.2)
  h_modEq.symm.dvd'

/-- Places of prime norm above distinct primes of the real subfield are distinct from each other and
from all their conjugates. -/
lemma New.Selmer.isConjApart_of_injective_primeBelowPlus {E : Type} [Field E]
    [CMFieldWithRoot5040 E] {J : Type} {x : J → FrobeniusDatum E}
    (hx : Injective fun j : J ↦ primeBelowPlus (x j).place) :
    IsConjApart fun j : J ↦ (x j).place := by
  refine ⟨.of_comp (f := primeBelowPlus) hx, fun i j hij ↦ ?_⟩
  obtain rfl : i = j := hx (by simp only [← hij, primeBelowPlus_star])
  -- A place of prime norm is not its own conjugate.
  exact isSplit_of_q_prime (x i).prime_q hij

/-- Let `ℓ` be a prime, `cyc` the `ℓ`-adic cyclotomic character, and `E` a CM field with a primitive
`5040`-th root of unity and at least four infinite places, inside the algebraic closure `Ω` of `ℚ`,
that lies in the cyclotomic field of level `N > 0`. Let `N + t < y`, let `γ` generate `Gal(Ω/E)`
topologically modulo the kernel of `cyc`, let `cyc γ ^ a - 1` divide `ℓ ^ h` for `0 < a < t`, let
`ℓ ≤ y ^ 2` or `h = 0`, and suppose that for all `ν` and `g` there is a `δ` of trivial `cyc` such
that `W` contains most Frobenii near `δ ^ ℓ ^ ν * g`. Then there is a finite linear order `J` with a
monotone map `ty` (the exponent) to the `e` with `0 < e < t` such that for each `ν > 0` some
Taylor–Wiles places `Q` of level `ℓ ^ ν` indexed by `J` have their Frobenius data in `W` and satisfy
`IsPrimeTriangle` for `γ⁻¹` with bounds `b = y * h` and `c = y ^ 22 * h`. This says, with `τ j` the
chosen generator of tame inertia and `φ j` the Frobenius element at the `j`-th place:
* the `φ j` fix `μ_{ℓ^ν}` and the places are not above `ℓ`;
* there is a finite set `s` of test points of trivial `cyc` with `(#J + #s + 1) * b ≤ c`, such that
  a cocycle unramified off `ℓ` that vanishes at `γ⁻¹` and on `s` is zero, and for each exponent `e`
  and each point of `s` some `φ j` of exponent `e` is where the even classes unramified off `ℓ` take
  twice their value at that point;
* if an even class of exponent `ty j`, allowed to ramify at the places and their conjugates,
  vanishes at the earlier `τ i` and at the earlier `φ i` of the same exponent, then `ℓ ^ b` kills
  its value at `τ j`;
* `∏_{k ≠ e} (cyc γ ^ e - cyc γ ^ k)` and, for `e > 0`, `4 (cyc γ ^ e - 1) ^ 2` divide `ℓ ^ b`. -/
lemma New.Selmer.exists_isPrimeTriangle {ℓ : ℕ} {E : Type} [ThePrime ℓ] [Field E]
    [CMFieldWithRoot5040 E] (t : ℕ) {N y h : ℕ} {γ : Gal(Ω/E)} [NeZero N]
    (hE : ∀ x : E, algebraMap E Ω x ∈ cycloField N) (hN : N + t < y)
    (hγ_gen : (cyclotomicChar Ω ℓ).IsGeneratorModKer γ)
    (hγ_dvd : ∀ a ∈ Set.Ioo 0 t, (cyclotomicChar Ω ℓ γ ^ a).val - 1 ∣ ℓ ^ h)
    (hy : ℓ ≤ y ^ 2 ∨ h = 0) (h_inf_places : 4 ≤ Core.numInfPlaces E) {W : Set (FrobeniusDatum E)}
    (hW : ∀ (ν : ℕ) (g : Gal(Ω/E)), ∃ δ : Gal(Ω/E),
      cyclotomicChar Ω ℓ δ = 1 ∧ W ∈ mostFrobeniiAt E (δ ^ ℓ ^ ν * g)) :
    ∃ (J : Type) (_ : Fintype J) (_ : LinearOrder J) (ty : J →o {e : Fin t // 0 < e.val}),
      ∀ ν > (0 : ℕ), ∃ Q : TaylorWilesPlaces E J (ℓ ^ ν),
        IsPrimeTriangle ν Q.place (fun j : J ↦ (Q.frobData j).isPlaceOver.tameGenerator)
          (fun j : J ↦ (Q.frobData j).frob) γ⁻¹ t ty (y * h) (y ^ 22 * h) ∧
        ∀ j : J, Q.frobData j ∈ W := by
  -- `J` has one place for each exponent `0 < e < t` and each test point `i ∈ testPoints`. In the
  -- order of `J` choose a Kummer map and then a place, with `i` as test element. The test points
  -- have trivial cyclotomic character, and with `γ⁻¹` they detect the cocycles unramified off `ℓ`.
  obtain ⟨testPoints, h_ker, h_card, h_detect⟩ :=
    exists_detecting_points_mem_ker hE ℓ hγ_gen.inv
  have hty : t + 2 ≤ y := by grind [NeZero.pos N]
  -- `4` divides `cyc γ ^ e - 1`, which divides `ℓ ^ h`; so `4 (cyc γ ^ e - 1) ^ 2` divides
  -- `ℓ ^ (3 h)`.
  have h_four (e : {e : Fin t // 0 < e.val}) :
      (4 * ((cyclotomicChar Ω ℓ γ ^ e.val.val).val - 1) ^ 2 : ℤ_[ℓ]) ∣ ℓ ^ (3 * h) := by
    have he : (cyclotomicChar Ω ℓ γ ^ e.1.val).val - 1 ∣ ℓ ^ h := hγ_dvd _ ⟨e.2, e.1.isLt⟩
    have h_dvd : (2 ^ 2 : ℤ_[ℓ]) ∣ ℓ ^ h :=
      (four_dvd_cyclotomicChar_sub_one (γ ^ e.val.val)).trans (by simpa using he)
    calc (4 * ((cyclotomicChar Ω ℓ γ ^ e.val.val).val - 1) ^ 2 : ℤ_[ℓ])
        = 2 ^ 2 * ((cyclotomicChar Ω ℓ γ ^ e.val.val).val - 1) ^ 2 := by norm_num
      _ ∣ ℓ ^ h * (ℓ ^ h) ^ 2 := mul_dvd_mul h_dvd (pow_dvd_pow_of_dvd he 2)
      _ = ℓ ^ (3 * h) := by ring
  -- Well-order the test points, and order `J` lexicographically, first by the exponent.
  obtain ⟨points_order, points_wf⟩ := exists_wellFoundedLT testPoints
  let J : Type := {e : Fin t // 0 < e.val} ×ₗ testPoints
  let ty : J →o {e : Fin t // 0 < e.val} := ⟨fun j ↦ (ofLex j).1, Prod.Lex.monotone_fst⟩
  refine ⟨J, inferInstance, inferInstance, ty, fun ν hν ↦ ?_⟩
  let ty' : J → Fin t := fun j ↦ ty j
  let g' : J → Gal(Ω/E) := fun j ↦ (ofLex j).2
  obtain ⟨f, hf⟩ := TriangleEntry.exists_forall_mayFollow hν h_inf_places hty hγ_dvd (hW ν) ty'
    (g := g') (fun j ↦ h_ker _ (coe_mem _)) fun ⟨j⟩ ↦ dvd_of_mul_right_dvd (h_four (ty j))
  have h_apart : IsConjApart fun j : J ↦ (f j).frobeniusDatum.place :=
    isConjApart_of_injective_primeBelowPlus (TriangleEntry.primeBelowPlus_injective_of_mayFollow hf)
  refine ⟨⟨fun j ↦ (f j).frobeniusDatum, h_apart, fun j ↦
    (f j).isNuSplitPlace.prime_pow_dvd_q_sub_one⟩,
    { isTameGeneratorFamily := TriangleEntry.isTameGeneratorFamily f
      exists_test_points := ⟨testPoints, h_ker, ?_, fun O e ↦ h_detect, fun e i hi ↦ ?_⟩
      prod_dvd := fun e ↦ ?_
      pow_smul_eq_zero := fun O j z hz h_earlier ↦
        TriangleEntry.nsmul_tameGenerator_eq_zero_of_mayFollow hf hz (fun i hi ↦ (h_earlier i hi).1)
          fun i hi h_eq ↦ (h_earlier i hi).2 (Subtype.ext h_eq)
      four_mul_sq_dvd := fun O e ↦ ?_ }, fun j ↦ (hf j).mem⟩
  · -- There are at most `(t + 2) * y ^ 20 ≤ y ^ 21` places and points, each of cost `y * h`.
    obtain hℓy | rfl := hy
    · have h_one : testPoints.card + 1 ≤ 2 * y ^ 20 := by
        grind [h_card y (by omega) hℓy, Nat.one_le_pow 20 y (by omega)]
      grw [h_one, card_lex, card_prod, card_subtype_le, card_coe, h_card y (by omega) hℓy,
        Fintype.card_fin, ← add_mul, hty]
      exact le_of_eq (by ring)
    · simp
  · -- At the place of index `(e, i)` the even classes take twice their value at `i`.
    exact ⟨toLex (e, ⟨i, hi⟩), rfl, (hf (toLex (e, ⟨i, hi⟩))).even_apply⟩
  · simpa using mul_prod_pow_sub_pow_dvd hty hγ_dvd e (one_dvd _)
  · have h_int : (4 * ((cyclotomicChar Ω ℓ γ ^ (e : ℕ)).val - 1) ^ 2 : ℤ_[ℓ]) ∣ ℓ ^ (y * h) :=
      dvd_of_mul_right_dvd (mul_prod_pow_sub_pow_dvd hty hγ_dvd e.val (h_four e))
    simpa [cyclotomicInv, map_ofNat] using map_dvd (algebraMap _ O) h_int
