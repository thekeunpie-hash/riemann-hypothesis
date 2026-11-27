module

import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation
public import Lib.General.Algebra.SharpMinors
public import New.Congruences.Selmer.AuxiliaryPrimes
public import New.Congruences.Selmer.SelmerData
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import New.Congruences.Selmer.StickelbergerSystems
public import Lib.General.NumberTheory.GaussValuation
import Lib.General.NumberTheory.PadicLimitsValuation
public import Lib.ClassField.GaloisCohomology.TameSelmerCocycles
public import Lib.General.NumberTheory.CoefficientInclusion
public import Lib.General.Algebra.BlockFittingBound
import Lib.GaloisRep.Main.DivisibleSelmerModules
import New.Congruences.Selmer.Descent

section
/-!
# The universal twist and one system of equations for all twists

For homomorphisms `h_j : G → ℤ / q` let `ψ_X(g) = ∏ (1 + X_j) ^ (h_j g)`, and let `Sel(x)` be the
Selmer module of the twist of a representation by the value `ψ_x` at a point `x`. The members of all
`Sel(x)` are functions on one finite quotient of the Galois group, and the cocycle rule and the
other conditions are linear equations over `O[X]` for their values.

* `New.Selmer.universalChar`, `New.Selmer.IsTiedPrimes.universalChar_frob`,
  `New.Selmer.IsTiedPrimes.universalChar_tame_gen`: the polynomial `ψ_X` and its values at the
  auxiliary primes.
* `New.Selmer.exists_matrix_selmerAtPoint_equiv`: there is one matrix `A` over `O[X]` such that each
  `Sel(x)` is isomorphic to the kernel of `A(x)` on a power of `O' / ℓ ^ M`.
* `New.Selmer.exists_isLeast_length_selmerAtPoint`, `New.Selmer.exists_sharp_polynomial`: the
  valuations of a set of polynomials (in the proof, maximal minors) bound the lengths of `Sel(x)` at
  all points over discrete valuation rings of characteristic zero, and one is sharp at a given
  point.

Notions from other files:
* `New.selmerModule ρ S L B`: the locally constant cocycles for `ρ` with values in `B ^ n` that are
  unramified outside `S` and obey the relations `L`.
* `New.obeying`, `New.mapRel`: a relation is a finitely supported `f : Γ →₀ Matrix n n O`; a
  function `c` obeys it if `∑ γ, f γ • c γ = 0`, and `mapRel e f` applies `e` to all entries of `f`.
* `New.Selmer.IsTiedPrimes ℓ S₀ V W N P₀ J d`: a finite set `J` of primes that, with their
  conjugates, avoid `S₀`, and a first prime `P₀ ∈ J`. At `v ∈ J`, `(d v).1` holds a place, a
  Frobenius element `φ`, a tame generator `γ` and a character to `ℤ / ℓ ^ N`, and `(d v).2 i ∈ O` is
  the slope for the index `i : ι`. The Frobenius element of `P₀` lies in `W`, and where the slope
  for `i` is not zero, the condition `V i` holds at `φ` and at `(c φ c)⁻¹` for the complex
  conjugation `c`.
* `New.QuotSpan a`, `New.Selmer.reduceModPow ℓ M ρ`: the ring `O / a`, and `ρ` modulo `ℓ ^ M`.

## Relation to the literature

See `New.Congruences.Selmer.TwistingTheorem` for related work.
-/

@[expose] public section

noncomputable section

namespace New.Selmer

open IsDiscreteValuationRing Module MvPolynomial Matrix.Module

/-- A matrix over `O` acts on `(O / a) ^ n` as its reduction modulo `a` does; `QuotSpan a` is the
ring `O / a`. -/
lemma map_mk_smul {n O : Type} [Fintype n] [DecidableEq n] [CommRing O] {a : O}
    (A : Matrix n n O) (u : n → QuotSpan a) :
    A.map (Ideal.Quotient.mk (Ideal.span {a})) • u = A • u := by
  ext j
  simp [Algebra.smul_def]

section UniversalTwist

open Finset

variable {G R σ : Type} [Monoid G] [CommRing R] [Fintype σ] {q : ℕ}
  (h : σ → G →* Multiplicative (ZMod q))

/-- The polynomial `ψ_X(g) = ∏ (1 + X_j) ^ (h_j g)` attached to homomorphisms `h_j : G → ℤ / q`;
for `q ≠ 0` the exponents are taken in the interval `[0, q)`. -/
def universalChar (g : G) : MvPolynomial σ R :=
  ∏ j : σ, (1 + X j) ^ (h j g).toAdd.val

lemma aeval_universalChar {A : Type*} [CommRing A] [Algebra R A] (x : σ → A) (g : G) :
    aeval x (universalChar (R := R) h g) = ∏ j : σ, (1 + x j) ^ (h j g).toAdd.val := by
  simp [universalChar]

lemma eval_universalChar (x : σ → R) (g : G) :
    eval x (universalChar h g) = ∏ j : σ, (1 + x j) ^ (h j g).toAdd.val := by
  simp [universalChar]

/-- At the point `(ζ_j - 1)_j` for `q`-th roots of unity `ζ_j`, the polynomial
`universalChar h g = ∏ (1 + X_j) ^ (h_j g)` takes the value at `g` of the character
`pointChar h ζ hζ = ∏ ζ_j ^ h_j`. -/
lemma aeval_sub_one_universalChar [NeZero q] {A : Type} [CommRing A] [Algebra R A] {ζ : σ → A}
    (hζ : ∀ j : σ, ζ j ^ q = 1) (g : G) :
    aeval (fun j : σ ↦ ζ j - 1) (universalChar (R := R) h g) = pointChar h ζ hζ g := by
  simp [aeval_universalChar]

variable {ℓ : ℕ} [ThePrime ℓ] {E ι O : Type} [Field E]
  [EmbeddedNumberField E] [NumberField.IsCMField E] [CommRing O]
  {V : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)} {N : ℕ} {P₀ : FinPlace E}
  {S₀ J : Finset (FinPlace E)} {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}

open scoped Classical in
/-- Let `ℓ` be prime and `N ≠ 0`. Let `J` be a finite set of primes of the CM field `E` with data
`d` as in `IsTiedPrimes`: each `w ∈ J` carries an anticyclotomic character `h_w = (d w).1.character`
of `Gal(Ω/E)` to `ℤ / ℓ ^ N`. Let `ψ_X = ∏ (1 + X_w) ^ h_w` be the polynomial over a commutative
ring `R` in variables `X_w`, `w ∈ J`. If `h_v(g) = 1 ∈ ℤ / ℓ ^ N` and the other `h_w` vanish at `g`,
then `ψ_X` is `1 + X_v` at `idOrConjInv b g`, that is, at `g` and at `(c g c)⁻¹` for the complex
conjugation `c`. -/
lemma IsTiedPrimes.universalChar_eq_one_add_X (hJ : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0)
    {g : Gal(Ω/E)} (v : J)
    (hg : ∀ w ∈ J, (d w).1.character g = if w = v then Multiplicative.ofAdd 1 else 1) (b : Bool) :
    universalChar (R := R) (fun j : J ↦ (d j).1.character) (idOrConjInv b g) = 1 + X v := by
  have : Fact (1 < ℓ ^ N) := ⟨Nat.one_lt_pow hN (Fact.out : ℓ.Prime).one_lt⟩
  -- The characters are anticyclotomic, so they take the same value at `g` and at `(c g c)⁻¹`.
  have h_val (w : J) : (d w).1.character (idOrConjInv b g) = (d w).1.character g :=
    (hJ.isAuxPrimeDataAt w w.property).apply_idOrConjInv b g
  rw [universalChar, prod_eq_single_of_mem v (mem_univ v)]
  · simp [h_val, hg v v.property, ZMod.val_one]
  · intro w _ hw
    simp [h_val, hg w w.property, Subtype.coe_ne_coe.2 hw]

/-- Let `ℓ` be prime and `N ≠ 0`. Let `J` be a finite set of primes of the CM field `E` with data
`d` as in `IsTiedPrimes`: each `w ∈ J` carries an anticyclotomic character
`h_w = (d w).1.character` to `ℤ / ℓ ^ N`, and at the Frobenius element `φ = (d v).1.frob` of a prime
`v ∈ J` other than the distinguished prime `P₀ ∈ J`, the character `h_{P₀}` is `1` and the other
`h_w` vanish; `S₀`, `V`, `W` and the slopes play no part. Then at `φ` and at `(c φ c)⁻¹` for the
complex conjugation `c`, the two values of `idOrConjInv b φ`, the polynomial
`ψ_X = ∏ (1 + X_w) ^ h_w` over `R` in variables `X_w`, `w ∈ J`, is `1 + X_{P₀}`. -/
lemma IsTiedPrimes.universalChar_frob (hJ : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0)
    {v : FinPlace E} (hv : v ∈ J) (hv_ne : v ≠ P₀) (b : Bool) :
    universalChar (R := R) (fun j : J ↦ (d j).1.character) (idOrConjInv b (d v).1.frob) =
      1 + X ⟨P₀, hJ.first_mem⟩ :=
  hJ.universalChar_eq_one_add_X hN ⟨P₀, hJ.first_mem⟩ (hJ.char_frob_eq_ite v hv hv_ne) b

/-- Let `ℓ` be prime and `N ≠ 0`. Let `J` be a finite set of primes of the CM field `E` with data
`d` as in `IsTiedPrimes`: each `w ∈ J` carries an anticyclotomic character
`h_w = (d w).1.character` to `ℤ / ℓ ^ N` and a tame generator of inertia; `P₀`, `S₀`, `V`, `W` and
the slopes do not enter the claim. Let `γ = (d v).1.tameGenerator` be the tame generator at a prime
`v` of `J`. At `γ` and at `(c γ c)⁻¹` for the complex conjugation `c`, the two values of
`idOrConjInv b γ`, the polynomial `ψ_X = ∏ (1 + X_w) ^ h_w` over `R` in variables `X_w`, `w ∈ J`, is
`1 + X_v`. -/
lemma IsTiedPrimes.universalChar_tame_gen (hJ : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0)
    (v : J) (b : Bool) :
    universalChar (R := R) (fun j : J ↦ (d j).1.character) (idOrConjInv b (d v).1.tameGenerator) =
      1 + X v :=
  hJ.universalChar_eq_one_add_X hN v (hJ.character_tameGenerator_eq_ite v.property) b

end UniversalTwist

section Relations

variable {Γ 𝒢 n Λ O B : Type} [Fintype 𝒢] [Fintype n] [DecidableEq n] [CommRing Λ] [CommRing O]
  [AddCommGroup B] [Module O B]

lemma mapRel_single (ev : Λ →+* O) (g : Γ) (m : Matrix n n Λ) :
    mapRel ev (.single g m) = .single g (m.map ev) := Finsupp.mapRange_single

/-- Mapping the entries of a relation by `e` and then by `ev` is mapping them by `ev ∘ e`. -/
lemma mapRel_mapRel {Λ' : Type} [CommRing Λ'] (e : Λ' →+* Λ) (ev : Λ →+* O)
    (f : Γ →₀ Matrix n n Λ') : mapRel ev (mapRel e f) = mapRel (ev.comp e) f :=
  Finsupp.ext fun _ ↦ Matrix.map_map

/-- Applying `ev` to all matrix entries carries the relations that express the cocycle identity for
`ρ` onto those that express it for `g ↦ ev (ρ g)`. -/
lemma mapRel_image_cocycleRelations [Mul Γ] (ev : Λ →+* O) (ρ : Γ → Matrix n n Λ) :
    mapRel ev '' cocycleRelations ρ = cocycleRelations fun g : Γ ↦ (ρ g).map ev := by
  have h_rel (g g' : Γ) : mapRel ev (.single (g * g') 1 - .single g 1 - .single g' (ρ g)) =
      .single (g * g') 1 - .single g 1 - .single g' ((ρ g).map ev) := by
    simp [mapRel, Finsupp.mapRange_sub']
  simp only [Set.ext_iff, Set.mem_image, cocycleRelations, Set.mem_ofPred_eq]
  aesop

/-- The linear equations that a set `R` of relations imposes on the functions on `Γ` that factor
through `π : Γ → 𝒢`. The unknowns are the coordinates of the values on `𝒢`, and there is one
equation for each relation and each coordinate. -/
def relationMatrix (π : Γ → 𝒢) (R : Set (Γ →₀ Matrix n n Λ)) : Matrix (R × n) (𝒢 × n) Λ :=
  .of fun (f, i) (c, j) ↦ f.val.mapDomain π c i j

lemma relationMatrix_apply {Γ 𝒢 n Λ : Type} [CommRing Λ] (π : Γ → 𝒢)
    (R : Set (Γ →₀ Matrix n n Λ)) (f : R) (i : n) (c : 𝒢 × n) :
    relationMatrix π R (f, i) c = (f : Γ →₀ Matrix n n Λ).mapDomain π c.1 i c.2 := rfl

/-- For `π : Γ → 𝒢`, let `f.mapDomain π` be `f` pushed forward along `π`, adding the matrices over
each fibre. Then `∑ c, ev (f.mapDomain π c.1 i c.2) • w c` is coordinate `i` of
`relEval B (mapRel ev f)` applied to `g ↦ w (π g, ·)`, that is, of `∑ g, ev (f g) • w (π g, ·)`. -/
lemma sum_mapDomain_smul_eq_relEval (π : Γ → 𝒢) (ev : Λ →+* O) (w : 𝒢 × n → B)
    (f : Γ →₀ Matrix n n Λ) (i : n) :
    ∑ c : 𝒢 × n, ev (f.mapDomain π c.1 i c.2) • w c =
      relEval B (mapRel ev f) (fun (g : Γ) (j : n) ↦ w (π g, j)) i := by
  induction f using Finsupp.induction_linear with
  | zero => simp [mapRel]
  | add f f' hf hf' =>
    simp [mapRel, Finsupp.mapRange_add', Finsupp.mapDomain_add, add_smul,
      Finset.sum_add_distrib, hf, hf']
  | single g m =>
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (π g)]
    · simp [mapRel]
    · simp +contextual
    · simp

/-- A vector `w` solves the linear system `relationMatrix π R`, with entries mapped by `ev`, if and
only if the function `g ↦ w (π g, ·)` obeys the relations of `R` mapped by `ev`. -/
lemma mem_matrixKernel_relationMatrix (π : Γ → 𝒢) (R : Set (Γ →₀ Matrix n n Λ)) (ev : Λ →+* O)
    (w : 𝒢 × n → B) :
    w ∈ matrixKernel ((relationMatrix π R).map ev) B ↔
      (fun (g : Γ) (i : n) ↦ w (π g, i)) ∈ obeying (mapRel ev '' R) B := by
  simp only [mem_matrixKernel, mem_obeying, Set.forall_mem_image, Prod.forall, Subtype.forall,
    funext_iff, ← sum_mapDomain_smul_eq_relEval, Matrix.map_apply, relationMatrix_apply,
    Pi.zero_apply]

end Relations

variable {E G n σ Λ O O' : Type} [Field E] [EmbeddedNumberField E] [Monoid G] [Fintype n]
  [DecidableEq n] [Fintype σ] [CommRing Λ] [CommRing O] [CommRing O'] {q : ℕ} {S : Set (FinPlace E)}

/-- Let `B` be an abelian group killed by `m ≠ 0`. An element of `B` that is killed by every
homomorphism `B → ℤ / m` is zero. -/
lemma eq_zero_of_forall_hom_zmod_eq_zero {B : Type} [AddCommGroup B] {m : ℕ} [NeZero m]
    (hm : ∀ b : B, m • b = 0) {b : B} (hb : ∀ χ : B →+ ZMod m, χ b = 0) : b = 0 := by
  refine QZ.eq_zero_of_forall_hom_eq_zero fun u ↦ ?_
  obtain ⟨χ, rfl⟩ := (QZ.bijective_ofZMod_comp hm).surjective u
  simp [hb]

/-- Finitely many locally constant functions on an open subgroup `G'` of `Gal(Ω/E)` are all constant
on some open normal subgroup `G''` of `Gal(Ω/E)` that is contained in `G'`. -/
lemma exists_openNormalSubgroup_forall_apply_eq_apply_one (G' : OpenSubgroup Gal(Ω/E)) {V : Type}
    {Y : Set (G'.toSubgroup → V)} (hY : Y.Finite) (hY_const : ∀ y ∈ Y, IsLocallyConstant y) :
    ∃ G'' : OpenNormalSubgroup Gal(Ω/E),
      ∀ g ∈ G'', ∃ hg : g ∈ G'.toSubgroup, ∀ y ∈ Y, y ⟨g, hg⟩ = y 1 := by
  have h_nhds : {u : G'.toSubgroup | ∀ y ∈ Y, y u = y 1} ∈ nhds 1 :=
    hY.eventually_all.2 fun y hy ↦ (hY_const y hy).eventually_eq 1
  obtain ⟨W, hW_sub, hW_open, hW_one⟩ :=
    mem_nhds_iff.1 (G'.isOpen.isOpenMap_subtypeVal.image_mem_nhds h_nhds)
  obtain ⟨G'', hG''⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW_open hW_one
  refine ⟨G'', fun g hg ↦ ?_⟩
  obtain ⟨u, hu, rfl⟩ := hW_sub (hG'' hg)
  exact ⟨u.property, hu⟩

/-- Let `G'` be an open subgroup of `Gal(Ω/E)`, let `m ≠ 0` and let `S` be a finite set of primes of
the number field `E`. There is one open normal subgroup `G''` such that, for every abelian group `B`
killed by `m`, each locally constant `z : Gal(Ω/E) → B` that is additive on `G'` and vanishes on
`inertiaAbove Sᶜ`, the union of the inertia groups above the primes outside `S`, vanishes on
`G''`. -/
lemma exists_openNormalSubgroup_forall_eq_zero (G' : OpenSubgroup Gal(Ω/E)) (m : ℕ) [NeZero m]
    (hS : S.Finite) :
    ∃ G'' : OpenNormalSubgroup Gal(Ω/E),
      ∀ (B : Type) [AddCommGroup B], (∀ b : B, m • b = 0) → ∀ z : Gal(Ω/E) → B,
        IsLocallyConstant z →
        (∀ g ∈ G', ∀ g' ∈ G', z (g * g') = z g + z g') →
        (∀ g ∈ inertiaAbove Sᶜ, z g = 0) →
        ∀ g ∈ G'', z g = 0 := by
  -- The continuous homomorphisms `G' → ℤ / m` that are unramified outside the primes above `S`
  -- form a finite set `Y`.
  let : TopologicalSpace (ZMod m) := ⊥
  have : DiscreteTopology (ZMod m) := ⟨rfl⟩
  let H : Subgroup Gal(Ω/E) := G'.toSubgroup
  let V : DiscreteModule ℤ H := .of (.trivial ℤ H (ZMod m))
  let S' : Set (FinPlace (fixedFieldOf H)) := FinPlace.below E ⁻¹' S
  have hS' : S'.Finite := by
    simpa [S'] using
      tendsto_place_comap_cofinite (algebraMap E (fixedFieldOf H)) hS.compl_mem_cofinite
  let Y : Set (H → V) := {y ∈ Z1 V.ρ | ∀ w ∉ S', ∀ A : ClosurePlace, IsPlaceOver A w →
    ∀ g ∈ inertiaGroup H A, y g = 0}
  -- So they are all constant on an open normal subgroup `G''` of `Gal(Ω/E)`.
  obtain ⟨G'', hG''⟩ := exists_openNormalSubgroup_forall_apply_eq_apply_one G'
    (finite_cocycles_unramified_outside V hS' : Y.Finite)
    fun y ⟨⟨hy_cont, _⟩, _⟩ ↦ (IsLocallyConstant.iff_continuous y).2 hy_cont
  refine ⟨G'', fun B _ hm z hz_const hz_add hz_unr g hg ↦ ?_⟩
  have hz_one : z 1 = 0 := by simpa using hz_add 1 (one_mem G') 1 (one_mem G')
  -- The homomorphisms `χ : B → ℤ / m` separate the points of `B`, and `χ ∘ z` lies in `Y`.
  refine eq_zero_of_forall_hom_zmod_eq_zero hm fun χ ↦ ?_
  have h_cocycle : (fun u : H ↦ χ (z u)) ∈ Z1 V.ρ := by
    refine ⟨(hz_const.comp χ).continuous.comp continuous_subtypeVal, fun u u' ↦ ?_⟩
    simp [V, hz_add u u.property u' u'.property]
  have h_mem : (fun u : H ↦ χ (z u)) ∈ Y := by
    refine ⟨h_cocycle, fun w hw A hA u hu ↦ ?_⟩
    simp [hz_unr u ⟨w.below E, hw, A, hA.isPlaceOver_below, hu⟩]
  obtain ⟨hg_mem, h_const⟩ : ∃ hg : g ∈ H, ∀ y ∈ Y, y ⟨g, hg⟩ = y 1 := hG'' g hg
  simpa only [Subgroup.coe_one, hz_one, map_zero] using h_const _ h_mem

/-- Let `ρ` be a function from `Gal(Ω/E)` to matrices over a ring `Λ`, let `L` be a set of relations
`∑ γ, f γ • c γ = 0` with matrix coefficients over `Λ`, let `G'` be an open subgroup, let `m ≠ 0`
and let `S` be a finite set of primes of `E`. There is one matrix `A` over `Λ`, with columns indexed
by a finite type `k`, such that for every `ev : Λ → O'` and every `O'`-module `B` killed by `m`, if
`G'` acts trivially on `B ^ n` through `ev ρ`, the Selmer module of `ev ρ` in `B ^ n` is isomorphic
to the kernel of `ev A` on `B ^ k`. -/
theorem exists_matrix_selmerModule_equiv (ρ : Gal(Ω/E) → Matrix n n Λ)
    (G' : OpenSubgroup Gal(Ω/E)) (m : ℕ) [NeZero m] (hS : S.Finite)
    (L : Set (Gal(Ω/E) →₀ Matrix n n Λ)) :
    ∃ (r k : Type) (_ : Fintype k) (A : Matrix r k Λ),
      ∀ (O' : Type) [CommRing O'] (ev : Λ →+* O') (B : Type) [AddCommGroup B] [Module O' B],
        (∀ b : B, m • b = 0) →
        (∀ g ∈ G', ∀ b : n → B, (ρ g).map ev • b = b) →
        Nonempty (selmerModule (fun g : Gal(Ω/E) ↦ (ρ g).map ev) S (mapRel ev '' L) B ≃ₗ[O']
          matrixKernel (A.map ev) B) := by
  -- The cocycles factor through one finite quotient `𝒢` of `Gal(Ω/E)`, and `A` is the matrix of
  -- the equations that define the Selmer module among the functions on `𝒢`.
  obtain ⟨G'', h_zero⟩ := exists_openNormalSubgroup_forall_eq_zero G' m hS
  let H : Subgroup Gal(Ω/E) := G''.toSubgroup
  let 𝒢 : Type := Gal(Ω/E) ⧸ H
  let : Fintype 𝒢 := .ofFinite 𝒢
  let π : Gal(Ω/E) → 𝒢 := QuotientGroup.mk
  -- The equations: the cocycle rule, vanishing on inertia outside `S`, and the relations `L`.
  let R : Set (Gal(Ω/E) →₀ Matrix n n Λ) :=
    cocycleRelations ρ ∪ (fun g ↦ Finsupp.single g 1) '' inertiaAbove Sᶜ ∪ L
  refine ⟨R × n, 𝒢 × n, inferInstance, relationMatrix π R, fun O' _ ev B _ _ hm h_triv ↦ ?_⟩
  let Sel := selmerModule (fun g ↦ (ρ g).map ev) S (mapRel ev '' L) B
  let Ker : Submodule O' (𝒢 × n → B) := matrixKernel ((relationMatrix π R).map ev) B
  -- The members of `Sel` are additive on `G'`, so they vanish on `G''` and are functions on `𝒢`.
  have h_inv (z : Gal(Ω/E) → n → B) (hz : z ∈ Sel) (g : Gal(Ω/E)) (g'' : H) :
      z (g * g'') = z g := by
    obtain ⟨h_cocycle, h_unr, -, h_const⟩ := mem_selmerModule_iff.1 hz
    have h_add : ∀ u ∈ G', ∀ u' ∈ G', z (u * u') = z u + z u' :=
      fun u hu u' _ ↦ by rw [h_cocycle, h_triv u hu]
    have h_vanish : z g'' = 0 :=
      h_zero (n → B) (fun b ↦ funext fun i ↦ hm (b i)) z h_const h_add h_unr g'' g''.property
    rw [h_cocycle, h_vanish, smul_zero, add_zero]
  -- A function on `𝒢` is a vector `w` with coordinates in `B`; it gives a member of `Sel` if and
  -- only if it satisfies the equations.
  let pull : (𝒢 × n → B) →ₗ[O'] Gal(Ω/E) → n → B := .pi fun g ↦ .pi fun i ↦ .proj (π g, i)
  have h_rel : mapRel ev '' R = cocycleRelations (fun g ↦ (ρ g).map ev) ∪
      (fun g ↦ Finsupp.single g 1) '' inertiaAbove Sᶜ ∪ mapRel ev '' L := by
    simp [R, Set.image_union, mapRel_image_cocycleRelations, Set.image_image, mapRel_single]
  have h_mem (w : 𝒢 × n → B) : w ∈ Ker ↔ pull w ∈ Sel := by
    have h_const : IsLocallyConstant (pull w) :=
      (IsLocallyConstant.of_discrete w.curry).comp_continuous QuotientGroup.continuous_mk
    have h_Sel : pull w ∈ Sel ↔
        pull w ∈ obeying (mapRel ev '' R) B ∧ IsLocallyConstant (pull w) := by
      rw [h_rel]
      exact Submodule.mem_inf
    rw [h_Sel, and_iff_left h_const]
    exact mem_matrixKernel_relationMatrix π R ev w
  have h_inj : Function.Injective pull := fun w w' h_eq ↦ funext fun (c, i) ↦ by
    obtain ⟨g, rfl⟩ : ∃ g : Gal(Ω/E), π g = c := QuotientGroup.mk_surjective c
    exact congr_fun₂ h_eq g i
  have h_map : Ker.map pull = Sel := by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun w hw ↦ (h_mem w).1 hw) fun z hz ↦ ?_
    have h_pull : pull (fun (c, i) ↦ z c.out i) = z := by
      funext g
      obtain ⟨g'', hg''⟩ : ∃ g'' : H, (π g).out = g * g'' := QuotientGroup.mk_out_eq_mul H g
      change z (π g).out = z g
      rw [hg'', h_inv z hz]
    exact ⟨_, (h_mem _).2 (by rwa [h_pull]), h_pull⟩
  exact ⟨((Submodule.equivMapOfInjective pull h_inj Ker).trans (.ofEq _ Sel h_map)).symm⟩

/-- The matrices `ψ_x(g) ρ(g)` over `O'`, where `ψ_x(g)` is the value of
`ψ_X(g) = universalChar h g` at the point `x` and `ρ(g)` is mapped by `e`. The function `ψ_x` need
not be multiplicative. -/
def pointTwist (h : σ → G →* Multiplicative (ZMod q)) (x : σ → O') (e : O →+* O')
    (ρ : G → Matrix n n O) (g : G) : Matrix n n O' :=
  eval x (universalChar h g) • (ρ g).map e

/-- Let `h j : G → ℤ / q` be finitely many homomorphisms, `ρ` a representation of `G` by matrices
over `O`, `e : O → O'` a ring homomorphism and `x` a point with coordinates `x j ∈ O'`. If all
`h j` vanish at `g` and `ρ g` is the identity modulo `ℓ ^ M`, then the twisted matrix
`pointTwist h x e ρ g = (∏ (1 + x_j) ^ (h_j g)) • e (ρ g)` acts trivially on `(O' / ℓ ^ M) ^ n`. -/
lemma pointTwist_smul_eq_self {ℓ M : ℕ} {h : σ → G →* Multiplicative (ZMod q)}
    {ρ : G →* Matrix n n O} {g : G} (hg_char : ∀ j : σ, h j g = 1)
    (hg_red : reduceModPow ℓ M ρ g = 1) (x : σ → O') (e : O →+* O')
    (b : n → QuotSpan (ℓ ^ M : O')) : pointTwist h x e ρ g • b = b := by
  have h_char : eval x (universalChar h g) = 1 := by simp [eval_universalChar, hg_char]
  -- The reduction of `e (ρ g)` is the image of that of `ρ g` under `O / ℓ ^ M → O' / ℓ ^ M`.
  let ē : QuotSpan (ℓ ^ M : O) →+* QuotSpan (ℓ ^ M : O') := Ideal.quotientMap _ e (by simp)
  have h_red : ((ρ g).map e).map (Ideal.Quotient.mk (.span {(ℓ ^ M : O')})) =
      (reduceModPow ℓ M ρ g).map ē := by
    ext i j
    simp [ē, reduceModPow]
  rw [pointTwist, h_char, one_smul, ← map_mk_smul, h_red, hg_red,
    Matrix.map_one ē ē.map_zero ē.map_one, one_smul]

/-- The module `Sel(x)`: the locally constant cocycles in `(O' / ℓ ^ M) ^ n` for the twist
`pointTwist h x e ρ` of `ρ` by `ψ_x` that are unramified outside `S` and obey the relations `L`,
with coefficients mapped by `e`. -/
def selmerAtPoint (ℓ M : ℕ) (h : σ → Gal(Ω/E) →* Multiplicative (ZMod q))
    (ρ : Gal(Ω/E) → Matrix n n O) (S : Set (FinPlace E)) (L : Set (Gal(Ω/E) →₀ Matrix n n O))
    (e : O →+* O') (x : σ → O') : Submodule O' (Gal(Ω/E) → n → QuotSpan (ℓ ^ M : O')) :=
  selmerModule (pointTwist h x e ρ) S (mapRel e '' L) (QuotSpan (ℓ ^ M : O'))

variable {ℓ M : ℕ} [NeZero ℓ] {h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)}
  {ρ : Gal(Ω/E) →* Matrix n n O}

/-- Let `ℓ ≠ 0` and `q` be natural numbers, let `h j : Gal(Ω/E) → ℤ / q` be finitely many locally
constant homomorphisms, and let `ρ` be a representation of `Gal(Ω/E)` by matrices over `O` that is
locally constant modulo `ℓ ^ M`. Let `S` be a finite set of finite places of `E`. There is a matrix
`A` over `MvPolynomial σ O`, with finitely many columns and possibly infinitely many rows, such that
`Sel(x)` is isomorphic to the kernel of `A` evaluated at `x` on a power of `O' / ℓ ^ M`. This holds
for all `e : O → O'` and all points `x : σ → O'`. -/
theorem exists_matrix_selmerAtPoint_equiv (h_char_const : ∀ j : σ, IsLocallyConstant (h j))
    (hρ : IsLocallyConstant (reduceModPow ℓ M ρ)) (hS : S.Finite)
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
    ∃ (r k : Type) (_ : Fintype k) (A : Matrix r k (MvPolynomial σ O)),
      ∀ (O' : Type) [CommRing O'] (e : O →+* O') (x : σ → O'),
        Nonempty (selmerAtPoint ℓ M h ρ S L e x ≃ₗ[O']
          matrixKernel (A.map (eval₂Hom e x)) (QuotSpan (ℓ ^ M : O'))) := by
  -- On the open subgroup `G'` the characters `h j` are trivial, and so is `ρ` modulo `ℓ ^ M`.
  let G' : OpenSubgroup Gal(Ω/E) := ⟨(⨅ j : σ, (h j).ker) ⊓ (reduceModPow ℓ M ρ).ker, by
    change IsOpen (((⨅ j : σ, (h j).ker : Subgroup Gal(Ω/E)) : Set Gal(Ω/E)) ∩ _)
    rw [Subgroup.coe_iInf]
    exact (isOpen_iInter_of_finite fun j ↦ (h_char_const j).isOpen_fiber 1).inter
      (hρ.isOpen_fiber 1)⟩
  let ρX (g : Gal(Ω/E)) : Matrix n n (MvPolynomial σ O) := universalChar (R := O) h g • (ρ g).map C
  obtain ⟨r, k, _, A, hA⟩ := exists_matrix_selmerModule_equiv ρX G' (ℓ ^ M) hS (mapRel C '' L)
  refine ⟨r, k, inferInstance, A, fun O' _ e x ↦ ?_⟩
  -- At `X = x` the matrices `ρX g` and the relations are those of `Sel(x)`.
  have h_twist (g : Gal(Ω/E)) : (ρX g).map (eval₂Hom e x) = pointTwist h x e ρ g := by
    ext i j
    simp [ρX, pointTwist, universalChar]
  rw [selmerAtPoint, ← funext h_twist,
    show mapRel e '' L = mapRel (eval₂Hom e x) '' (mapRel C '' L) by
      simp [Set.image_image, mapRel_mapRel]]
  refine hA O' (eval₂Hom e x) (QuotSpan (ℓ ^ M : O')) (nsmul_quot_eq_zero dvd_rfl) fun g hg b ↦ ?_
  obtain ⟨hg_char, hg_red⟩ := Subgroup.mem_inf.1 hg
  rw [h_twist, pointTwist_smul_eq_self (Subgroup.mem_iInf.1 hg_char) (MonoidHom.mem_ker.1 hg_red)]

/-- Let `ℓ ≠ 0`, let the homomorphisms `h j : Gal(Ω/E) → ℤ / q` and the representation `ρ` over `O`,
taken modulo `ℓ ^ M`, be locally constant, let `S` be a finite set of primes of `E` and let `L` be
any set of relations `∑ γ, f γ • c γ = 0` on cocycles `c`. There is a set `𝓜` of polynomials over
`O` such that, at every point `x` over a discrete valuation ring `O'` of characteristic zero, the
length of `Sel(x)` is the least valuation of a value `P(x)`, `P ∈ 𝓜`. -/
theorem exists_isLeast_length_selmerAtPoint (h_char_const : ∀ j : σ, IsLocallyConstant (h j))
    (hρ : IsLocallyConstant (reduceModPow ℓ M ρ)) (hS : S.Finite)
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
    ∃ 𝓜 : Set (MvPolynomial σ O),
      ∀ (O' : Type) [CommRing O'] [DVR O'] [CharZero O'] (e : O →+* O') (x : σ → O'),
        IsLeast ((fun P : MvPolynomial σ O ↦ addVal O' (eval₂ e x P)) '' 𝓜)
          (length O' (selmerAtPoint ℓ M h ρ S L e x)) := by
  classical
  obtain ⟨r, k, _, A, hA⟩ := exists_matrix_selmerAtPoint_equiv h_char_const hρ hS L
  refine ⟨maximalMinors A (ℓ ^ M), fun O' _ _ _ e x ↦ ?_⟩
  obtain ⟨φ⟩ := hA O' e x
  rw [φ.length_eq, ← show eval₂Hom e x (ℓ ^ M : MvPolynomial σ O) = ℓ ^ M by simp]
  exact isLeast_length_matrixKernel A (ℓ ^ M) (eval₂Hom e x) (by simp [NeZero.ne])

/-- Let `ℓ ≠ 0`, let the homomorphisms `h j : Gal(Ω/E) → ℤ / q` and the representation `ρ` over `O`,
taken modulo `ℓ ^ M`, be locally constant, let `S` be a finite set of primes of `E` and let `L` be
any set of relations `∑ γ, f γ • c γ = 0` on cocycles `c`. Let `x₀` be a point over a discrete
valuation ring `O₀` of characteristic zero, with `e₀ : O → O₀`. There is a polynomial `P` over `O`
such that the valuation of `P(x₀)` is the length of `Sel(x₀)`, and the valuation of `P(x)` is at
least the length of `Sel(x)` at every point `x` over a ring of the same kind. -/
theorem exists_sharp_polynomial (h_char_const : ∀ j : σ, IsLocallyConstant (h j))
    (hρ : IsLocallyConstant (reduceModPow ℓ M ρ)) (hS : S.Finite)
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) {O₀ : Type} [CommRing O₀] [DVR O₀] [CharZero O₀]
    (e₀ : O →+* O₀) (x₀ : σ → O₀) :
    ∃ P : MvPolynomial σ O,
      addVal O₀ (eval₂ e₀ x₀ P) = length O₀ (selmerAtPoint ℓ M h ρ S L e₀ x₀) ∧
      ∀ (O' : Type) [CommRing O'] [DVR O'] [CharZero O'] (e : O →+* O') (x : σ → O'),
        length O' (selmerAtPoint ℓ M h ρ S L e x) ≤ addVal O' (eval₂ e x P) := by
  obtain ⟨𝓜, h_least⟩ := exists_isLeast_length_selmerAtPoint h_char_const hρ hS L
  obtain ⟨P, hP, h_sharp⟩ := (h_least O₀ e₀ x₀).1
  exact ⟨P, h_sharp, fun O' _ _ _ e x ↦ (h_least O' e x).2 (Set.mem_image_of_mem _ hP)⟩

end New.Selmer

end
end
end

section
/-!
# Stickelberger systems on a line

Let `P = ψ_X(Θ_J)` be the value of the polynomial character `ψ_X = ∏_j (1 + X_j) ^ h_j` at the
element `Θ_J` of a Stickelberger system, where `J` is a set of tied auxiliary primes, the first
prime `P₀` included. On the line on which all variables but the one of `P₀` vanish, `P` is a
polynomial `P(X, 0)` in one variable. Up to a power of `1 + X` it is congruent to `R₀ R₁` modulo
`(1 + X) ^ ℓ ^ N - 1`. Here `R₀` comes from the element for `{P₀}` and has `v(R₀(0)) ≤ β` if
`ϑ(φ_{P₀})` is close enough to `ϑ(g₀)` and `N` is large, and `R₁` comes from the Euler factors at
the other primes and has small Gauss valuation. If `ρ ≤ 1` and `v_ρ(R₀ R₁) < N ρ`, the congruence
bounds the valuation of `P` at a point where `R₀ R₁` attains its Gauss valuation.

* `New.Selmer.StickelbergerSystem.exists_congruence_lineChar_element`: the congruence.
* `New.Selmer.StickelbergerSystem.exists_point_ellVal_universalChar_le`: an upper bound for the
  valuation of `P` at some point whose coordinates have valuation at least `ρ`.

Notions from other files:
* `New.Selmer.StickelbergerSystem`: elements `Θ_Q` of the group rings of class groups `Cl_Q` with a
  norm relation, a character `ϑ`, a list of integers `e`, and the number `β`.
* `New.Selmer.IsTiedPrimes`: an auxiliary set `J` of primes with places, Frobenius elements `φ`,
  tame generators `γ`, characters `h` to `ℤ / ℓ ^ N` and slopes, and a first prime `P₀ ∈ J`; for
  primes `v, w ≠ P₀` of `J` one has `h_{P₀}(φ_v) = 1` and `h_w(φ_v) = 0`.
* `New.Selmer.groupRingEval`: the value of a function on `Gal(Ω/E)`, read on `Cl_Q` and extended
  linearly, at an element of the group ring of `Cl_Q`.
* `New.ellVal`: the valuation `v` of `ℚ̄_ℓ` with `v(ℓ) = 1`, cut off at `0` from below;
  `New.intQpBar` is its valuation ring.
* `New.Selmer.gaussVal`: the Gauss valuation `v_ρ(g) = min_i (v(y_i) + ρ i)` of `g = ∑ y_i Y ^ i`.
-/

@[expose] public section

noncomputable section

namespace New.Selmer

open Finset Filter Polynomial

open scoped NNReal ENNReal NNRat

/-- Let `E` be a CM number field embedded in the algebraic closure `Ω` of `ℚ`, let `ζ_j` be `q`-th
roots of unity in `R`, and `h_j` characters of `Gal(Ω/E)` to `ℤ / q`. If each `h_j` with `ζ_j ≠ 1`
comes from the norm-one torus with modulus `I` and is trivial at `S`, then so does the character
`g ↦ ∏ ζ_j ^ h_j(g)` (`pointChar`). -/
lemma isFromU1_pointChar {E σ R : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
    [CommRing R] [Fintype σ] {q : ℕ} [NeZero q] {S I : Set (FinPlace E)}
    {h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)} {ζ : σ → R} (hζ : ∀ j : σ, ζ j ^ q = 1)
    (h_fromU1 : ∀ j : σ, ζ j ≠ 1 → IsFromU1 S I (h j)) : IsFromU1 S I (pointChar h ζ hζ) := by
  let factor (j : σ) : Gal(Ω/E) →* R := (AddChar.zmodChar q (hζ j)).toMonoidHom.comp (h j)
  have h_prod : pointChar h ζ hζ = ∏ j : σ, factor j :=
    MonoidHom.ext fun g ↦ by simp [factor, AddChar.zmodChar_apply]
  rw [h_prod]
  refine prod_induction factor _ (fun _ _ ↦ IsFromU1.mul) IsFromU1.one fun j _ ↦ ?_
  by_cases hj : ζ j = 1
  · rw [show factor j = 1 from MonoidHom.ext fun g ↦ by simp [factor, AddChar.zmodChar_apply, hj]]
    exact IsFromU1.one
  · exact (h_fromU1 j hj).map _

/-- Let `E` be a CM number field embedded in the algebraic closure `Ω` of `ℚ`, let `h_j` be
characters of `Gal(Ω/E)` to `ℤ / q`, and `ζ_j` `q`-th roots of unity in the valuation ring of
`ℚ̄_ℓ`. Let `a` be in the group ring over that valuation ring of `Cl_Q = U1ClassGroup Q`, the finite
ideles `u` with `u ū = 1` modulo those in `Eˣ` and the units that are `≡ 1` at the primes in `Q`.
Then the value of `ψ_X = ∏ (1 + X_j) ^ h_j` (`universalChar`) on `a`, at the point `(ζ_j - 1)_j`, is
the value of the character `∏ ζ_j ^ h_j` (`pointChar`) on `a`. -/
lemma coe_eval_groupRingEval_universalChar {ℓ : ℕ} [ThePrime ℓ] {E σ : Type} [Field E]
    [EmbeddedNumberField E] [NumberField.IsCMField E] [Fintype σ] {q : ℕ} [NeZero q]
    (h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)) {ζ : σ → intQpBar ℓ}
    (hζ : ∀ j : σ, (ζ j : PadicAlgCl ℓ) ^ q = 1) {Q : Finset (FinPlace E)}
    (a : MonoidAlgebra (intQpBar ℓ) (U1ClassGroup Q)) :
    ((MvPolynomial.eval (fun j : σ ↦ ζ j - 1) (groupRingEval (universalChar h) a) : intQpBar ℓ) :
        PadicAlgCl ℓ) =
      groupRingEval (pointChar h (fun j : σ ↦ (ζ j : PadicAlgCl ℓ)) hζ) a := by
  let L : MvPolynomial σ (intQpBar ℓ) →ₐ[intQpBar ℓ] PadicAlgCl ℓ :=
    MvPolynomial.aeval fun j ↦ (ζ j : PadicAlgCl ℓ) - 1
  have hL (P : MvPolynomial σ (intQpBar ℓ)) :
      (MvPolynomial.eval (fun j ↦ ζ j - 1) P : intQpBar ℓ) = L P :=
    (MvPolynomial.aeval_algebraMap_apply (PadicAlgCl ℓ) (fun j ↦ ζ j - 1) P).symm
  have h_char : (fun g ↦ L (universalChar h g)) = pointChar h (fun j ↦ (ζ j : PadicAlgCl ℓ)) hζ :=
    funext (aeval_sub_one_universalChar h hζ)
  rw [hL, ← h_char]
  exact map_groupRingEval L.toLinearMap (universalChar h) a

section Valuation

variable {ℓ : ℕ} [ThePrime ℓ] {a b c : PadicAlgCl ℓ} {M : ℝ≥0∞}

/-- The ultrametric inequality for the valuation `v = ellVal` of `ℚ̄_ℓ`. -/
lemma le_ellVal_add (ha : M ≤ ellVal a) (hb : M ≤ ellVal b) : M ≤ ellVal (a + b) := by
  obtain h | h := le_max_iff.1 (IsUltrametricDist.norm_add_le_max a b)
  · exact ha.trans (ellVal_le_ellVal h)
  · exact hb.trans (ellVal_le_ellVal h)

lemma ellVal_eq_of_lt_ellVal_sub (h_lt : ellVal b < ellVal (a - b)) : ellVal a = ellVal b := by
  have h_norm : ‖a - b‖ < ‖b‖ := lt_of_not_ge fun h_le ↦ h_lt.not_ge (ellVal_le_ellVal h_le)
  refine ellVal_congr_norm ?_
  simpa [max_eq_right h_norm.le] using IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_norm.ne

/-- For units `a` and `b`, the differences `a⁻¹ - b⁻¹` and `a - b` have the same valuation. -/
lemma ellVal_inv_sub_inv (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : ellVal (a⁻¹ - b⁻¹) = ellVal (a - b) := by
  refine ellVal_congr_norm ?_
  rw [inv_sub_inv (norm_ne_zero_iff.1 (by simp [ha])) (norm_ne_zero_iff.1 (by simp [hb])),
    norm_div, norm_mul, ha, hb, mul_one, div_one, norm_sub_rev]

/-- For a unit `a`, the valuation of `a ^ k - 1` is at least that of `a - 1`, for every integer
`k`. -/
lemma ellVal_sub_one_le_ellVal_zpow_sub_one (ha : ‖a‖ = 1) (k : ℤ) :
    ellVal (a - 1) ≤ ellVal (a ^ k - 1) := by
  have h_nat (n : ℕ) : ellVal (a - 1) ≤ ellVal (a ^ n - 1) := by
    simpa using dvd_iff_ellVal_le.1 (sub_one_dvd_pow_sub_one (⟨a, ha.le⟩ : intQpBar ℓ) n)
  obtain ⟨n, rfl | rfl⟩ : ∃ n : ℕ, k = n ∨ k = -n := k.eq_nat_or_neg
  · simpa using h_nat n
  · calc ellVal (a - 1) ≤ ellVal (a ^ n - 1) := h_nat n
      _ = ellVal (a ^ (-n : ℤ) - 1) := by
        simpa using (ellVal_inv_sub_inv (a := a ^ n) (by simp [ha]) norm_one).symm

/-- If `‖a‖ = 1`, and `a ≡ b` and `c ≡ 1` up to valuation `M > v(b - 1)`, where `v = ellVal`, then
`v(1 - a * c) = v(b - 1)`. -/
lemma ellVal_one_sub_mul_eq (ha : ‖a‖ = 1) (hab : M ≤ ellVal (a - b)) (hc : M ≤ ellVal (c - 1))
    (hb : ellVal (b - 1) < M) : ellVal (1 - a * c) = ellVal (b - 1) := by
  have h_congr : M ≤ ellVal (a * c - 1 - (b - 1)) := by
    rw [show a * c - 1 - (b - 1) = a * (c - 1) + (a - b) by ring]
    exact le_ellVal_add (hc.trans_eq (ellVal_congr_norm (by simp [ha]))) hab
  rw [ellVal_congr_norm (norm_sub_rev 1 (a * c)), ellVal_eq_of_lt_ellVal_sub (hb.trans_le h_congr)]

/-- Let `a`, `b` and `q` be `ℓ`-adic units with `a ≡ b` and `q ≡ 1` up to valuation
`M > v(b - 1)`. Then `(1 - a q ^ k) (1 - a⁻¹ q ^ k)` has valuation at most `2 v(b - 1)`, since each
factor has the valuation of `b - 1`. -/
lemma ellVal_one_sub_mul_one_sub_inv_le {q : PadicAlgCl ℓ} (k : ℤ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hq_norm : ‖q‖ = 1) (hab : M ≤ ellVal (a - b)) (hq : M ≤ ellVal (q - 1))
    (hM : ellVal (b - 1) < M) :
    ellVal ((1 - a * q ^ k) * (1 - a⁻¹ * q ^ k)) ≤ 2 * ellVal (b - 1) := by
  have hq_zpow : M ≤ ellVal (q ^ k - 1) :=
    hq.trans (ellVal_sub_one_le_ellVal_zpow_sub_one hq_norm k)
  have hab_inv : M ≤ ellVal (a⁻¹ - b⁻¹) := hab.trans (ellVal_inv_sub_inv ha hb).ge
  have hb_inv : ellVal (b⁻¹ - 1) = ellVal (b - 1) := by
    rw [← ellVal_inv_sub_inv hb norm_one, inv_one]
  calc ellVal ((1 - a * q ^ k) * (1 - a⁻¹ * q ^ k))
      ≤ ellVal (1 - a * q ^ k) + ellVal (1 - a⁻¹ * q ^ k) := ellVal_mul_le
    _ = ellVal (b - 1) + ellVal (b⁻¹ - 1) := by
        rw [ellVal_one_sub_mul_eq ha hab hq_zpow hM,
          ellVal_one_sub_mul_eq (by simp [ha]) hab_inv hq_zpow (hb_inv.trans_lt hM)]
    _ = 2 * ellVal (b - 1) := by rw [hb_inv, two_mul]

/-- Let `a`, `b` and `q` be `ℓ`-adic units with `a ≡ b` and `q ≡ 1` up to valuation `M`, and let
`M > 2 r v(b - 1)`, where `r` is the length of the list `exps`. Then the product
`eulerFactor exps a q` of the factors `1 - a ^ (±1) q ^ (-e)`, `e ∈ exps`, has valuation at most
`2 r v(b - 1)`. -/
lemma ellVal_eulerFactor_le {q : ℕ} (exps : List ℤ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hq_norm : ‖(q : PadicAlgCl ℓ)‖ = 1) (hab : M ≤ ellVal (a - b))
    (hq : M ≤ ellVal (q - 1 : PadicAlgCl ℓ)) (hM : exps.length * (2 * ellVal (b - 1)) < M) :
    ellVal (eulerFactor exps a q) ≤ exps.length * (2 * ellVal (b - 1)) := by
  induction exps with
  | nil => simp [ellVal, eulerFactor_nil]
  | cons e exps ih =>
    rw [List.length_cons, Nat.cast_succ, add_one_mul] at hM ⊢
    rw [eulerFactor_cons, add_comm]
    exact ellVal_mul_le.trans (add_le_add
      (ellVal_one_sub_mul_one_sub_inv_le (-e) ha hb hq_norm hab hq <|
        (le_self_add.trans_eq (two_mul _).symm).trans_lt (le_add_self.trans_lt hM))
      (ih (le_self_add.trans_lt hM)))

end Valuation

section Congruence

variable {ℓ : ℕ} [ThePrime ℓ]

/-- Let `α` and `c` be `ℓ`-adic units. There is an integral polynomial `R` whose Gauss valuation of
radius `ρ` is at most `2 ρ`, with `R(ζ - 1) = ζ (1 - α ζ c) (1 - (α ζ)⁻¹ c)` for all integral
`ζ ≠ 0`. It is the product of `1 - α c (1 + X)` and `1 + X - α⁻¹ c`. -/
lemma exists_polynomial_one_sub_mul_one_sub_inv (ρ : ℚ≥0) {α c : PadicAlgCl ℓ} (hα : ‖α‖ = 1)
    (hc : ‖c‖ = 1) :
    ∃ R : (intQpBar ℓ)[X], gaussVal ρ R ≤ 2 * (ρ : ℝ≥0) ∧
      ∀ ζ : intQpBar ℓ, ζ ≠ 0 → ((R.eval (ζ - 1) : intQpBar ℓ) : PadicAlgCl ℓ) =
        ζ * ((1 - α * ζ * c) * (1 - (α * ζ)⁻¹ * c)) := by
  let a : intQpBar ℓ := ⟨α * c, by simp [hα, hc, ← NNReal.coe_le_coe]⟩
  let b : intQpBar ℓ := ⟨α⁻¹ * c, by simp [hα, hc, ← NNReal.coe_le_coe]⟩
  have ha_unit : IsUnit a := ellVal_eq_zero_iff_isUnit.1 (by simp [a, ellVal, hα, hc])
  have h_linear (g : (intQpBar ℓ)[X]) (hg : IsUnit (g.coeff 1)) : gaussVal ρ g ≤ (ρ : ℝ≥0) := by
    simpa using gaussVal_le_of_isUnit_coeff (ρ := ρ) hg
  refine ⟨(1 - C a * (1 + X)) * (1 + X - C b), ?_, fun ζ hζ ↦ ?_⟩
  · rw [gaussVal_mul, two_mul]
    exact add_le_add (h_linear _ (by simpa [coeff_one] using ha_unit))
      (h_linear _ (by simp [coeff_one]))
  · have hζ_ne : (ζ : PadicAlgCl ℓ) ≠ 0 := by simpa using hζ
    calc ((((1 - C a * (1 + X)) * (1 + X - C b)).eval (ζ - 1) : intQpBar ℓ) : PadicAlgCl ℓ)
        = (1 - α * c * ζ) * (ζ - α⁻¹ * c) := by simp [a, b]
      _ = ζ * ((1 - α * ζ * c) * (1 - (α * ζ)⁻¹ * c)) := by field_simp

/-- Let `α` and `q` be `ℓ`-adic units and `r` the length of the list `exps`. There is an integral
polynomial `R` whose Gauss valuation of radius `ρ` is at most `2 r ρ`, with `R(ζ - 1) = ζ ^ r ∏_e
∏_± (1 - (α ζ) ^ (±1) q ^ (-e))` for all integral `ζ ≠ 0`. The double product, over `e ∈ exps`, is
`eulerFactor exps (α ζ) q`. -/
lemma exists_polynomial_eulerFactor (ρ : ℚ≥0) (exps : List ℤ) {α : PadicAlgCl ℓ} (hα : ‖α‖ = 1)
    {q : ℕ} (hq : ‖(q : PadicAlgCl ℓ)‖ = 1) :
    ∃ R : (intQpBar ℓ)[X], gaussVal ρ R ≤ exps.length * (2 * (ρ : ℝ≥0)) ∧
      ∀ ζ : intQpBar ℓ, ζ ≠ 0 → ((R.eval (ζ - 1) : intQpBar ℓ) : PadicAlgCl ℓ) =
        (ζ : PadicAlgCl ℓ) ^ exps.length * eulerFactor exps (α * (ζ : PadicAlgCl ℓ)) q := by
  induction exps with
  | nil => exact ⟨1, by simp [gaussVal_one], fun ζ _ ↦ by simp [eulerFactor_nil]⟩
  | cons e exps ih =>
    obtain ⟨R, hR_le, hR_eval⟩ := ih
    obtain ⟨S, hS_le, hS_eval⟩ :=
      exists_polynomial_one_sub_mul_one_sub_inv ρ hα (c := (q : PadicAlgCl ℓ) ^ (-e)) (by simp [hq])
    refine ⟨R * S, ?_, fun ζ hζ ↦ ?_⟩
    · rw [gaussVal_mul, List.length_cons, Nat.cast_succ, add_one_mul]
      exact add_le_add hR_le hS_le
    · rw [eval_mul, MulMemClass.coe_mul, hR_eval ζ hζ, hS_eval ζ hζ, eulerFactor_cons,
        List.length_cons]
      ring

/-- A polynomial that vanishes at all `ζ - 1` with `ζ ^ q = 1` is divisible by `(1 + X) ^ q - 1`,
since these are the `q` distinct roots of this monic polynomial. -/
lemma one_add_X_pow_sub_one_dvd {q : ℕ} [NeZero q] {D : (intQpBar ℓ)[X]}
    (hD : ∀ ζ : intQpBar ℓ, ζ ^ q = 1 → D.eval (ζ - 1) = 0) : (1 + X) ^ q - 1 ∣ D := by
  obtain ⟨η, hη⟩ : ∃ η : PadicAlgCl ℓ, IsPrimitiveRoot η q := HasEnoughRootsOfUnity.prim
  let ζ : intQpBar ℓ := ⟨η, (hη.isOfFinOrder (NeZero.ne q)).norm_eq_one.le⟩
  have hζ : IsPrimitiveRoot ζ q := IsPrimitiveRoot.coe_submonoidClass_iff.1 hη
  have h_monic : IsMonicOfDegree ((1 + X) ^ q - 1 : (intQpBar ℓ)[X]) q := by
    simpa [add_comm] using ((isMonicOfDegree_X_add_one (1 : intQpBar ℓ)).pow q).sub
      (natDegree_one.trans_lt (by simpa using NeZero.pos q))
  have h_inj : Set.InjOn (fun i : ℕ ↦ ζ ^ i - 1) (range q) :=
    fun i hi j hj h_eq ↦ hζ.injOn_pow hi hj (sub_left_injective h_eq)
  have h_degree : (D %ₘ ((1 + X) ^ q - 1)).degree < #(range q) :=
    (degree_modByMonic_lt D h_monic.monic).trans_eq <| by
      simp [degree_eq_natDegree h_monic.monic.ne_zero, h_monic.natDegree_eq]
  have h_eval (i : ℕ) : (D %ₘ ((1 + X) ^ q - 1)).eval (ζ ^ i - 1) = 0 := by
    have h_root : (ζ ^ i) ^ q = 1 := by rw [pow_right_comm, hζ.pow_eq_one, one_pow]
    simp [modByMonic_eq_sub_mul_div, hD _ h_root, h_root]
  rw [← modByMonic_eq_zero_iff_dvd h_monic.monic]
  exact eq_zero_of_degree_lt_of_eval_index_eq_zero (range q) h_inj h_degree fun i _ ↦ h_eval i

/-- If `v(y) ≥ ρ` for the valuation `v = ellVal`, with `ρ ≤ 1`, then `(1 + y) ^ ℓ ^ N - 1` has
valuation at least `N * ρ`. -/
lemma le_ellVal_one_add_pow_sub_one {ρ : ℚ≥0} (hρ : ρ ≤ 1) {y : intQpBar ℓ}
    (hy : (ρ : ℝ≥0) ≤ ellVal (y : PadicAlgCl ℓ)) (N : ℕ) :
    (N : ℝ≥0∞) * (ρ : ℝ≥0) ≤ ellVal ((1 + y) ^ ℓ ^ N - 1 : intQpBar ℓ).val :=
  calc (N : ℝ≥0∞) * (ρ : ℝ≥0) ≤ ellVal (∑ i ∈ range (ℓ ^ N), (1 + y) ^ i).val :=
      le_ellVal_geom_sum hρ (by rwa [add_sub_cancel_left]) N
    _ ≤ ellVal ((1 + y) ^ ℓ ^ N - 1).val :=
      dvd_iff_ellVal_le.1 (Dvd.intro _ (geom_sum_mul (1 + y) (ℓ ^ N)))

/-- Let `(1 + X) ^ j P ≡ R` modulo `(1 + X) ^ ℓ ^ N - 1`, where the Gauss valuation `v_ρ(R)` is less
than `N ρ` and `ρ ≤ 1`. Then `v(P(y)) ≤ v_ρ(R)` at some point `y` with `v(y) ≥ ρ`. -/
lemma exists_ellVal_eval_le_gaussVal {ρ : ℚ≥0} (hρ : ρ ≤ 1) {N j : ℕ} {P R : (intQpBar ℓ)[X]}
    (h_congr : (1 + X) ^ ℓ ^ N - 1 ∣ (1 + X) ^ j * P - R) (hR : gaussVal ρ R < N * (ρ : ℝ≥0)) :
    ∃ y : intQpBar ℓ, (ρ : ℝ≥0) ≤ ellVal (y : PadicAlgCl ℓ) ∧
      ellVal (P.eval y).val ≤ gaussVal ρ R := by
  obtain ⟨y, hy, h_generic⟩ := exists_ellVal_eval_eq_gaussVal ρ R
  have h_dvd : (1 + y) ^ ℓ ^ N - 1 ∣ (1 + y) ^ j * P.eval y - R.eval y := by
    simpa using eval_dvd (x := y) h_congr
  have h_lt : ellVal (R.eval y).val < ellVal ((1 + y) ^ j * P.eval y - R.eval y).val :=
    calc ellVal (R.eval y).val = gaussVal ρ R := h_generic
      _ < N * (ρ : ℝ≥0) := hR
      _ ≤ ellVal ((1 + y) ^ ℓ ^ N - 1).val := le_ellVal_one_add_pow_sub_one hρ hy N
      _ ≤ ellVal ((1 + y) ^ j * P.eval y - R.eval y).val := dvd_iff_ellVal_le.1 h_dvd
  refine ⟨y, hy, ?_⟩
  calc ellVal (P.eval y).val
      ≤ ellVal ((1 + y) ^ j * P.eval y).val := dvd_iff_ellVal_le.1 (dvd_mul_left _ _)
    _ = ellVal (R.eval y).val := ellVal_eq_of_lt_ellVal_sub (by rwa [← AddSubgroupClass.coe_sub])
    _ = gaussVal ρ R := h_generic

end Congruence

section Line

variable {ℓ : ℕ} [ThePrime ℓ] {E σ : Type} [Field E] [EmbeddedNumberField E]
  [NumberField.IsCMField E] {q : ℕ} {Q : Finset (FinPlace E)}

/-- The polynomial `(1 + X) ^ (h g)`, with the exponent `h g ∈ ℤ / q` read as a natural number. It
is the restriction of `ψ_X(g) = ∏ (1 + X_j) ^ (h_j g)` to the line on which all variables but the
one belonging to `h` vanish. -/
def lineChar (h : Gal(Ω/E) →* Multiplicative (ZMod q)) (g : Gal(Ω/E)) : (intQpBar ℓ)[X] :=
  (1 + X) ^ (h g).toAdd.val

/-- Let the `h_i` be characters `Gal(Ω/E) → ℤ / q`, let `Q` be a finite set of primes of `E`, and
let `a` be an element of the group ring of `Cl_Q = U1ClassGroup Q`, the finite ideles `u` with
`u ū = 1` modulo those in `Eˣ` and the units that are `≡ 1` at the primes of `Q`. The value of
`ψ_X = ∏ (1 + X_i) ^ h_i` (`universalChar`) on `a`, at the point with `j`-th coordinate `y` and all
others `0`, is the value of `(1 + X) ^ h_j` (`lineChar`) on `a` at `X = y`. -/
lemma eval_single_groupRingEval_universalChar [Fintype σ] [DecidableEq σ]
    (h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)) (j : σ) (y : intQpBar ℓ)
    (a : MonoidAlgebra (intQpBar ℓ) (U1ClassGroup Q)) :
    MvPolynomial.eval (Pi.single j y) (groupRingEval (universalChar h) a) =
      (groupRingEval (lineChar (h j)) a : (intQpBar ℓ)[X]).eval y := by
  have h_line (g : Gal(Ω/E)) :
      MvPolynomial.eval (Pi.single j y) (universalChar h g) = (lineChar (h j) g).eval y := by
    rw [eval_universalChar, prod_eq_single_of_mem j (mem_univ j) fun i _ hi ↦ by simp [hi]]
    simp [lineChar]
  calc MvPolynomial.eval (Pi.single j y) (groupRingEval (universalChar h) a)
      = groupRingEval (fun g ↦ MvPolynomial.eval (Pi.single j y) (universalChar h g)) a :=
        map_groupRingEval (MvPolynomial.aeval (Pi.single j y)).toLinearMap (universalChar h) a
    _ = groupRingEval (fun g ↦ (lineChar (h j) g).eval y) a := by rw [funext h_line]
    _ = (groupRingEval (lineChar (h j)) a : (intQpBar ℓ)[X]).eval y :=
        (map_groupRingEval (leval y) (lineChar (h j)) a).symm

/-- For a function `f` on `Gal(Ω/E)` with polynomial values, extended linearly to the group ring of
`Cl_Q = U1ClassGroup Q` (`groupRingEval`), evaluation of the polynomials at a point `y` commutes
with this extension. -/
lemma coe_eval_groupRingEval (f : Gal(Ω/E) → (intQpBar ℓ)[X]) (y : intQpBar ℓ)
    (a : MonoidAlgebra (intQpBar ℓ) (U1ClassGroup Q)) :
    (((groupRingEval f a).eval y : intQpBar ℓ) : PadicAlgCl ℓ) =
      groupRingEval (fun g : Gal(Ω/E) ↦ (((f g).eval y : intQpBar ℓ) : PadicAlgCl ℓ)) a :=
  map_groupRingEval (Algebra.linearMap (intQpBar ℓ) (PadicAlgCl ℓ) ∘ₗ leval y) f a

/-- At `X = ζ - 1` with `ζ ^ q = 1`, the value of `(1 + X) ^ h` (`lineChar`) on an element `a` of
the group ring of `Cl_Q` is the value of the character `ζ ^ h` on `a`. -/
lemma coe_eval_groupRingEval_lineChar [NeZero q] (h : Gal(Ω/E) →* Multiplicative (ZMod q))
    {ζ : intQpBar ℓ} (hζ : (ζ : PadicAlgCl ℓ) ^ q = 1)
    (a : MonoidAlgebra (intQpBar ℓ) (U1ClassGroup Q)) :
    (((groupRingEval (lineChar h) a : (intQpBar ℓ)[X]).eval (ζ - 1) : intQpBar ℓ) : PadicAlgCl ℓ) =
      groupRingEval ((AddChar.zmodChar q hζ).toMonoidHom.comp h) a := by
  rw [coe_eval_groupRingEval]
  exact congrArg (groupRingEval · a) (funext fun g ↦ by simp [lineChar, AddChar.zmodChar_apply])

/-- At `X = 0`, the value of `(1 + X) ^ h` (`lineChar`) on an element `a` of the group ring of
`Cl_Q` is the value of the trivial character on `a`. -/
lemma coe_eval_zero_groupRingEval_lineChar (h : Gal(Ω/E) →* Multiplicative (ZMod q))
    (a : MonoidAlgebra (intQpBar ℓ) (U1ClassGroup Q)) :
    (((groupRingEval (lineChar h) a : (intQpBar ℓ)[X]).eval 0 : intQpBar ℓ) : PadicAlgCl ℓ) =
      groupRingEval (1 : Gal(Ω/E) →* PadicAlgCl ℓ) a := by
  rw [coe_eval_groupRingEval]
  exact congrArg (groupRingEval · a) (funext fun g ↦ by simp [lineChar])

end Line

/-- A natural number `q ≡ 1` modulo a positive power of `ℓ` is an `ℓ`-adic unit. -/
lemma norm_natCast_eq_one_of_modEq {ℓ : ℕ} [ThePrime ℓ] {q N : ℕ} (hN : N ≠ 0)
    (hq : q ≡ 1 [MOD ℓ ^ N]) : ‖(q : PadicAlgCl ℓ)‖ = 1 :=
  have h_coprime : q.Coprime ℓ :=
    Nat.coprime_of_mul_modEq_one 1 <| by simpa using hq.of_dvd (dvd_pow_self ℓ hN)
  h_coprime.symm.norm_natCast_eq_one _

/-- If `q ≡ 1` modulo `ℓ ^ N`, then `q - 1` has valuation (`ellVal`) at least `N`. -/
lemma le_ellVal_natCast_sub_one {ℓ : ℕ} [ThePrime ℓ] {q N : ℕ} (hq : q ≡ 1 [MOD ℓ ^ N]) :
    (N : ℝ≥0∞) ≤ ellVal (q - 1 : PadicAlgCl ℓ) := by
  simpa using dvd_iff_ellVal_le.1 ((Int.castRingHom (intQpBar ℓ)).map_dvd hq.symm.dvd)

namespace StickelbergerSystem

variable {ℓ : ℕ} [ThePrime ℓ] {E ι O : Type} [Field E] [EmbeddedNumberField E]
  [NumberField.IsCMField E] [CommRing O]
  {S₀ : Finset (FinPlace E)} {g₀ : Gal(Ω/E)} (Y : StickelbergerSystem ℓ S₀ g₀)

/-- Near `g₀` the values of the continuous character `ϑ = Y.twistChar` of the Stickelberger system
`Y` are congruent to `ϑ(g₀)` modulo `ℓ ^ M`. -/
lemma eventually_le_ellVal_sub (M : ℕ) :
    ∀ᶠ g : Gal(Ω/E) in nhds g₀, (M : ℝ≥0∞) ≤ ellVal
      (Y.twistChar g - Y.twistChar g₀ : PadicAlgCl ℓ) := by
  have h_pos : 0 < ‖(ℓ : PadicAlgCl ℓ) ^ M‖ := norm_pos_iff.2 (pow_ne_zero M (NeZero.ne _))
  filter_upwards [(Units.continuous_val.comp Y.continuous_twistChar).continuousAt.eventually
    (Metric.closedBall_mem_nhds _ h_pos)] with g hg using
    by simpa using ellVal_le_ellVal (mem_closedBall_iff_norm.1 hg)

variable {U : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)} {N : ℕ} {P₀ : FinPlace E}
  {J : Finset (FinPlace E)} {x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}

open scoped Classical in
/-- The norm relation of a Stickelberger system along tied primes. If `ζ ^ ℓ ^ N = 1`, the value of
the character `ζ ^ h_{P₀}` at `Θ_J` is its value at `Θ_{P₀}` times the product, over `v ≠ P₀` in `J`
and all `e`, of `(1 - a q ^ (-e)) (1 - a⁻¹ q ^ (-e))` (`eulerFactor`), where `a = ϑ(φ_v) ζ` and `q`
is the norm of `v`. -/
lemma groupRingEval_element_eq_mul_prod_eulerFactor (h_tied : IsTiedPrimes ℓ S₀ U W N P₀ J x)
    {ζ : PadicAlgCl ℓ} (hζ : ζ ^ ℓ ^ N = 1) :
    groupRingEval ((AddChar.zmodChar (ℓ ^ N) hζ).toMonoidHom.comp (x P₀).1.character)
        (Y.element J) =
      groupRingEval ((AddChar.zmodChar (ℓ ^ N) hζ).toMonoidHom.comp (x P₀).1.character)
          (Y.element {P₀}) *
        ∏ v ∈ J.erase P₀,
          eulerFactor Y.exponents ((Y.twistChar (x v).1.frob : PadicAlgCl ℓ) * ζ) v.q := by
  set ψ : Gal(Ω/E) →* PadicAlgCl ℓ :=
    (AddChar.zmodChar (ℓ ^ N) hζ).toMonoidHom.comp (x P₀).1.character with hψ_def
  have hψ : IsFromU1 (placesDividing E ℓ) ({P₀} : Finset (FinPlace E)) ψ := by
    simpa using (h_tied.isAuxPrimeDataAt P₀ h_tied.first_mem).toIsFromU1.map _
  have hψ_frob (v : FinPlace E) (hv : v ∈ J.erase P₀) : ψ (x v).1.frob = ζ := by
    simpa [hψ_def, h_tied.char_frob_eq_ite v (mem_of_mem_erase hv) (ne_of_mem_erase hv) P₀
      h_tied.first_mem] using AddChar.zmodChar_apply' hζ 1
  have h_union : {P₀} ∪ J.erase P₀ = J := by rw [← insert_eq, insert_erase h_tied.first_mem]
  calc groupRingEval ψ (Y.element J)
      = groupRingEval ψ (Y.element {P₀}) * ∏ v ∈ J.erase P₀,
          eulerFactor Y.exponents ((Y.twistChar (x v).1.frob : PadicAlgCl ℓ) * ψ (x v).1.frob)
            v.q := by
        conv_lhs => rw [← h_union]
        exact Y.groupRingEval_element_union (disjoint_singleton_left.2 (notMem_erase P₀ J))
          (h_tied.auxiliary.mono h_union.subset) hψ
          (fun v hv ↦ (h_tied.isAuxPrimeDataAt v (mem_of_mem_erase hv)).isPlaceOver)
          (fun v hv ↦ (h_tied.isAuxPrimeDataAt v (mem_of_mem_erase hv)).isFrob)
    _ = groupRingEval ψ (Y.element {P₀}) * ∏ v ∈ J.erase P₀,
          eulerFactor Y.exponents ((Y.twistChar (x v).1.frob : PadicAlgCl ℓ) * ζ) v.q :=
        congrArg _ (prod_congr rfl fun v hv ↦ by rw [hψ_frob v hv])

open scoped Classical in
/-- The congruence `(1 + X) ^ j₀ P(X, 0) ≡ R₀(X) R(X)` modulo `(1 + X) ^ ℓ ^ N - 1`, for `N ≠ 0`.
The polynomials `P(X, 0)` and `R₀(X)` are the values of `(1 + X) ^ h₀` (`lineChar`) at `Θ_J` and
`Θ_{P₀}`, where `h₀ = (x P₀).1.character`, and `j₀ = #(J \ {P₀}) * r` with `r` the length of
`Y.exponents`. The polynomial `R` collects the Euler factors at the primes other than `P₀`, and its
Gauss valuation of radius `ρ` is at most `2 j₀ ρ`. -/
lemma exists_congruence_lineChar_element (h_tied : IsTiedPrimes ℓ S₀ U W N P₀ J x) (hN : N ≠ 0)
    (ρ : ℚ≥0) :
    ∃ R : (intQpBar ℓ)[X],
      gaussVal ρ R ≤ #(J.erase P₀) * (Y.exponents.length * (2 * (ρ : ℝ≥0))) ∧
      (1 + X) ^ ℓ ^ N - 1 ∣
        (1 + X) ^ (Y.exponents.length * #(J.erase P₀)) *
            groupRingEval (lineChar (x P₀).1.character) (Y.element J) -
          groupRingEval (lineChar (x P₀).1.character) (Y.element {P₀}) * R := by
  -- `R` is the product of the polynomials for the Euler factors at the primes `v ≠ P₀`. The
  -- congruence is checked at the roots `ζ - 1` of the modulus, where it is the norm relation.
  let euler (v : FinPlace E) (ζ : intQpBar ℓ) : PadicAlgCl ℓ :=
    eulerFactor Y.exponents ((Y.twistChar (x v).1.frob : PadicAlgCl ℓ) * (ζ : PadicAlgCl ℓ)) v.q
  have h_poly (v : FinPlace E) (hv : v ∈ J.erase P₀) : ∃ R : (intQpBar ℓ)[X],
      gaussVal ρ R ≤ Y.exponents.length * (2 * (ρ : ℝ≥0)) ∧ ∀ ζ : intQpBar ℓ, ζ ≠ 0 →
        (R.eval (ζ - 1) : intQpBar ℓ) = (ζ : PadicAlgCl ℓ) ^ Y.exponents.length * euler v ζ :=
    exists_polynomial_eulerFactor ρ Y.exponents (Y.norm_twistChar _)
      (norm_natCast_eq_one_of_modEq hN (h_tied.isAuxPrimeDataAt v (mem_of_mem_erase hv)).norm_modEq)
  choose! R hR_le hR_eval using h_poly
  refine ⟨∏ v ∈ J.erase P₀, R v, ?_, one_add_X_pow_sub_one_dvd fun ζ hζ ↦ ?_⟩
  · rw [gaussVal_prod, ← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ hR_le
  have hζ_coe : (ζ : PadicAlgCl ℓ) ^ ℓ ^ N = 1 := mod_cast hζ
  have hζ_ne : ζ ≠ 0 := (IsUnit.of_pow_eq_one hζ (NeZero.ne _)).ne_zero
  have h_prod : ((∏ v ∈ J.erase P₀, R v).eval (ζ - 1) : intQpBar ℓ) =
      (ζ : PadicAlgCl ℓ) ^ (Y.exponents.length * #(J.erase P₀)) * ∏ v ∈ J.erase P₀, euler v ζ := by
    rw [eval_prod, SubmonoidClass.coe_finsetProd, prod_congr rfl fun v hv ↦ hR_eval v hv ζ hζ_ne,
      prod_mul_distrib, prod_const, pow_mul]
  have h_norm_rel :
      ((groupRingEval (lineChar (x P₀).1.character) (Y.element J)).eval (ζ - 1) : intQpBar ℓ) =
        ((groupRingEval (lineChar (x P₀).1.character) (Y.element {P₀})).eval (ζ - 1) : intQpBar ℓ) *
          ∏ v ∈ J.erase P₀, euler v ζ := by
    rw [coe_eval_groupRingEval_lineChar _ hζ_coe, coe_eval_groupRingEval_lineChar _ hζ_coe,
      Y.groupRingEval_element_eq_mul_prod_eulerFactor h_tied hζ_coe]
  rw [eval_sub, sub_eq_zero, eval_mul, eval_mul, Subtype.ext_iff, MulMemClass.coe_mul,
    MulMemClass.coe_mul, h_norm_rel, h_prod]
  simp [mul_left_comm]

/-- A Stickelberger system `Y` for a set `S₀` of places and an element `g₀ ∈ Gal(Ω/E)` gives
elements `Θ_Q = Y.element Q` of the group rings of class groups `Cl_Q` with a norm relation, a
character `ϑ = Y.twistChar` with `ϑ(g₀) ≠ 1` and a list of `r` integers `e` (`Y.exponents`). Let
`β = v(1(Θ_∅)) + 2 r v(ϑ(g₀) - 1)`, where `1` is the trivial character and `v = ellVal`. Let `J` be
tied auxiliary primes with first prime `P₀`, so the norm `q` of `P₀` is `≡ 1` modulo `ℓ ^ N`, and
let `φ = (x P₀).1.frob` be its Frobenius element. If `β < M ≤ N` and `ϑ(φ) ≡ ϑ(g₀)` modulo `ℓ ^ M`,
then `v(1(Θ_{P₀})) ≤ β`, since each factor `1 - ϑ(φ) ^ (±1) q ^ (-e)` is congruent to
`1 - ϑ(g₀) ^ (±1)` modulo `ℓ ^ M`. -/
lemma ellVal_one_element_singleton_le (h_tied : IsTiedPrimes ℓ S₀ U W N P₀ J x) {M : ℕ}
    (hM : Y.β < M) (hMN : M ≤ N)
    (h_frob : (M : ℝ≥0∞) ≤ ellVal (Y.twistChar (x P₀).1.frob - Y.twistChar g₀ : PadicAlgCl ℓ)) :
    ellVal (groupRingEval (1 : Gal(Ω/E) →* PadicAlgCl ℓ) (Y.element {P₀})) ≤ Y.β := by
  classical
  have h_data := h_tied.isAuxPrimeDataAt P₀ h_tied.first_mem
  rw [← insert_empty_eq P₀, Y.element_insert ∅ P₀ (notMem_empty P₀)
    (h_tied.auxiliary.mono (singleton_subset_iff.2 h_tied.first_mem)) 1 IsFromU1.one _
    h_data.isPlaceOver _ h_data.isFrob, MonoidHom.one_apply, mul_one, β]
  exact ellVal_mul_le.trans (add_le_add le_rfl (ellVal_eulerFactor_le Y.exponents
    (Y.norm_twistChar _) (Y.norm_twistChar _)
    (norm_natCast_eq_one_of_modEq ((Nat.cast_pos.1 hM.pos).trans_le hMN).ne' h_data.norm_modEq)
    h_frob ((Nat.cast_le.2 hMN).trans (le_ellVal_natCast_sub_one h_data.norm_modEq))
    (le_add_self.trans_lt hM)))

/-- The system `Y`, for a set `S₀` of places and `g₀ ∈ Gal(Ω/E)`, gives elements `Θ_Q = Y.element Q`
of the group rings of class groups `Cl_Q` with a norm relation, a character `ϑ = Y.twistChar` and
`r` integers (`Y.exponents`); `β = v(1(Θ_∅)) + 2 r v(ϑ(g₀) - 1)`, with `v = ellVal`. Suppose
`ϑ(φ_{P₀}) ≡ ϑ(g₀)` modulo `ℓ ^ M`, `β + 1 < M ≤ N ρ`, and a natural number `s₀ ≥ 1` satisfies
`2 r #J ≤ s₀` and `s₀ ρ < 1`. Then `v(P(y)) ≤ β + s₀ ρ` at some point `y` whose coordinates have
valuation at least `ρ`. -/
theorem exists_point_ellVal_universalChar_le (h_tied : IsTiedPrimes ℓ S₀ U W N P₀ J x)
    {M s₀ : ℕ} {ρ : ℚ≥0} (hM : Y.β + 1 < M)
    (h_frob : (M : ℝ≥0∞) ≤ ellVal (Y.twistChar (x P₀).1.frob - Y.twistChar g₀ : PadicAlgCl ℓ))
    (hs₀ : 1 ≤ s₀) (h_card : 2 * Y.exponents.length * #J ≤ s₀) (hρ : s₀ * ρ < 1)
    (h_level : M ≤ N * ρ) :
    ∃ y : J → intQpBar ℓ, (∀ j : J, (ρ : ℝ≥0) ≤ ellVal (y j : PadicAlgCl ℓ)) ∧
      ellVal (MvPolynomial.eval y
          (groupRingEval (universalChar fun j : J ↦ (x j).1.character) (Y.element J))).val ≤
        Y.β + s₀ * (ρ : ℝ≥0) := by
  -- The point lies on the line on which all variables but the one of `P₀` vanish. There `P` is
  -- congruent to `R₀ R₁` up to a power of `1 + X`, and `v_ρ(R₀ R₁) ≤ β + s₀ ρ < N ρ`.
  classical
  have hρ_le : ρ ≤ 1 := (le_mul_of_one_le_left zero_le (mod_cast hs₀)).trans hρ.le
  have hMN : M ≤ N := mod_cast h_level.trans (mul_le_of_le_one_right zero_le hρ_le)
  let R₀ : (intQpBar ℓ)[X] := groupRingEval (lineChar (x P₀).1.character) (Y.element {P₀})
  have hN : N ≠ 0 := ((Nat.cast_pos.1 hM.pos : 0 < M).trans_le hMN).ne'
  obtain ⟨R₁, hR₁_le, h_congr⟩ : ∃ R₁ : (intQpBar ℓ)[X],
      gaussVal ρ R₁ ≤ #(J.erase P₀) * (Y.exponents.length * (2 * (ρ : ℝ≥0))) ∧
      (1 + X) ^ ℓ ^ N - 1 ∣ (1 + X) ^ (Y.exponents.length * #(J.erase P₀)) *
        groupRingEval (lineChar (x P₀).1.character) (Y.element J) - R₀ * R₁ :=
    Y.exists_congruence_lineChar_element h_tied hN ρ
  have hR₀ : gaussVal ρ R₀ ≤ Y.β := by
    refine (gaussVal_le_eval_zero R₀).trans ?_
    rw [coe_eval_zero_groupRingEval_lineChar]
    exact Y.ellVal_one_element_singleton_le h_tied (le_self_add.trans_lt hM) hMN h_frob
  have hR₁ : gaussVal ρ R₁ ≤ s₀ * (ρ : ℝ≥0) := by
    have h_count : #(J.erase P₀) * (Y.exponents.length * 2) ≤ s₀ :=
      calc #(J.erase P₀) * (Y.exponents.length * 2) ≤ #J * (Y.exponents.length * 2) :=
          Nat.mul_le_mul_right _ card_erase_le
        _ = 2 * Y.exponents.length * #J := by ring
        _ ≤ s₀ := h_card
    calc gaussVal ρ R₁ ≤ #(J.erase P₀) * (Y.exponents.length * 2) * (ρ : ℝ≥0) := by
          rwa [mul_assoc, mul_assoc]
      _ ≤ s₀ * (ρ : ℝ≥0) := mul_le_mul_left (mod_cast h_count) _
  have hR : gaussVal ρ (R₀ * R₁) ≤ Y.β + s₀ * (ρ : ℝ≥0) :=
    (gaussVal_mul _ _).trans_le (add_le_add hR₀ hR₁)
  have hR_lt : gaussVal ρ (R₀ * R₁) < N * (ρ : ℝ≥0) :=
    calc gaussVal ρ (R₀ * R₁) ≤ Y.β + s₀ * (ρ : ℝ≥0) := hR
      _ ≤ Y.β + 1 := add_le_add le_rfl (mod_cast hρ.le)
      _ < M := hM
      _ ≤ N * (ρ : ℝ≥0) := mod_cast h_level
  obtain ⟨y, hy, hP⟩ : ∃ y : intQpBar ℓ, (ρ : ℝ≥0) ≤ ellVal (y : PadicAlgCl ℓ) ∧
      ellVal ((groupRingEval (lineChar (x P₀).1.character) (Y.element J)).eval y).val ≤
        gaussVal ρ (R₀ * R₁) :=
    exists_ellVal_eval_le_gaussVal hρ_le h_congr hR_lt
  refine ⟨Pi.single ⟨P₀, h_tied.first_mem⟩ y, fun j ↦ ?_, ?_⟩
  · obtain rfl | hj := eq_or_ne j ⟨P₀, h_tied.first_mem⟩
    · simpa using hy
    · simp [hj, ellVal_zero]
  · rw [eval_single_groupRingEval_universalChar]
    exact hP.trans hR

end StickelbergerSystem

end New.Selmer

end
end
end

section
/-!
# The failure to be tied

At a prime of norm `≡ 1` modulo `ℓ ^ N`, a Frobenius element `φ` and an inertial element `γ` commute
up to wild inertia and `ℓ ^ N`-th powers of inertia. If these act trivially and a cocycle `z`
vanishes on them, then `z(γ φ) = z(φ γ)`, which is the relation `(φ - 1) z(γ) = (γ - 1) z(φ)`.

Let `𝔮₀` be the first auxiliary prime and `s_𝔮` the slopes at the others. At a point of the line
`X_{𝔮₀} = Y`, `X_𝔮 = s_𝔮 Y` the relation puts `tie_w(z) = z(γ_w) - s_𝔮 z(φ_w)`, for `w = 𝔮, 𝔮̄`, in
the kernel of `φ_w - 1` for the twisted action. At `Y = 0` it does the same for `z(γ_w)`,
`w = 𝔮₀, 𝔮̄₀`. The valuation of a determinant bounds the length of the kernel.

* `New.Selmer.sub_one_smul_eq_of_tame`: the relation.
* `New.Selmer.selmerOnLine`: the Selmer module of the twist at a point of the line.
* `New.Selmer.IsTiedPrimes.relLength_tied_le`: the failure to be tied at the primes other than the
  first is at most `v(P¹(y))`, where `P¹ = New.Selmer.tiePolynomial`.
* `New.Selmer.IsTiedPrimes.relLength_tieRelations_le_sum_addVal_det`: the cost of dropping the ties
  at the first prime and its conjugate, at the point `0`.

Letters: `J` is the set of all auxiliary primes, `P₀ ∈ J` is the first prime `𝔮₀`, and `d` attaches
to `v ∈ J` the elements `φ_v = (d v).1.frob` and `γ_v = (d v).1.tameGenerator`, the homomorphism
`λ_v = (d v).1.character` to `ℤ / ℓ ^ N` and, for each index `i : ι`, the slope `(d v).2 i`.
Coefficients are taken modulo `ℓ ^ M`.

Notions from other files:
* `New.Selmer.IsTiedPrimes`: an auxiliary set `J` of primes with places, Frobenius elements `φ`,
  tame generators `γ`, characters to `ℤ / ℓ ^ N` and slopes, and a first prime `P₀ ∈ J`.
* `New.Selmer.tieRelations`: the ties `z(γ) = s z(φ)` at the primes of a set and at their
  conjugates.
* `New.Selmer.universalChar`: the polynomial `ψ_X(g) = ∏ (1 + X_j) ^ (h_j g)`;
  `New.Selmer.selmerAtPoint` is the Selmer module `Sel(x)` of the twist by `ψ_x`.

## Relation to the literature

See `New.Congruences.Selmer.TwistingTheorem` for related work.
-/

@[expose] public section

noncomputable section

namespace New.Selmer

open Finset

open scoped Polynomial

variable {ℓ : ℕ}

section Affine

open Matrix.Module

variable {E O n B : Type} [Field E] [EmbeddedNumberField E] [CommRing O] [Fintype n] [DecidableEq n]
  [AddCommGroup B] [Module O B] {ρ : Gal(Ω/E) →* Matrix n n O} {c : Gal(Ω/E) → n → B}

/-- If `g` acts through `ρ` by the scalar `α`, then the affine action `u ↦ c(g) + g u` of the
cocycle `c` has `k`-th iterate `u ↦ α ^ k u + ∑ i < k, α ^ i c(g)` at `g`. At `u = 0` this says
`c(g ^ k) = ∑ i < k, α ^ i c(g)`. -/
lemma affineAction_pow_apply (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    {g : Gal(Ω/E)} {α : O} (hg : ρ g = α • 1) (k : ℕ) (u : n → B) :
    (affineAction hc g ^ k) u = α ^ k • u + (∑ i ∈ range k, α ^ i) • c g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, affineAction_apply, hg, smul_assoc, one_smul,
      geom_sum_succ]
    module

/-- If `g` acts through `ρ` by the scalar `α` and `∑ i < k, α ^ i = 0`, then the affine action
`u ↦ c(g) + g u` of the cocycle `c` at `g` has `k`-th power `1`: the element `g ^ k` acts trivially
and `c` vanishes at it. -/
lemma affineAction_pow_eq_one (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    {g : Gal(Ω/E)} {α : O} (hg : ρ g = α • 1) {k : ℕ} (hα : ∑ i ∈ range k, α ^ i = 0) :
    affineAction hc g ^ k = 1 := by
  have h_pow : α ^ k = 1 := by rw [← sub_eq_zero, ← geom_sum_mul, hα, zero_mul]
  exact Equiv.ext fun u ↦ by simp [affineAction_pow_apply hc hg, hα, h_pow]

/-- Let `c` be a locally constant cocycle for `ρ`, let `A` be a place of `Ω` over the prime `v`, and
let `ρ` be trivial on the elements of inertia at `A` near `1`. Each `g` acts by the affine map
`u ↦ c(g) + ρ(g) u` (`affineAction`). Suppose that this map has `q`-th power `1` for every `g` in
inertia at `A`, with `q` prime to `A`. Then the affine maps of a Frobenius element `φ` at `A` of
norm `k ≡ 1` modulo `q` and of an element `γ` of inertia at `A` commute. -/
lemma commute_affineAction (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    {A : ClosurePlace} {v : FinPlace E} (hA : IsPlaceOver A v) (hc_lc : IsLocallyConstant c)
    (h_open : ∀ᶠ g : Gal(Ω/E) in nhds 1, g ∈ inertiaGroup Gal(Ω/E) A → ρ g = 1) {q k : ℕ}
    (hq : A.valuation (q : ℕ) = 1)
    (h_pow : ∀ g ∈ inertiaGroup Gal(Ω/E) A, affineAction hc g ^ q = 1) (hk : k ≡ 1 [MOD q])
    {φ γ : Gal(Ω/E)} (hφ : IsFrob A k φ) (hγ : γ ∈ inertiaGroup Gal(Ω/E) A) :
    Commute (affineAction hc φ) (affineAction hc γ) := by
  have h_one : c 1 = 0 := by simpa using hc 1 1
  have h_near : ∀ᶠ g : Gal(Ω/E) in nhds 1,
      g ∈ inertiaGroup Gal(Ω/E) A → affineAction hc g = 1 := by
    filter_upwards [hc_lc.eventually_eq 1, h_open] with g hcg hρg hg
    exact Equiv.ext fun u ↦ by simp [affineAction_apply, hcg, h_one, hρg hg]
  -- On inertia the action is tame, so conjugation by `φ` is the power `k ≡ 1` modulo `q`.
  have h_conj : affineAction hc (φ * γ * φ⁻¹) = affineAction hc γ := by
    rw [(hA.tame_inertia (affineAction hc) h_near hq h_pow ⟨γ, hγ⟩).right k φ hφ,
      pow_eq_pow_of_modEq hk (h_pow γ hγ), pow_one]
  rw [commute_iff_eq, ← map_mul, ← h_conj, ← map_mul, inv_mul_cancel_right]

/-- If the affine maps `u ↦ c(g) + g u` of the cocycle `c` at `g = φ` and `g = γ` commute, then
`c(γ φ) = c(φ γ)`, which is `(φ - 1) c(γ) = (γ - 1) c(φ)` by the cocycle rule. -/
lemma sub_one_smul_eq_of_commute (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    {φ γ : Gal(Ω/E)} (h_comm : Commute (affineAction hc φ) (affineAction hc γ)) :
    (ρ φ - 1) • c γ = (ρ γ - 1) • c φ := by
  have h_swap : c φ + ρ φ • c γ = c γ + ρ γ • c φ := by
    simpa [affineAction_apply] using DFunLike.congr_fun h_comm.eq 0
  rw [sub_smul, sub_smul, one_smul, one_smul]
  linear_combination (norm := abel) h_swap

/-- The relation `(φ - 1) c(γ) = (γ - 1) c(φ)` for a cocycle `c` passes from `φ` to `φ⁻¹` if `γ`
acts by a scalar: multiply it by `-φ⁻¹` and use `c(φ⁻¹) = -φ⁻¹ c(φ)`. -/
lemma inv_sub_one_smul_eq (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    {φ γ : Gal(Ω/E)} {α : O} (hγ : ρ γ = α • 1) (h_rel : (ρ φ - 1) • c γ = (ρ γ - 1) • c φ) :
    (ρ φ⁻¹ - 1) • c γ = (ρ γ - 1) • c φ⁻¹ := by
  have h_inv : ρ φ⁻¹ * ρ φ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have h_comm : ρ φ⁻¹ * (ρ γ - 1) = (ρ γ - 1) * ρ φ⁻¹ := by simp [hγ, mul_sub, sub_mul]
  calc
    (ρ φ⁻¹ - 1) • c γ = -(ρ φ⁻¹ • (ρ φ - 1) • c γ) := by
      rw [← mul_smul, mul_sub, h_inv, mul_one, ← neg_smul, neg_sub]
    _ = -(ρ φ⁻¹ • (ρ γ - 1) • c φ) := by rw [h_rel]
    _ = (ρ γ - 1) • c φ⁻¹ := by
      rw [cocycle_apply_inv hc, smul_neg, ← mul_smul, h_comm, mul_smul]

/-- The relation from tame inertia. Let `q` be prime to the place `A`, let `ρ` be trivial on
inertia near `1`, and let each inertial element act by a scalar `α` with `∑ i < q, α ^ i = 0`. If
`φ` or `φ⁻¹` is a Frobenius element of norm `k ≡ 1` modulo `q` and `γ` is inertial, every locally
constant cocycle `c` has `(φ - 1) c(γ) = (γ - 1) c(φ)`. -/
lemma sub_one_smul_eq_of_tame (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    {A : ClosurePlace} {v : FinPlace E} (hA : IsPlaceOver A v) (hc_lc : IsLocallyConstant c)
    (h_open : ∀ᶠ g : Gal(Ω/E) in nhds 1, g ∈ inertiaGroup Gal(Ω/E) A → ρ g = 1) {q k : ℕ}
    (hq : A.valuation (q : ℕ) = 1)
    (h_scalar : ∀ g ∈ inertiaGroup Gal(Ω/E) A, ∃ α : O, ρ g = α • 1 ∧ ∑ i ∈ range q, α ^ i = 0)
    (hk : k ≡ 1 [MOD q]) {φ γ : Gal(Ω/E)} (hφ : IsFrob A k φ ∨ IsFrob A k φ⁻¹)
    (hγ : γ ∈ inertiaGroup Gal(Ω/E) A) : (ρ φ - 1) • c γ = (ρ γ - 1) • c φ := by
  have h_frob {φ' : Gal(Ω/E)} (hφ' : IsFrob A k φ') : (ρ φ' - 1) • c γ = (ρ γ - 1) • c φ' := by
    refine sub_one_smul_eq_of_commute hc
      (commute_affineAction hc hA hc_lc h_open hq (fun g hg ↦ ?_) hk hφ' hγ)
    obtain ⟨α, hα, h_sum⟩ := h_scalar g hg
    exact affineAction_pow_eq_one hc hα h_sum
  obtain hφ | hφ := hφ
  · exact h_frob hφ
  · obtain ⟨α, hα, -⟩ := h_scalar γ hγ
    simpa only [inv_inv] using inv_sub_one_smul_eq hc hα (h_frob hφ)

end Affine

section Line

open Matrix.Module Module IsDiscreteValuationRing Polynomial

variable {E ι O n : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  [CommRing O] [Fintype n] [DecidableEq n]
  {V : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)} {S₀ J : Finset (FinPlace E)} {M N : ℕ}
  {P₀ : FinPlace E} {ρ : Gal(Ω/E) →* Matrix n n O}
  {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}

open scoped Classical in
/-- The direction of the line `X_{P₀} = Y`, `X_v = s_v Y` in the space with coordinates `X_v`,
`v ∈ J`: the entry at the prime `P₀` is `1`, and the entry at `v ≠ P₀` is the slope
`s_v = (d v).2 i` that `d` attaches to `v` and the index `i`. -/
def lineDirection {q : ℕ} (P₀ : FinPlace E) (J : Finset (FinPlace E))
    (d : FinPlace E → AuxPrimeData E q × (ι → O)) (i : ι) (v : J) : O :=
  if ↑v = P₀ then 1 else (d v).2 i

/-- The Selmer module at the point `Y = y` of the line with index `i`. The point `x` has coordinates
`x_{P₀} = y` and `x_v = e(s_v) y` for `v ≠ P₀` in `J`, where `s_v = (d v).2 i` (`lineDirection`).
The module is `Sel(x)` (`selmerAtPoint`) for the characters that `d` attaches to the primes of `J`:
the locally constant cocycles in `(O' / ℓ ^ M) ^ n` for the twist of `ρ` at `x` that are unramified
outside `S` and obey the linear relations `L`. -/
def selmerOnLine (ℓ M : ℕ) {q : ℕ} (ρ : Gal(Ω/E) →* Matrix n n O) (P₀ : FinPlace E)
    (J : Finset (FinPlace E)) (d : FinPlace E → AuxPrimeData E q × (ι → O)) (i : ι)
    {O' : Type} [CommRing O'] (e : O →+* O') (y : O') (S : Set (FinPlace E))
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) : Submodule O' (Gal(Ω/E) → n → QuotSpan (ℓ ^ M : O')) :=
  selmerAtPoint ℓ M (fun v : J ↦ (d v).1.character) ρ S L e fun v : J ↦
    e (lineDirection P₀ J d i v) * y

/-- The polynomial `det ((1 + Y) A - 1)`. -/
def shiftedDet (A : Matrix n n O) : O[X] := ((1 + X : O[X]) • A.map C - 1).det

/-- Evaluating `shiftedDet A` at `y`, with coefficients mapped by `e`, gives
`det ((1 + y) e(A) - 1)`. -/
lemma eval₂_shiftedDet {O' : Type} [CommRing O'] (e : O →+* O') (y : O') (A : Matrix n n O) :
    (shiftedDet A).eval₂ e y = ((1 + y) • A.map e - 1).det := by
  rw [shiftedDet, ← coe_eval₂RingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, apply_ite (eval₂ e y)]

lemma coeff_shiftedDet_card (A : Matrix n n O) :
    (shiftedDet A).coeff (Fintype.card n) = A.det := by
  have h_split : (1 + X : O[X]) • A.map C - 1 = (X : O[X]) • A.map C + (A - 1).map C := by
    rw [add_smul, one_smul, Matrix.map_sub _ (map_sub C), Matrix.map_one _ C_0 C_1]
    abel
  rw [shiftedDet, h_split, coeff_det_X_add_C_card]

/-- The polynomial `P¹(Y) = ∏_w det ((1 + Y) ρ(φ_w) - 1)`, over the primes `w` of `I` and their
conjugates; here `φ_w` is the Frobenius element of the data `d` at `v ∈ I` for `w = v`, and its
conjugate inverse for the conjugate prime. -/
def tiePolynomial {q : ℕ} (ρ : Gal(Ω/E) →* Matrix n n O) (I : Finset (FinPlace E))
    (d : FinPlace E → AuxPrimeData E q × (ι → O)) : O[X] :=
  ∏ p : I × Bool, shiftedDet (ρ (idOrConjInv p.2 (d p.1).1.frob))

omit [NumberField.IsCMField E] in
/-- For a family `h` of characters to `ℤ / q`, the twist of `ρ` by the function
`ψ_x(g) = ∏ (1 + x_j) ^ (h_j g)` is trivial at `x = 0`. So the Selmer module at the point `0`, with
the places `S` of allowed ramification and the relations `L`, is the Selmer module of `ρ` with
values in `(O / ℓ ^ M) ^ n`. -/
lemma selmerAtPoint_zero {σ : Type} [Fintype σ] {q : ℕ}
    (h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)) (S : Set (FinPlace E))
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
    selmerAtPoint ℓ M h ρ S L (RingHom.id O) (fun _ : σ ↦ 0) =
      selmerModule ρ S L (QuotSpan (ℓ ^ M : O)) := by
  have h_twist : pointTwist h (fun _ ↦ 0) (.id O) ρ = ρ := funext fun g ↦ by
    simp [pointTwist, universalChar]
  rw [selmerAtPoint, h_twist, show mapRel (.id O) '' L = L by simp [mapRel.eq_def]]

/-- For the line with index `i` (the points `x_{P₀} = Y` and `x_v = s_v Y` for `v ≠ P₀`, with
`s_v = (d v).2 i`), the point at `Y = 0` is `0`. So the Selmer module `selmerOnLine` at
`Y = 0` is the Selmer module of `ρ` with values in `(O / ℓ ^ M) ^ n`. -/
lemma selmerOnLine_zero {q : ℕ} (P₀ : FinPlace E) (J : Finset (FinPlace E))
    (d : FinPlace E → AuxPrimeData E q × (ι → O)) (i : ι) (S : Set (FinPlace E))
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) : selmerOnLine ℓ M ρ P₀ J d i (RingHom.id O) 0 S L =
      selmerModule ρ S L (QuotSpan (ℓ ^ M : O)) := by
  simp only [selmerOnLine, mul_zero, selmerAtPoint_zero]

omit [NumberField.IsCMField E] in
/-- If `ρ(g)` and `ρ(g')` agree modulo `ℓ ^ M`, then their images under `e : O →+* O'` act in the
same way on `(O' / ℓ ^ M) ^ n`. -/
lemma map_smul_eq_of_reduceModPow_eq {g g' : Gal(Ω/E)}
    (h_eq : reduceModPow ℓ M ρ g = reduceModPow ℓ M ρ g') {O' : Type} [CommRing O'] (e : O →+* O')
    (u : n → QuotSpan (ℓ ^ M : O')) : (ρ g).map e • u = (ρ g').map e • u := by
  let red : QuotSpan (ℓ ^ M : O) →+* QuotSpan (ℓ ^ M : O') := Ideal.quotientMap _ e (by simp)
  have h_red (g : Gal(Ω/E)) :
      ((ρ g).map e).map (Ideal.Quotient.mk _) = (reduceModPow ℓ M ρ g).map red := by
    ext i j
    simp [reduceModPow, red]
  rw [← map_mk_smul, ← map_mk_smul ((ρ g').map e), h_red, h_red, h_eq]

/-- If `y` divides all coordinates of the point `x`, then it divides `ψ_x(g) - 1`, where `ψ_x(g)` is
the value at `x` of the polynomial `universalChar h g = ∏ (1 + X_j) ^ (h_j g)`. -/
lemma dvd_eval_universalChar_sub_one {G σ O' : Type} [Monoid G] [Fintype σ] [CommRing O'] {q : ℕ}
    (h : σ → G →* Multiplicative (ZMod q)) {y : O'} {x : σ → O'} (hx_dvd : ∀ j : σ, y ∣ x j)
    (g : G) : y ∣ MvPolynomial.eval x (universalChar h g) - 1 := by
  rw [← Ideal.Quotient.eq_zero_iff_dvd]
  simp [eval_universalChar, (Ideal.Quotient.eq_zero_iff_dvd y _).2 (hx_dvd _)]

omit [NumberField.IsCMField E] in
/-- Let `h` be a finite family of characters `h_j` to `ℤ / q`, let `e : O →+* O'` be a change of
coefficients, and let `ψ_x(g) = ∏ (1 + x_j) ^ (h_j g)` be the value of `universalChar h g` at a
point `x` with coordinates in `O'`. If the `1 + x_j` are `q`-th roots of unity modulo `ℓ ^ M`, then
the twisted matrices `pointTwist h x e ρ g = ψ_x(g) e(ρ(g))` act on `(O' / ℓ ^ M) ^ n` through a
representation `R` over `O' / ℓ ^ M`, and `R(g)` is the scalar `ψ_x(g)` wherever `ρ(g) ≡ 1` modulo
`ℓ ^ M`. -/
lemma exists_monoidHom_smul_eq_pointTwist_smul {σ O' : Type} [Fintype σ] [CommRing O'] {q : ℕ}
    [NeZero q] (h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)) (e : O →+* O') {x : σ → O'}
    (hx_pow : ∀ j : σ, algebraMap O' (QuotSpan (ℓ ^ M : O')) (1 + x j) ^ q = 1) :
    ∃ R : Gal(Ω/E) →* Matrix n n (QuotSpan (ℓ ^ M : O')),
      (∀ (g : Gal(Ω/E)) (u : n → QuotSpan (ℓ ^ M : O')), R g • u = pointTwist h x e ρ g • u) ∧
      ∀ g : Gal(Ω/E), reduceModPow ℓ M ρ g = 1 →
        R g = algebraMap O' (QuotSpan (ℓ ^ M : O')) (MvPolynomial.eval x (universalChar h g)) •
          1 := by
  -- Modulo `ℓ ^ M`, `ψ_x` is a character `χ`; take `R = χ • ρ`.
  let B : Type := QuotSpan (ℓ ^ M : O')
  let χ : Gal(Ω/E) →* B := pointChar h (fun j ↦ algebraMap O' B (1 + x j)) hx_pow
  have hχ (g : Gal(Ω/E)) : χ g = algebraMap O' B (MvPolynomial.eval x (universalChar h g)) := by
    simp [χ, eval_universalChar]
  let red : QuotSpan (ℓ ^ M : O) →+* B := Ideal.quotientMap _ e (by simp)
  let R : Gal(Ω/E) →* Matrix n n B := twistRep red χ (reduceModPow ℓ M ρ)
  have hR (g : Gal(Ω/E)) : R g = χ g • (reduceModPow ℓ M ρ g).map red := rfl
  refine ⟨R, fun g u ↦ ?_, fun g hg ↦ by simp [hR, hχ, hg, B]⟩
  rw [← map_mk_smul]
  congr 1
  ext j k
  simp [hR, hχ, pointTwist, reduceModPow, red, B]

/-- Let `v ∤ ℓ` be a prime of the CM field `E` of norm `≡ 1` modulo `ℓ ^ N`, and let `a` consist of
a place over `v`, a Frobenius element `φ`, the tame generator `γ` and a character
(`IsAuxPrimeDataAt`). Let `S` contain `v` and its complex conjugate `star v`, let `ρ` be trivial
on inertia above `S` near `1`, and let each element of inertia above `S` act by a scalar `α` with
`∑ j < ℓ ^ N, α ^ j = 0`. Then every locally constant cocycle `c` has
`(φ_b - 1) c(γ_b) = (γ_b - 1) c(φ_b)`. Here `g_b = idOrConjInv b g` is `g` for `b = true` and
`(τ g τ)⁻¹` for `b = false`, where `τ = cmConj` is the chosen complex conjugation of `Ω`. -/
lemma sub_one_smul_eq_of_isAuxPrimeDataAt {B : Type} [AddCommGroup B] [Module O B]
    {c : Gal(Ω/E) → n → B} (hc : ∀ g h : Gal(Ω/E), c (g * h) = c g + ρ g • c h)
    (hc_lc : IsLocallyConstant c) {S : Set (FinPlace E)}
    (h_open : ∀ᶠ g : Gal(Ω/E) in nhds 1, g ∈ inertiaAbove S → ρ g = 1)
    (h_scalar : ∀ g ∈ inertiaAbove S, ∃ α : O, ρ g = α • 1 ∧ ∑ j ∈ range (ℓ ^ N), α ^ j = 0)
    {v : FinPlace E} {a : AuxPrimeData E (ℓ ^ N)}
    (ha : IsAuxPrimeDataAt (placesDividing E ℓ) v a) (hv : v ∈ S) (hv_star : star v ∈ S)
    (b : Bool) :
    (ρ (idOrConjInv b a.frob) - 1) • c (idOrConjInv b a.tameGenerator) =
      (ρ (idOrConjInv b a.tameGenerator) - 1) • c (idOrConjInv b a.frob) := by
  have h_tame {w : FinPlace E} {A : ClosurePlace} (hA : IsPlaceOver A w) (hw : w ∈ S)
      (hℓ : w ∉ placesDividing E ℓ) {φ γ : Gal(Ω/E)} (hφ : IsFrob A v.q φ ∨ IsFrob A v.q φ⁻¹)
      (hγ : γ ∈ inertiaGroup Gal(Ω/E) A) : (ρ φ - 1) • c γ = (ρ γ - 1) • c φ :=
    sub_one_smul_eq_of_tame hc hA hc_lc (h_open.mono fun g hg hgA ↦ hg ⟨w, hw, A, hA, hgA⟩)
      (q := ℓ ^ N) (by simp [hA.valuation_natCast_eq_one_iff.2 hℓ])
      (fun g hgA ↦ h_scalar g ⟨w, hw, A, hA, hgA⟩) ha.norm_modEq hφ hγ
  cases b
  · -- At the conjugate prime, `φ_w` is the inverse of a Frobenius element.
    exact h_tame ha.isPlaceOver.conjPlace_star hv_star (by simpa using ha.notMem)
      (.inr (by simpa [idOrConjInv] using ha.isFrob.conjPlace_conjGal))
      (inv_mem (conjGal_mem_inertiaGroup_iff.2 ha.tame_gen.left))
  · exact h_tame ha.isPlaceOver hv ha.notMem (.inl ha.isFrob) ha.tame_gen.left

/-- Let `J` be a finite set of primes of the CM field `E` that lie, with their conjugates, outside
`S₀`, and let `d` attach to each `u ∈ J` a Frobenius element `φ_u`, a tame generator `γ_u` of
inertia and a character `λ_u` to `ℤ / ℓ ^ N`. This is the part of `hp` (`IsTiedPrimes`) that is
used; its conditions on the first prime `P₀`, the set `W`, the properties `V` and the slopes play no
role. Let `ρ` modulo `ℓ ^ M` (`reduceModPow`) be trivial on inertia outside `S₀`. Let `e : O →+* O'`
be a ring map, let `x` be a point over `O'` with coordinates divisible by `y`, and let
`∑ j < ℓ ^ N, α ^ j` vanish modulo `ℓ ^ M` whenever `α ≡ 1` modulo `y`. Let `g` act through the
twist `pointTwist`, the matrix `ψ_x(g) e(ρ(g))` with `ψ_x(g) = ∏_{u ∈ J} (1 + x_u) ^ (λ_u g)`, and
let `z` be a locally constant cocycle in `(O' / ℓ ^ M) ^ n` for this twist, unramified outside `S`
and obeying the linear relations `L` (`selmerAtPoint`). Then `(φ_w - 1) z(γ_w) = (γ_w - 1) z(φ_w)`
for `w` a prime `v` of `J` (`b = true`) or its conjugate (`b = false`), where `φ_w`, `γ_w` are
`φ_v`, `γ_v` or their conjugate inverses (`idOrConjInv`). -/
lemma IsTiedPrimes.frob_sub_one_smul_eq [ThePrime ℓ] (hp : IsTiedPrimes ℓ S₀ V W N P₀ J d)
    (h_unr : ∀ g ∈ inertiaAbove S₀ᶜ, reduceModPow ℓ M ρ g = 1) {O' : Type} [CommRing O']
    (e : O →+* O') {y : O'}
    (h_geom_sum : ∀ α : O', y ∣ α - 1 → (ℓ ^ M : O') ∣ ∑ j ∈ range (ℓ ^ N), α ^ j)
    {x : J → O'} (hx_dvd : ∀ w : J, y ∣ x w)
    {S : Set (FinPlace E)} {L : Set (Gal(Ω/E) →₀ Matrix n n O)}
    {z : Gal(Ω/E) → n → QuotSpan (ℓ ^ M : O')}
    (hz : z ∈ selmerAtPoint ℓ M (fun v : J ↦ (d v).1.character) ρ S L e x) (v : J) (b : Bool) :
    (pointTwist (fun u : J ↦ (d u).1.character) x e ρ (idOrConjInv b (d v).1.frob) - 1) •
        z (idOrConjInv b (d v).1.tameGenerator) =
      (pointTwist (fun u : J ↦ (d u).1.character) x e ρ (idOrConjInv b (d v).1.tameGenerator) - 1) •
        z (idOrConjInv b (d v).1.frob) := by
  -- Modulo `ℓ ^ M` the twist is a representation `R`. Inertia off `S₀` acts by scalars `≡ 1`
  -- modulo `y`, and trivially near the identity.
  let B : Type := QuotSpan (ℓ ^ M : O')
  let lam (w : J) : Gal(Ω/E) →* Multiplicative (ZMod (ℓ ^ N)) := (d w).1.character
  have h_sum {α : O'} (hα : y ∣ α - 1) : ∑ j ∈ range (ℓ ^ N), algebraMap O' B α ^ j = 0 := by
    simpa [B] using (Ideal.Quotient.eq_zero_iff_dvd _ _).2 (h_geom_sum α hα)
  have hx_pow (w : J) : algebraMap O' B (1 + x w) ^ ℓ ^ N = 1 := by
    rw [← sub_eq_zero, ← geom_sum_mul, h_sum (by simp [hx_dvd]), zero_mul]
  obtain ⟨R, hR_smul, hR_scalar⟩ : ∃ R : Gal(Ω/E) →* Matrix n n B,
      (∀ (g : Gal(Ω/E)) (u : n → B), R g • u = pointTwist lam x e ρ g • u) ∧
      ∀ g : Gal(Ω/E), reduceModPow ℓ M ρ g = 1 →
        R g = algebraMap O' B (MvPolynomial.eval x (universalChar lam g)) • 1 :=
    exists_monoidHom_smul_eq_pointTwist_smul lam e hx_pow
  obtain ⟨hz_cocycle, -, -, hz_lc⟩ := mem_selmerModule_iff.1 hz
  have hc (g g' : Gal(Ω/E)) : z (g * g') = z g + R g • z g' := by rw [hR_smul, hz_cocycle]
  have h_open : ∀ᶠ g : Gal(Ω/E) in nhds 1, g ∈ inertiaAbove S₀ᶜ → R g = 1 := by
    have h_near : ∀ᶠ g : Gal(Ω/E) in nhds 1, ∀ u : J, lam u g = lam u 1 :=
      Filter.eventually_all.2 fun u ↦ (hp.isAuxPrimeDataAt u u.2).isLocallyConstant.eventually_eq 1
    filter_upwards [h_near] with g hg hg_inertia
    simp [hR_scalar g (h_unr g hg_inertia), eval_universalChar, hg]
  have h_scalar (g : Gal(Ω/E)) (hg : g ∈ inertiaAbove S₀ᶜ) :
      ∃ α : B, R g = α • 1 ∧ ∑ j ∈ range (ℓ ^ N), α ^ j = 0 :=
    ⟨_, hR_scalar g (h_unr g hg), h_sum (dvd_eval_universalChar_sub_one lam hx_dvd g)⟩
  obtain ⟨hv_off, -, -, hv_star_off⟩ := hp.auxiliary v v.property
  -- Tame inertia at `v` or at its conjugate, both off `S₀`, gives the relation for `R`.
  simpa only [sub_smul, one_smul, hR_smul] using
    sub_one_smul_eq_of_isAuxPrimeDataAt hc hz_lc h_open h_scalar (hp.isAuxPrimeDataAt v v.property)
      hv_off hv_star_off b

/-- Let `J` be a finite set of primes of the CM field `E` that lie, with their conjugates, outside
`S₀`. Let `d` attach to each `v ∈ J` a Frobenius element `φ_v`, a tame generator `γ_v` of inertia, a
character `λ_v` to `ℤ / ℓ ^ N` and a slope `s_v = (d v).2 i` in `O` for the index `i : ι`. The
hypothesis `hp` (`IsTiedPrimes`) says this, and further that `P₀ ∈ J` is a first prime, that for
`v ≠ P₀` the value `λ_u(φ_v)` is `1` for `u = P₀` and `0` otherwise, and that the property `V i`
holds at `φ_v` and its conjugate inverse if `s_v ≠ 0`.

Let `ρ` modulo `ℓ ^ M` be trivial on inertia outside `S₀` and at the elements with the property
`V i`, and let `∑ j < ℓ ^ N, α ^ j` vanish modulo `ℓ ^ M` whenever `α ≡ 1` modulo `y`. Let `z` be a
locally constant cocycle for the twist of `ρ` at the point `x_{P₀} = y`, `x_v = e(s_v) y`,
unramified outside `S` and obeying the linear relations `L` (`selmerOnLine`). Then the matrix
`(1 + y) e(ρ(φ_w)) - 1` kills `z(γ_w) - e(s_v) z(φ_w)`. Here `w` is a prime `v` of `J` (`b = true`)
or its conjugate (`b = false`), where `φ_w`, `γ_w` are `φ_v`, `γ_v` or their conjugate inverses
(`idOrConjInv`), and `v` may be `P₀` only if `y = 0`. -/
lemma IsTiedPrimes.frob_sub_one_smul_tie_eq_zero_of_selmerOnLine [ThePrime ℓ]
    (hp : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0) (i : ι)
    (h_unr : ∀ g ∈ inertiaAbove S₀ᶜ, reduceModPow ℓ M ρ g = 1)
    (h_triv_of_V : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M ρ g = 1) {O' : Type} [CommRing O']
    (e : O →+* O') {y : O'}
    (h_geom_sum : ∀ α : O', y ∣ α - 1 → (ℓ ^ M : O') ∣ ∑ j ∈ range (ℓ ^ N), α ^ j)
    {S : Set (FinPlace E)} {L : Set (Gal(Ω/E) →₀ Matrix n n O)}
    {z : Gal(Ω/E) → n → QuotSpan (ℓ ^ M : O')}
    (hz : z ∈ selmerOnLine ℓ M ρ P₀ J d i e y S L) (v : J)
    (hy_zero_of_eq_first : ↑v = P₀ → y = 0) (b : Bool) :
    ((1 + y) • (ρ (idOrConjInv b (d v).1.frob)).map e - 1) •
      (z (idOrConjInv b (d v).1.tameGenerator) - e ((d v).2 i) • z (idOrConjInv b (d v).1.frob)) =
        0 := by
  let x (w : J) : O' := e (lineDirection P₀ J d i w) * y
  let lam (w : J) : Gal(Ω/E) →* Multiplicative (ZMod (ℓ ^ N)) := (d w).1.character
  let φ : Gal(Ω/E) := idOrConjInv b (d v).1.frob
  let γ : Gal(Ω/E) := idOrConjInv b (d v).1.tameGenerator
  -- We have `ψ_x(γ) = 1 + s y` and `ψ_x(φ) = 1 + y`. At the first prime `y = 0`, and both values
  -- are `1`.
  have hψγ : MvPolynomial.eval x (universalChar lam γ) = 1 + e ((d v).2 i) * y := by
    by_cases hvP : ↑v = P₀
    · simp [universalChar, x, hy_zero_of_eq_first hvP]
    · simp [γ, lam, hp.universalChar_tame_gen hN v, x, lineDirection, hvP]
  have hψφ : MvPolynomial.eval x (universalChar lam φ) = 1 + y := by
    by_cases hvP : ↑v = P₀
    · simp [universalChar, x, hy_zero_of_eq_first hvP]
    · simp [φ, lam, hp.universalChar_frob hN v.property hvP, x, lineDirection]
  have h_trivial {g : Gal(Ω/E)} (hg : reduceModPow ℓ M ρ g = 1) (u : n → QuotSpan (ℓ ^ M : O')) :
      (ρ g).map e • u = u := by
    simpa using map_smul_eq_of_reduceModPow_eq (hg.trans (map_one _).symm) e u
  obtain ⟨hv_off, -, -, hv_star_off⟩ := hp.auxiliary v v.property
  have hγ : reduceModPow ℓ M ρ γ = 1 :=
    have hd : IsAuxPrimeDataAt (placesDividing E ℓ) v (d v).1 := hp.isAuxPrimeDataAt v v.property
    h_unr γ (idOrConjInv_mem_inertiaAbove hd.isPlaceOver hd.tame_gen.left
      ⟨hv_off, hv_star_off⟩ b)
  let Φ : Matrix n n O' := (1 + y) • (ρ φ).map e
  have hγ_act (u : n → QuotSpan (ℓ ^ M : O')) :
      pointTwist lam x e ρ γ • u = (1 + e ((d v).2 i) * y) • u := by
    rw [pointTwist, hψγ, smul_assoc, h_trivial hγ]
  have hφ_twist : pointTwist lam x e ρ φ = Φ := by rw [pointTwist, hψφ]
  have h_commute : (Φ - 1) • z γ = (e ((d v).2 i) * y) • z φ := by
    have h_eq : (pointTwist lam x e ρ φ - 1) • z γ = (pointTwist lam x e ρ γ - 1) • z φ :=
      hp.frob_sub_one_smul_eq h_unr e h_geom_sum (fun w : J ↦ dvd_mul_left y _) hz v b
    simpa [hφ_twist, sub_smul, hγ_act, add_smul] using h_eq
  -- Moreover `s (φ - 1)` acts on `z φ` as `s y`, as `γ - 1` does: if `s ≠ 0` then `ρ(φ) ≡ 1`
  -- modulo `ℓ ^ M`.
  have h_slope : (e ((d v).2 i) * y) • z φ = e ((d v).2 i) • (Φ - 1) • z φ := by
    by_cases hs : (d v).2 i = 0
    · simp [hs]
    · simp [Φ, sub_smul, add_smul, mul_smul,
        h_trivial (h_triv_of_V φ (hp.apply_idOrConjInv_of_slope_ne_zero v.property hs b))]
  change (Φ - 1) • (z γ - e ((d v).2 i) • z φ) = 0
  rw [smul_sub, h_commute, smul_comm, h_slope, sub_self]

/-- Let `J` be a finite set of primes of the CM field `E` that lie, with their conjugates, outside
`S₀`. Let `d` attach to each `v ∈ J` a Frobenius element `φ_v`, a tame generator `γ_v` of inertia, a
character to `ℤ / ℓ ^ N` and a slope `s_v = (d v).2 i` in `O` for the index `i : ι`. The hypothesis
`hp` (`IsTiedPrimes`) says this, singles out a first prime `P₀ ∈ J` with Frobenius element in `W`,
fixes the values of the characters at the `φ_v` with `v ≠ P₀`, and gives the property `V i` at `φ_v`
and its conjugate inverse if `s_v ≠ 0`.

Let `ρ` modulo `ℓ ^ M` be trivial on inertia outside `S₀` and at the elements with the property
`V i`, and let `∑ j < ℓ ^ N, α ^ j` vanish modulo `ℓ ^ M` whenever `α ≡ 1` modulo `y`. Consider the
locally constant cocycles `z` for the twist of `ρ` at the point `x_{P₀} = y`, `x_v = e(s_v) y`,
unramified outside `S` and obeying the linear relations `L` (`selmerOnLine`). Let `I ⊆ J` contain
`P₀` only if `y = 0`, and let `w` run over the primes `v` of `I` and their conjugates, where `φ_w`,
`γ_w` are `φ_v`, `γ_v` or conjugate inverses (`idOrConjInv`). The quotient by the cocycles with
`z(γ_w) = e(s_v) z(φ_w)` for all `w` (`tieRelations`) has length (`relLength`) at most the sum of
the lengths of the kernels of the `(1 + y) e(ρ(φ_w)) - 1` on `(O' / ℓ ^ M) ^ n`. -/
lemma IsTiedPrimes.relLength_tied_le_sum_ker [ThePrime ℓ]
    (hp : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0)
    (i : ι) (h_unr : ∀ g ∈ inertiaAbove S₀ᶜ, reduceModPow ℓ M ρ g = 1)
    (h_triv_of_V : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M ρ g = 1) {O' : Type} [CommRing O']
    (e : O →+* O') {y : O'}
    (h_geom_sum : ∀ α : O', y ∣ α - 1 → (ℓ ^ M : O') ∣ ∑ j ∈ range (ℓ ^ N), α ^ j)
    (S : Set (FinPlace E)) (L : Set (Gal(Ω/E) →₀ Matrix n n O))
    {I : Finset (FinPlace E)} (hI : I ⊆ J) (hy_zero_of_first_mem : P₀ ∈ I → y = 0) :
    relLength (selmerOnLine ℓ M ρ P₀ J d i e y S L)
        (selmerOnLine ℓ M ρ P₀ J d i e y S (L ∪ tieRelations I d i)) ≤
      ∑ v : I, ∑ b : Bool, length O' (LinearMap.ker
        (((1 + y) • (ρ (idOrConjInv b (d v).1.frob)).map e - 1) • 1 :
          End O' (n → QuotSpan (ℓ ^ M : O')))) := by
  let B : Type := QuotSpan (ℓ ^ M : O')
  let Sel (L' : Set (Gal(Ω/E) →₀ Matrix n n O)) : Submodule O' (Gal(Ω/E) → n → B) :=
    selmerOnLine ℓ M ρ P₀ J d i e y S L'
  let φ (p : I × Bool) : Gal(Ω/E) := idOrConjInv p.2 (d p.1).1.frob
  let γ (p : I × Bool) : Gal(Ω/E) := idOrConjInv p.2 (d p.1).1.tameGenerator
  let tie (p : I × Bool) : (Gal(Ω/E) → n → B) →ₗ[O'] n → B :=
    LinearMap.proj (γ p) - e ((d p.1).2 i) • LinearMap.proj (φ p)
  have h_tied : Sel L ⊓ ⨅ p, (tie p).ker ≤ Sel (L ∪ tieRelations I d i) := by
    rintro z ⟨hz, hz_tie⟩
    obtain ⟨h_cocycle, h_unram, hL, h_lc⟩ := mem_selmerModule_iff.1 hz
    refine mem_selmerModule_iff.2 ⟨h_cocycle, h_unram, mem_obeying.2 ?_, h_lc⟩
    rintro _ ⟨f, hf | ⟨p, rfl⟩, rfl⟩
    · exact mem_obeying.1 hL _ ⟨f, hf, rfl⟩
    · simpa [tie, mapRel, Finsupp.mapRange_sub', Matrix.map_smul'] using
        (Submodule.mem_iInf _).1 hz_tie p
  calc
    relLength (Sel L) (Sel (L ∪ tieRelations I d i)) ≤ relLength (Sel L) (⨅ p, (tie p).ker) :=
      relLength_le_of_mapsTo LinearMap.id (fun _ hz ↦ hz) fun z hz hz' ↦ h_tied ⟨hz, hz'⟩
    _ ≤ ∑ p : I × Bool, relLength (Sel L) (tie p).ker := relLength_iInf_le _ _
    _ = ∑ v : I, ∑ b : Bool, relLength (Sel L) (tie (v, b)).ker := Fintype.sum_prod_type _
    _ ≤ _ := sum_le_sum fun v _ ↦ sum_le_sum fun b _ ↦ by
      -- The image of `Sel L` under `tie (v, b)` lies in the kernel.
      have hy_zero_of_eq_first (h_first : ↑v = P₀) : y = 0 :=
        hy_zero_of_first_mem (by simp [← h_first])
      rw [relLength_ker]
      refine length_mono ?_
      rintro _ ⟨z, hz, rfl⟩
      exact hp.frob_sub_one_smul_tie_eq_zero_of_selmerOnLine hN i h_unr h_triv_of_V e h_geom_sum hz
        ⟨v, hI v.property⟩ hy_zero_of_eq_first b

open scoped Classical in
/-- Let `J` be a finite set of primes of the CM field `E` that lie, with their conjugates, outside
`S₀`. Let `d` attach to each `v ∈ J` a Frobenius element `φ_v`, a tame generator `γ_v` of inertia, a
character to `ℤ / ℓ ^ N` and a slope `s_v = (d v).2 i` in `O` for the index `i : ι`. The hypothesis
`hp` (`IsTiedPrimes`) says this, singles out a first prime `P₀ ∈ J` with Frobenius element in `W`,
fixes the values of the characters at the `φ_v` with `v ≠ P₀`, and gives the property `V i` at `φ_v`
and its conjugate inverse if `s_v ≠ 0`.

Let `ρ` modulo `ℓ ^ M` be trivial on inertia outside `S₀` and at the elements with the property
`V i`, and let `∑ j < ℓ ^ N, α ^ j` vanish modulo `ℓ ^ M` whenever `α ≡ 1` modulo `y`. Consider the
locally constant cocycles `z` for the twist of `ρ` at the point `x_{P₀} = y`, `x_v = e(s_v) y`,
unramified outside `S` and obeying the linear relations `L` (`selmerOnLine`). Adding the ties
`z(γ_w) = e(s_v) z(φ_w)` for `w` a prime `v ≠ P₀` of `J` or its conjugate (`tieRelations`) lowers
the length by at most the normalised valuation `addVal` of `tiePolynomial ρ (J.erase P₀) d`, with
coefficients mapped by `e`, evaluated at `y`. -/
lemma IsTiedPrimes.relLength_tied_le [ThePrime ℓ]
    (hp : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0) (i : ι)
    (h_unr : ∀ g ∈ inertiaAbove S₀ᶜ, reduceModPow ℓ M ρ g = 1)
    (h_triv_of_V : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M ρ g = 1) {O' : Type} [CommRing O']
    [DVR O'] (e : O →+* O') {y : O'}
    (h_geom_sum : ∀ α : O', y ∣ α - 1 → (ℓ ^ M : O') ∣ ∑ j ∈ range (ℓ ^ N), α ^ j)
    (S : Set (FinPlace E)) (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
    relLength (selmerOnLine ℓ M ρ P₀ J d i e y S L)
        (selmerOnLine ℓ M ρ P₀ J d i e y S (L ∪ tieRelations (J.erase P₀) d i)) ≤
      addVal O' ((tiePolynomial ρ (J.erase P₀) d).eval₂ e y) := by
  let Φ (v : J.erase P₀) (b : Bool) : Matrix n n O' :=
    (1 + y) • (ρ (idOrConjInv b (d v).1.frob)).map e - 1
  calc
    _ ≤ ∑ v, ∑ b, length O' (LinearMap.ker (Φ v b • 1 : End O' (n → QuotSpan (ℓ ^ M : O')))) :=
      hp.relLength_tied_le_sum_ker hN i h_unr h_triv_of_V e h_geom_sum S L (J.erase_subset P₀)
        fun h ↦ absurd h (J.notMem_erase P₀)
    _ ≤ ∑ v, ∑ b, addVal O' (Φ v b).det :=
      sum_le_sum fun v _ ↦ sum_le_sum fun b _ ↦ length_ker_le_addVal_det (Φ v b) _
    _ = addVal O' ((tiePolynomial ρ (J.erase P₀) d).eval₂ e y) := by
      simp only [tiePolynomial, eval₂_finsetProd, eval₂_shiftedDet, addVal_prod,
        Fintype.sum_prod_type, Φ]

/-- Release of the first prime. Let `J` be a finite set of primes of the CM field `E` that lie, with
their conjugates, outside `S₀`. Let `d` attach to each `v ∈ J` a Frobenius element, a tame generator
of inertia, a character to `ℤ / ℓ ^ N` and a slope `(d v).2 i` in `O` for the index `i : ι`. The
hypothesis `hp` (`IsTiedPrimes`) says this, singles out a first prime `P₀ ∈ J` of slope `0` with
Frobenius element `φ₀` in `W`, and gives the property `V i` at the Frobenius elements of the primes
with nonzero slope.

Let `ρ` modulo `ℓ ^ M` be trivial on inertia outside `S₀` and at the elements with the property
`V i`, let `M ≤ N`, and let `φ₀` and its conjugate inverse `φ₀^{-c}` (`idOrConjInv`) act modulo
`ℓ ^ M` as `g₀` and `g₀^{-c}`. Consider the locally constant cocycles `z` for `ρ` in
`(O / ℓ ^ M) ^ n`, unramified outside `S` and obeying the linear relations `L` (`selmerModule`). The
relations `tieRelations {P₀} d i` say `z(γ₀) = 0 = z(γ₀^{-c})` for the tame generator `γ₀` at `P₀`.
Adding them lowers the length by at most `∑ v(det (ρ(g) - 1))`, over `g = g₀, g₀^{-c}` (`relLength`
is the length of the quotient, `v = addVal` the normalised valuation). -/
lemma IsTiedPrimes.relLength_tieRelations_le_sum_addVal_det [ThePrime ℓ] [DVR O]
    (hp : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN : N ≠ 0)
    (i : ι) (h_unr : ∀ g ∈ inertiaAbove S₀ᶜ, reduceModPow ℓ M ρ g = 1)
    (h_triv_of_V : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M ρ g = 1) (hMN : M ≤ N) {g₀ : Gal(Ω/E)}
    (h_frob_first : ∀ b : Bool, reduceModPow ℓ M ρ (idOrConjInv b (d P₀).1.frob) =
      reduceModPow ℓ M ρ (idOrConjInv b g₀))
    (S : Set (FinPlace E)) (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
    relLength (selmerModule ρ S L (QuotSpan (ℓ ^ M : O)))
        (selmerModule ρ S (L ∪ tieRelations {P₀} d i) (QuotSpan (ℓ ^ M : O))) ≤
      ∑ b : Bool, addVal O (ρ (idOrConjInv b g₀) - 1).det := by
  have h_geom_sum (α : O) (hα : 0 ∣ α - 1) : (ℓ ^ M : O) ∣ ∑ j ∈ range (ℓ ^ N), α ^ j := by
    obtain rfl : α = 1 := sub_eq_zero.1 (zero_dvd_iff.1 hα)
    simpa using pow_dvd_pow (ℓ : O) hMN
  let K (A : Matrix n n O) : Submodule O (n → QuotSpan (ℓ ^ M : O)) :=
    LinearMap.ker ((A - 1) • 1 : End O (n → QuotSpan (ℓ ^ M : O)))
  let Φ (b : Bool) : Matrix n n O :=
    (1 + 0 : O) • (ρ (idOrConjInv b (d P₀).1.frob)).map (RingHom.id O)
  have h_ker (b : Bool) : K (Φ b) ≤ K (ρ (idOrConjInv b g₀)) := by
    intro u hu
    have h_eq : ρ (idOrConjInv b (d P₀).1.frob) • u = ρ (idOrConjInv b g₀) • u := by
      simpa using map_smul_eq_of_reduceModPow_eq (h_frob_first b) (RingHom.id O) u
    simpa [K, Φ, sub_smul, h_eq] using hu
  calc
    _ ≤ ∑ b : Bool, length O (K (Φ b)) := by
      -- At `y = 0`, where the point of the line is `0`, the two tie maps take their values in the
      -- kernels of `ρ(φ₀) - 1` and `ρ(φ₀^{-c}) - 1`.
      simpa [K, Φ, selmerOnLine_zero] using
        hp.relLength_tied_le_sum_ker hN i h_unr h_triv_of_V (RingHom.id O) h_geom_sum S L
          (singleton_subset_iff.2 hp.first_mem) fun _ ↦ rfl
    _ ≤ ∑ b : Bool, length O (K (ρ (idOrConjInv b g₀))) :=
      sum_le_sum fun b _ ↦ length_mono (h_ker b)
    _ ≤ _ := sum_le_sum fun b _ ↦ length_ker_le_addVal_det _ _

end Line

end New.Selmer

end
end
end

/-!
# Restriction to a line

For Selmer data and Stickelberger systems there is an integer `s₀` such that, for each radius `r`
with `0 < r` and `s₀ r < 1` and each large `N`, we find auxiliary primes `𝔮` and, for each datum and
each system, a polynomial `P` in variables `X_𝔮`. At a point `x = (ζ_𝔮 - 1)_𝔮` given by `ℓ ^ N`-th
roots of unity, `v(P(x))` bounds the length of the twisted Selmer group of a datum `T` if it is less
than `β_T + 1`, and `P(x)` is the twisted value of a system. At some point with coordinates of
valuation at least `r`, the valuation of `P` is at most `β + s₀ r`, where `β` is the number of the
datum or system. For a datum this point is taken on the line `X_{𝔮₀} = Y`, `X_𝔮 = s_𝔮 Y`, where `𝔮₀`
is the first prime and the `s_𝔮` are the slopes of the datum at the other primes.

For a datum, `v(P(x))` is bounded by `v(P⁰(y)) + v(P¹(y))` at the point `x` of the line with
`Y = y`. Here `P⁰` is the restriction to the line of a minor for the tied module that is sharp at
`0`, so that `v(P⁰(0)) ≤ β_T`, the polynomial `P¹` bounds the failure to be tied, and `y` is generic
for both.

* `New.Selmer.SelmerDatum.TwistedLengthLe`: a bound for the length of the twisted Selmer group.
* `New.Selmer.SelmerDatum.exists_boundsSelmer_and_eval_dvd`,
  `New.Selmer.SelmerDatum.exists_boundsSelmer_ellVal_eval_le`: the choice of `P⁰`, of `y` and of the
  polynomial `P` of a datum.
* `New.Selmer.IsTorsionLevel`: the power `ℓ ^ M` modulo which the Selmer modules are computed.
* `New.Selmer.TwistPolynomials`, `New.Selmer.exists_twistPolynomials`: the primes, polynomials and
  points.

Letters: for a set of tied primes (`New.Selmer.IsTiedPrimes`), `J` is the set `Q` of all auxiliary
primes, `P₀ ∈ J` is the first prime `𝔮₀`, and `d` attaches to `v ∈ J` a Frobenius element, a tame
generator, the homomorphism `λ_v = (d v).1.character` to `ℤ / ℓ ^ N` and the slopes `(d v).2 i`.

Notions from other files:
* `New.selmerModule ρ S L B`: the locally constant cocycles for `ρ` with values in `B ^ n` that are
  unramified outside `S` and obey the linear relations `L`. The coefficients `B` are
  `New.QuotSpan a = O / a` or `New.Selmer.DivisibleQuot O = Frac(O) / O`.
* `New.Selmer.SelmerDatum`: a lattice `T` with local conditions and the number `β_T`;
  `New.Selmer.SelmerDatum.tiedSelmer` is its tied Selmer group.
* `New.Selmer.StickelbergerSystem`: elements `Θ_Q` of the group rings of class groups `Cl_Q` with a
  norm relation, and the number `β`.
* `New.CoeffRing`: rings of integers of finite Galois extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`;
  `New.CoeffRing.normLength` scales lengths so that `O / ℓ` has length `1`.

## Relation to the literature

See `New.Congruences.Selmer.TwistingTheorem` for related work.
-/

@[expose] public section

noncomputable section

namespace New.Selmer

section Levels

open Module Submodule Ideal IsDiscreteValuationRing

variable {O : Type} [CommRing O] [DVR O]
  {E n : Type} [Field E] [EmbeddedNumberField E] [Fintype n] [DecidableEq n]

/-- The Selmer group of locally constant cocycles for `ρ` that are unramified outside `S` and obey
`L`, with coefficients in `DivisibleQuot O = Frac(O) / O`, is a torsion module: a member `z` takes
finitely many values, so a common denominator kills it. -/
lemma exists_smul_eq_zero_of_mem_selmerModule (ρ : Gal(Ω/E) → Matrix n n O) (S : Set (FinPlace E))
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) (z : selmerModule ρ S L (DivisibleQuot O)) :
    ∃ a : O, a ≠ 0 ∧ a • z = 0 := by
  obtain ⟨z, hz⟩ := z
  choose d hd_ne hd using exists_smul_eq_zero_divisibleQuot (O := O)
  obtain ⟨-, -, -, h_const⟩ := mem_selmerModule_iff.1 hz
  -- The product of the denominators `d y` of all coordinates `y` of all values of `z`.
  let a : O := ∏ u ∈ h_const.range_finite.toFinset, ∏ i : n, d (u i)
  have ha : a ≠ 0 := by simp [a, Finset.prod_ne_zero_iff, hd_ne]
  have h_smul (g : Gal(Ω/E)) (i : n) : a • z g i = 0 := by
    obtain ⟨c, hc⟩ : d (z g i) ∣ a :=
      calc d (z g i) ∣ ∏ j : n, d (z g j) := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
        _ ∣ a := Finset.dvd_prod_of_mem (fun u : n → DivisibleQuot O ↦ ∏ j : n, d (u j)) (by simp)
    rw [hc, mul_comm, mul_smul, hd, smul_zero]
  exact ⟨a, ha, Subtype.ext (funext₂ h_smul)⟩

/-- Let `O` be a discrete valuation ring with valuation `v = addVal O` and let `a ∈ O` be nonzero.
Consider the Selmer groups of locally constant cocycles for `ρ` that are unramified outside `S` and
obey the relations `L`. If the group with coefficients in `QuotSpan a = O / a` has length less than
`v(a)`, then the group with coefficients in `DivisibleQuot O = Frac(O) / O` is no longer than it,
because `a` kills the second group. -/
lemma length_selmerModule_divisibleQuot_le (ρ : Gal(Ω/E) → Matrix n n O) (S : Set (FinPlace E))
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) {a : O} (ha : a ≠ 0)
    (h_lt : length O (selmerModule ρ S L (QuotSpan a)) < addVal O a) :
    length O (selmerModule ρ S L (DivisibleQuot O)) ≤
      length O (selmerModule ρ S L (QuotSpan a)) := by
  rw [← length_torsionBy_selmerModule_divisibleQuot ρ S L ha] at h_lt ⊢
  have h_top : torsionBy O (selmerModule ρ S L (DivisibleQuot O)) a = ⊤ := by_contra fun h_ne ↦
    h_lt.not_ge (addVal_le_length_torsionBy (exists_smul_eq_zero_of_mem_selmerModule ρ S L) h_ne)
  rw [h_top, length_top]

end Levels

open Finset Filter Module MvPolynomial Subalgebra

open scoped NNReal ENNReal NNRat

section Choice

variable {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  {S₀ : Finset (FinPlace E)} {g₀ : Gal(Ω/E)}

namespace SelmerDatum

/-- The Selmer group `Sel_Q(T ψ)` modulo `a` of a Selmer datum `T`, for a character `ψ` with values
in a ring `O'` over `O` (by the map `e`): the cocycles in `T ψ ⊗ O' / a` that vanish at the element
`γ_* = T.γ`, are unramified outside `S ∪ Q ∪ Q̄`, where `S = T.places`, and satisfy the
local conditions of `T`. If `ψ(γ_*) = 1`, each class has exactly one cocycle that vanishes at
`γ_*`. -/
def twistedSelmer {O O' n : Type} [CommRing O] [PadicIntegerRing O ℓ] [CommRing O'] [Fintype n]
    [DecidableEq n] (T : SelmerDatum ℓ S₀ g₀ O n) (Q : Finset (FinPlace E)) (e : O →+* O')
    (ψ : Gal(Ω/E) →* O') (a : O') : Submodule O' (Gal(Ω/E) → n → QuotSpan a) :=
  selmerModule (twistRep e ψ T.ρ) (unionWithConj T.places Q) (mapRel e '' T.classRelations)
    (QuotSpan a)

/-- The Selmer group `Sel_Q(T ψ)` of a Selmer datum `T` with divisible coefficients, for a character
`ψ` with values in a discrete valuation ring `O'` over `O` (by the map `e`): the cocycles in
`T ψ ⊗ Frac(O') / O'` that vanish at `γ_* = T.γ`, are unramified outside `S ∪ Q ∪ Q̄`,
where `S = T.places`, and satisfy the local conditions of `T`. -/
def divisibleSelmer {O O' n : Type} [CommRing O] [PadicIntegerRing O ℓ] [CommRing O']
    [Fintype n] [DecidableEq n] (T : SelmerDatum ℓ S₀ g₀ O n) (Q : Finset (FinPlace E))
    (e : O →+* O') (ψ : Gal(Ω/E) →* O') : Submodule O' (Gal(Ω/E) → n → DivisibleQuot O') :=
  selmerModule (twistRep e ψ T.ρ) (unionWithConj T.places Q) (mapRel e '' T.classRelations)
    (DivisibleQuot O')

/-- The length over `O'` of the Selmer group `Sel_Q(T ψ)` with coefficients in `Frac(O') / O'`. -/
def divisibleLength {O O' n : Type} [CommRing O] [PadicIntegerRing O ℓ] [CommRing O']
    [Fintype n] [DecidableEq n] (T : SelmerDatum ℓ S₀ g₀ O n) (Q : Finset (FinPlace E))
    (e : O →+* O') (ψ : Gal(Ω/E) →* O') : ℕ∞ :=
  length O' (T.divisibleSelmer Q e ψ)

/-- For all large coefficient rings `O' ⊇ O`, the character `ψ` has values in `O'` and the group
`Sel_Q(T ψ)` with coefficients in `Frac(O') / O'` has length at most `b`, normalised by
`len O' / ℓ = 1`. -/
def TwistedLengthLe {O : CoeffRing ℓ} {n : Type} [Fintype n] [DecidableEq n]
    (T : SelmerDatum ℓ S₀ g₀ O.val n) (Q : Finset (FinPlace E)) (ψ : Gal(Ω/E) →* PadicAlgCl ℓ)
    (b : ℝ≥0∞) : Prop :=
  ∀ᶠ O' : CoeffRing ℓ in atTop, ∃ hO : O ≤ O', ∃ ψ' : Gal(Ω/E) →* O'.val,
    (∀ g : Gal(Ω/E), (ψ' g : PadicAlgCl ℓ) = ψ g) ∧
    O'.normLength (T.divisibleLength Q (inclusion hO).toRingHom ψ') ≤ b

/-- A bound for the length of the twisted Selmer group may be weakened. -/
lemma TwistedLengthLe.mono {O : CoeffRing ℓ} {n : Type} [Fintype n] [DecidableEq n]
    {T : SelmerDatum ℓ S₀ g₀ O.val n} {Q : Finset (FinPlace E)} {ψ : Gal(Ω/E) →* PadicAlgCl ℓ}
    {b b' : ℝ≥0∞} (h : T.TwistedLengthLe Q ψ b) (hb : b ≤ b') : T.TwistedLengthLe Q ψ b' := by
  filter_upwards [h] with O' ⟨hO, ψ', hψ', h_le⟩ using ⟨hO, ψ', hψ', h_le.trans hb⟩

end SelmerDatum

open IsDiscreteValuationRing Polynomial

open scoped Classical in
/-- Let `d` attach to each prime `w` a tame generator `γ_w` and a Frobenius element `φ_w` (first
component) and slopes `s` indexed by `ι` (second component). The ties `z(γ_w) = s • z(φ_w)` with the
slopes of index `i`, as relations by `n × n` matrices, at the primes of `I ∪ I'` are the ties at
the primes of `I` together with those at the primes of `I'`. -/
lemma tieRelations_union {O n ι : Type} [CommRing O] [DecidableEq n] {q : ℕ}
    (I I' : Finset (FinPlace E)) (d : FinPlace E → AuxPrimeData E q × (ι → O)) (i : ι) :
    tieRelations (n := n) (I ∪ I') d i = tieRelations I d i ∪ tieRelations I' d i := by
  ext f
  simp only [tieRelations, Set.mem_union, Set.mem_range, Prod.exists, Subtype.exists, mem_union,
    exists_prop, or_and_right, exists_or]

/-- The polynomial `P` bounds the length of `Sel(x)`, the Selmer module modulo `ℓ ^ M` of the twist
of `ρ` by `ψ_x(g) = ∏ (1 + x_j) ^ (h_j g)`: we have `len Sel(x) ≤ v(P(x))` at all points `x` over
all discrete valuation rings of characteristic zero over `O`, not only where `ψ_x` is a
character. -/
def BoundsSelmer (ℓ : ℕ) {E : Type} [Field E] [EmbeddedNumberField E]
    {O n σ : Type} [CommRing O] [Fintype n] [DecidableEq n] [Fintype σ] {q : ℕ} (M : ℕ)
    (h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)) (ρ : Gal(Ω/E) →* Matrix n n O)
    (S : Set (FinPlace E)) (L : Set (Gal(Ω/E) →₀ Matrix n n O)) (P : MvPolynomial σ O) : Prop :=
  ∀ (O' : Type) [CommRing O'] [DVR O'] [CharZero O'] (e : O →+* O') (x : σ → O'),
    length O' (selmerAtPoint ℓ M h ρ S L e x) ≤ addVal O' (P.eval₂ e x)

/-- The restriction of a polynomial to the line `X_j = a_j Y`. -/
def restrictToLine {O σ : Type} [CommRing O] (a : σ → O) (P : MvPolynomial σ O) : O[X] :=
  MvPolynomial.aeval (fun j : σ ↦ Polynomial.C (a j) * Polynomial.X) P

/-- The value at `y` of the restriction of `P` to the line `X_j = a_j Y` is the value of `P` at the
point `(a_j y)_j`, with coefficients mapped by `e`. -/
lemma eval₂_restrictToLine {O O' σ : Type} [CommRing O] [CommRing O'] (a : σ → O)
    (P : MvPolynomial σ O) (e : O →+* O') (y : O') :
    (restrictToLine a P).eval₂ e y = P.eval₂ e fun j : σ ↦ e (a j) * y := by
  induction P using MvPolynomial.induction_on <;> simp_all [restrictToLine]

/-- Let `d` attach a Frobenius element `φ_v` to each prime `v`, and let `P¹ = tiePolynomial ρ I d`
be the product of the polynomials `det ((1 + Y) ρ(g) - 1)` over `g = φ_v` and its conjugate inverse
`g = φ_v^{-c}` for `v ∈ I`. If `2 n #I ≤ s₀`, where `n` is the rank of `ρ`, then the Gauss valuation
of radius `r` satisfies `v_r(P¹) ≤ s₀ r`, because each of the `2 #I` factors has a unit coefficient
in degree `n`. -/
lemma gaussVal_tiePolynomial_le {O n ι : Type} [CommRing O] [Fintype n] [DecidableEq n] {q : ℕ}
    (ρ : Gal(Ω/E) →* Matrix n n O) (I : Finset (FinPlace E))
    (d : FinPlace E → AuxPrimeData E q × (ι → O)) (f : O →+* intQpBar ℓ) (r : ℚ≥0) {s₀ : ℕ}
    (hs₀ : 2 * Fintype.card n * #I ≤ s₀) :
    gaussVal r ((tiePolynomial ρ I d).map f) ≤ s₀ * (r : ℝ≥0) := by
  have h_factor (g : Gal(Ω/E)) :
      gaussVal r ((shiftedDet (ρ g)).map f) ≤ (r : ℝ≥0) * (Fintype.card n : ℝ≥0∞) := by
    refine gaussVal_le_of_isUnit_coeff ?_
    rw [Polynomial.coeff_map, coeff_shiftedDet_card]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 ((Group.isUnit g).map ρ)).map f
  -- The Frobenius element at the prime `v` of `I`, or its conjugate inverse.
  let φ : I × Bool → Gal(Ω/E) := fun (v, b) ↦ idOrConjInv b (d v).1.frob
  have h_prod : tiePolynomial ρ I d = ∏ p : I × Bool, shiftedDet (ρ (φ p)) := rfl
  calc gaussVal r ((tiePolynomial ρ I d).map f)
    _ ≤ ∑ _p : I × Bool, (r : ℝ≥0) * (Fintype.card n : ℝ≥0∞) := by
      rw [h_prod, Polynomial.map_prod, gaussVal_prod]
      exact sum_le_sum fun p _ ↦ h_factor (φ p)
    _ = (2 * Fintype.card n * #I : ℕ) * (r : ℝ≥0) := by simp [mul_assoc, mul_comm, mul_left_comm]
    _ ≤ s₀ * (r : ℝ≥0) := by gcongr

omit [NumberField.IsCMField E] in
/-- Let `λ_j = lam j` be homomorphisms to `ℤ / q` and `ζ_j` be `q`-th roots of unity. The twist of
`ρ` by the character `g ↦ ∏ ζ_j ^ (λ_j g)` is the twist by the value of
`ψ_X(g) = ∏ (1 + X_j) ^ (λ_j g)` at the point `x = (ζ_j - 1)_j`. -/
lemma coe_twistRep_pointChar {O O' n σ : Type} [CommRing O] [CommRing O'] [Fintype n]
    [DecidableEq n] [Fintype σ] {q : ℕ} [NeZero q] (lam : σ → Gal(Ω/E) →* Multiplicative (ZMod q))
    {ζ : σ → O'} (hζ : ∀ j : σ, ζ j ^ q = 1) (e : O →+* O') (ρ : Gal(Ω/E) →* Matrix n n O) :
    ⇑(twistRep e (pointChar lam ζ hζ) ρ) = pointTwist lam (fun j : σ ↦ ζ j - 1) e ρ := by
  ext1 g
  simp [twistRep, pointTwist, eval_universalChar]

/-- Bound module length using the relative length and the length of the comparison submodule. -/
private lemma length_le_of_relLength_le {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]
    {S T : Submodule A M} {b c : ℕ∞} (hrel : relLength S T ≤ b)
    (hT : Module.length A T ≤ c) : Module.length A S ≤ b + c := by
  rw [← relLength_add_length_inf S T]
  exact add_le_add hrel ((New.length_mono inf_le_right).trans hT)

namespace SelmerDatum

variable {ι n : Type} [Fintype n] [DecidableEq n] {V : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)}
  {J : Finset (FinPlace E)} {M N s₀ : ℕ} {P₀ : FinPlace E} {r : ℚ≥0}

/-- The action on the lattice of a Selmer datum `T`, reduced modulo `ℓ ^ M`, is trivial on the
inertia groups above the places outside `S₀`. -/
lemma reduceModPow_eq_one {O : Type} [CommRing O] [PadicIntegerRing O ℓ]
    (T : SelmerDatum ℓ S₀ g₀ O n) {g : Gal(Ω/E)} (hg : g ∈ inertiaAbove S₀ᶜ) :
    reduceModPow ℓ M T.ρ g = 1 := by
  obtain ⟨v, hv, hg_v⟩ := hg
  simp [reduceModPow, T.unramified g ⟨v, fun h_mem ↦ hv (T.subset h_mem), hg_v⟩]

open scoped Classical in
/-- Let `J` be a set of tied primes (`IsTiedPrimes`): auxiliary primes with a first prime `P₀ ∈ J`,
whose Frobenius element `(d P₀).1.frob` lies in `W`, and with Frobenius elements `φ_w`, tame
generators `γ_w` and slopes given by `d`. Let `M < N`. Suppose that the elements with the property
`V i` act trivially on `T` modulo `ℓ ^ M`, and that the Frobenius element of `P₀` and its conjugate
inverse act modulo `ℓ ^ M` as `g₀` and `g₀^{-c}` (`idOrConjInv`). If the Selmer group modulo `ℓ ^ M`
tied at all primes of `J` has length at most `globalTerm + placesTerm`, then the group tied only at
the primes other than `P₀` has length at most `β_T = globalTerm + placesTerm + firstPrimeTerm`. -/
lemma length_tiedSelmer_erase_le {O : Type} [CommRing O] [PadicIntegerRing O ℓ]
    (T : SelmerDatum ℓ S₀ g₀ O n) {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}
    (h_primes : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hMN : M < N) (i : ι)
    (hV : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M T.ρ g = 1)
    (h_first : ∀ b : Bool, reduceModPow ℓ M T.ρ (idOrConjInv b (d P₀).1.frob) =
      reduceModPow ℓ M T.ρ (idOrConjInv b g₀))
    (h_tied : length O (T.tiedSelmer J J d i (ℓ ^ M)) ≤ T.globalTerm + T.placesTerm) :
    length O (T.tiedSelmer J (J.erase P₀) d i (ℓ ^ M)) ≤ T.β := by
  let Z := T.tiedSelmer J J d i (ℓ ^ M)
  let Z₀ := T.tiedSelmer J (J.erase P₀) d i (ℓ ^ M)
  -- Dropping the ties at `P₀` and its conjugate costs at most `T.firstPrimeTerm`.
  have h_release : relLength Z₀ Z ≤ T.firstPrimeTerm := by
    have h_ties : tieRelations (n := n) J d i =
        tieRelations (J.erase P₀) d i ∪ tieRelations {P₀} d i := by
      rw [← tieRelations_union, union_comm, ← insert_eq, insert_erase h_primes.first_mem]
    simp only [Z₀, Z, tiedSelmer, h_ties, ← Set.union_assoc]
    exact h_primes.relLength_tieRelations_le_sum_addVal_det (Nat.ne_zero_of_lt hMN) i
      (fun _ hg ↦ T.reduceModPow_eq_one hg) hV hMN.le h_first (unionWithConj T.places J)
      (T.classRelations ∪ tieRelations (J.erase P₀) d i)
  calc length O Z₀ ≤ T.firstPrimeTerm + (T.globalTerm + T.placesTerm) :=
        length_le_of_relLength_le h_release h_tied
    _ = T.β := by rw [β, localTerms, add_comm, add_assoc]

open scoped Classical in
/-- Let `O` be the ring of integers of a finite extension of `ℚ_ℓ` and `T` a Selmer datum: a lattice
`O ^ n` with an action `ρ` of `Gal(Ω/E)`, unramified outside `T.places ⊆ S₀`, with the relations
`T.classRelations`. Its number `β_T = T.β` is the sum of a global term, local terms at `T.places`
and a term for the element `g₀`. Let `J` be a set of auxiliary primes with first prime `P₀`
(`IsTiedPrimes`), where `d` gives each `v ∈ J` a Frobenius element `φ_v`, a tame generator `γ_v`, a
character to `ℤ / ℓ ^ N` and the slope `s_v = (d v).2 i` for the index `i` of `T`. A cocycle `z` is
tied at `v` if `z(γ_v) = s_v • z(φ_v)`, and likewise at the conjugate prime. Let `T` modulo `ℓ ^ M`
be trivial at the elements with the property `V i`, and let `N ≠ 0`, `r ≤ 1` and `M ≤ N r`. Suppose
that the Selmer group of `T` modulo `ℓ ^ M` that is tied at the primes of `J` other than `P₀` has
length at most `β_T`. Then there is a polynomial `P⁰ = lineBound` with `v(P⁰(0)) ≤ β_T` and the
following property. Let `e : O → O'` be a discrete valuation ring of characteristic zero over `O`
with a map `f` to `ℤ̄_ℓ = intQpBar ℓ` that reflects divisibility, let `y ∈ O'` with
`ellVal (f y) ≥ r`, and let `x = (a_v y)_{v ∈ J}`, where `a = lineDirection P₀ J d i` has
`a_{P₀} = 1` and `a_v = s_v` otherwise. Then some polynomial `P` bounds the length of the Selmer
module of the characters `(d v).1.character` at all points (`BoundsSelmer`), and `P(x)` divides
`P⁰(y) P¹(y)` in `ℤ̄_ℓ`. Here `P¹ = tiePolynomial` is the product of the `det ((1 + Y) ρ(g) - 1)`
over the Frobenius elements `g = φ_v` of the primes `v` of `J` other than `P₀` and their conjugate
inverses. -/
lemma exists_boundsSelmer_and_eval_dvd {O : Type} [CommRing O] [PadicIntegerRing O ℓ]
    (T : SelmerDatum ℓ S₀ g₀ O n) {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}
    (h_primes : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN₀ : N ≠ 0) (i : ι)
    (hV : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M T.ρ g = 1)
    (h_tied : length O (T.tiedSelmer J (J.erase P₀) d i (ℓ ^ M)) ≤ T.β) (hr : r ≤ 1)
    (hN : M ≤ N * r) :
    ∃ lineBound : O[X], addVal O (lineBound.coeff 0) ≤ T.β ∧
      ∀ (O' : Type) [CommRing O'] [DVR O'] [CharZero O'] (e : O →+* O') (f : O' →+* intQpBar ℓ)
        (y : O') (_hf_reflects : ∀ z z' : O', f z ∣ f z' → z ∣ z')
        (_hy_val : (r : ℝ≥0) ≤ ellVal (f y).val),
        ∃ P : MvPolynomial J O,
          BoundsSelmer ℓ M (fun v : J ↦ (d v).1.character) T.ρ (unionWithConj T.places J)
            T.classRelations P ∧
          MvPolynomial.eval (fun v : J ↦ f.comp e (lineDirection P₀ J d i v) * f y)
              (P.map (f.comp e)) ∣
            (lineBound.map (f.comp e)).eval (f y) *
              ((tiePolynomial T.ρ (J.erase P₀) d).map (f.comp e)).eval (f y) := by
  let lam (v : J) : Gal(Ω/E) →* Multiplicative (ZMod (ℓ ^ N)) := (d v).1.character
  let S : Set (FinPlace E) := unionWithConj T.places J
  let L₀ : Set (Gal(Ω/E) →₀ Matrix n n O) := T.classRelations ∪ tieRelations (J.erase P₀) d i
  let a : J → O := lineDirection P₀ J d i
  have h_lam (v : J) : IsLocallyConstant (lam v) :=
    (h_primes.isAuxPrimeDataAt v v.property).isLocallyConstant
  -- A polynomial `G` for the tied module that is sharp at `0`; `P⁰` is its restriction to the line.
  obtain ⟨G, hG_sharp, hG_bound⟩ : ∃ G : MvPolynomial J O,
      addVal O (G.eval₂ (.id O) fun _ ↦ 0) =
        length O (selmerAtPoint ℓ M lam T.ρ S L₀ (.id O) fun _ ↦ 0) ∧
      BoundsSelmer ℓ M lam T.ρ S L₀ G :=
    exists_sharp_polynomial h_lam (T.isLocallyConstant M) (finite_toSet _) L₀ (.id O) fun _ ↦ 0
  refine ⟨restrictToLine a G, ?_, fun O' _ _ _ e f y hf_reflects hy_val ↦ ?_⟩
  · have h_zero : (restrictToLine a G).coeff 0 = G.eval₂ (.id O) fun _ ↦ 0 := by
      simpa using eval₂_restrictToLine a G (.id O) 0
    rwa [h_zero, hG_sharp, selmerAtPoint_zero]
  -- A polynomial `P` for the module without ties that is sharp at the point `x` of the line.
  let x (v : J) : O' := e (a v) * y
  let Sel (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
      Submodule O' (Gal(Ω/E) → n → QuotSpan (ℓ ^ M : O')) := selmerAtPoint ℓ M lam T.ρ S L e x
  obtain ⟨P, hP_sharp, hP_bound⟩ : ∃ P : MvPolynomial J O,
      addVal O' (P.eval₂ e x) = length O' (Sel T.classRelations) ∧
      BoundsSelmer ℓ M lam T.ρ S T.classRelations P :=
    exists_sharp_polynomial h_lam (T.isLocallyConstant M) (finite_toSet _) T.classRelations e x
  have h_norm (α : O') (hα : y ∣ α - 1) : (ℓ ^ M : O') ∣ ∑ j ∈ range (ℓ ^ N), α ^ j :=
    pow_dvd_geom_sum f hf_reflects hr hN (hy_val.trans (dvd_iff_ellVal_le.1 (map_dvd f hα)))
  have h_untie : relLength (Sel T.classRelations) (Sel L₀) ≤
      addVal O' ((tiePolynomial T.ρ (J.erase P₀) d).eval₂ e y) :=
    h_primes.relLength_tied_le hN₀ i (fun _ ↦ T.reduceModPow_eq_one) hV e h_norm S T.classRelations
  have h_dvd : P.eval₂ e x ∣
      (restrictToLine a G).eval₂ e y * (tiePolynomial T.ρ (J.erase P₀) d).eval₂ e y := by
    rw [← addVal_le_iff_dvd, addVal_mul, eval₂_restrictToLine, hP_sharp, add_comm]
    exact length_le_of_relLength_le h_untie (hG_bound O' e x)
  -- The claim is the image of `h_dvd` under `f`.
  refine ⟨P, hP_bound, ?_⟩
  simpa only [map_mul, Polynomial.hom_eval₂, MvPolynomial.eval₂_comp_left, Polynomial.eval_map,
    MvPolynomial.eval_map, Function.comp_def, RingHom.comp_apply, x, a] using map_dvd f h_dvd

/-- Let `P` bound, at all points `x`, the length of the Selmer module `Sel(x)` modulo `ℓ ^ M` of the
twist of `T` at `x`, unramified outside `S ∪ J ∪ J̄` and with the relations `T.classRelations`
(`BoundsSelmer`), for characters `λ_v = lam v` to `ℤ / q`. Let `e : O → O'` be a ring map to a
discrete valuation ring `O'` of characteristic zero, with valuation `v = addVal O'`, and let the
`ζ_v ∈ O'` be `q`-th roots of unity. At `x = (ζ_v - 1)_v` the module `Sel(x)` is the Selmer group
`Sel_J(T ψ)` modulo `ℓ ^ M` for `ψ = ∏ ζ_v ^ λ_v` (`pointChar`). So if `v(P(x)) < v(ℓ ^ M)`, where
`P(x)` is `P` evaluated through `e`, then `v(P(x))` bounds the length of `Sel_J(T ψ)` with
coefficients in `Frac(O') / O'` (`divisibleLength`). -/
lemma divisibleLength_pointChar_le {O : Type} [CommRing O] [PadicIntegerRing O ℓ]
    (T : SelmerDatum ℓ S₀ g₀ O n) {σ O' : Type} [Fintype σ] [CommRing O'] [DVR O'] [CharZero O']
    {q : ℕ} [NeZero q] {lam : σ → Gal(Ω/E) →* Multiplicative (ZMod q)} {P : MvPolynomial σ O}
    (hP : BoundsSelmer ℓ M lam T.ρ (unionWithConj T.places J) T.classRelations P) (e : O →+* O')
    {ζ : σ → O'} (hζ : ∀ v : σ, ζ v ^ q = 1)
    (h_lt : addVal O' (P.eval₂ e fun v : σ ↦ ζ v - 1) < addVal O' (ℓ ^ M)) :
    T.divisibleLength J e (pointChar lam ζ hζ) ≤
      addVal O' (P.eval₂ e fun v : σ ↦ ζ v - 1) := by
  have h_level : length O' (T.twistedSelmer J e (pointChar lam ζ hζ) (ℓ ^ M)) ≤
      addVal O' (P.eval₂ e fun v ↦ ζ v - 1) := by
    rw [twistedSelmer, coe_twistRep_pointChar]
    exact hP O' e _
  rw [twistedSelmer] at h_level
  exact (length_selmerModule_divisibleQuot_le _ _ _ (NeZero.ne _)
    (h_level.trans_lt h_lt)).trans h_level

open scoped Classical in
/-- The choice of the polynomial `P` of a Selmer datum `T` over a coefficient ring `O`, the ring of
integers of a finite Galois extension of `ℚ_ℓ`, included in `ℤ̄_ℓ` by `O.toIntQpBar`. The datum is
a lattice `O ^ n` with Galois action, unramified outside `T.places ⊆ S₀`, with the relations
`T.classRelations` (local conditions above `ℓ` and vanishing at `T.γ`); `β_T = T.β` is the sum of a
global term, local terms at `T.places` and a term for the element `g₀`. Let `J` be a set of
auxiliary primes with first prime `P₀` (`IsTiedPrimes`), where `d` gives each `w ∈ J` a Frobenius
element `φ_w`, a tame generator `γ_w`, a character to `ℤ / ℓ ^ N` and the slope `s_w = (d w).2 i`
for the index `i` of `T`; a cocycle `z` is tied at `w` if `z(γ_w) = s_w • z(φ_w)`, and likewise at
the conjugate prime. Let `T` modulo `ℓ ^ M` be trivial at the elements with the property `V i`, and
let `N ≠ 0`, `2 rank(T) #J ≤ s₀`, `r ≤ 1` and `M ≤ N r`. If the Selmer group modulo `ℓ ^ M` that is
tied at the primes of `J` other than `P₀` has length at most `β_T`, then some `P` bounds the length
of the Selmer module of these characters at all points (`BoundsSelmer`), and
`v(P(x₀)) ≤ β_T + s₀ r` at a point `x₀` over `ℤ̄_ℓ` whose coordinates have valuation at least `r`.
Here `v = ellVal` has `v(ℓ) = 1`, and `normLength` multiplies the length `β_T` by the valuation of a
uniformiser of `O`. -/
theorem exists_boundsSelmer_ellVal_eval_le {O : CoeffRing ℓ} (T : SelmerDatum ℓ S₀ g₀ O.val n)
    {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O.val)}
    (h_primes : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN₀ : N ≠ 0) (i : ι)
    (hV : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M T.ρ g = 1)
    (h_tied : length O.val (T.tiedSelmer J (J.erase P₀) d i (ℓ ^ M)) ≤ T.β)
    (hs₀ : 2 * Fintype.card n * #J ≤ s₀) (hr : r ≤ 1) (hN : M ≤ N * r) :
    ∃ (P : MvPolynomial J O.val) (x₀ : J → intQpBar ℓ),
      (∀ v : J, (r : ℝ≥0) ≤ ellVal (x₀ v).val) ∧
      ellVal (MvPolynomial.eval x₀ (P.map O.toIntQpBar)).val ≤
        O.normLength T.β + s₀ * (r : ℝ≥0) ∧
      BoundsSelmer ℓ M (fun v : J ↦ (d v).1.character) T.ρ (unionWithConj T.places J)
        T.classRelations P := by
  -- Take `x₀` on the line at a parameter `y` that is generic for `p₀ = P⁰` and `p₁ = P¹`: they
  -- attain their Gauss valuations of radius `r` at `y`. Then `v(P(x₀)) ≤ v_r(P⁰) + v_r(P¹)`.
  obtain ⟨lineBound, h_coeff_zero, h_bound_dvd⟩ :=
    T.exists_boundsSelmer_and_eval_dvd h_primes hN₀ i hV h_tied hr hN
  set p₀ : (intQpBar ℓ)[X] := lineBound.map O.toIntQpBar with hp₀
  set p₁ : (intQpBar ℓ)[X] := (tiePolynomial T.ρ (J.erase P₀) d).map O.toIntQpBar with hp₁
  have h_zero : ellVal (p₀.eval 0).val ≤ O.normLength T.β := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, hp₀, Polynomial.coeff_map, CoeffRing.coe_toIntQpBar,
      ← CoeffRing.normLength_addVal]
    exact CoeffRing.normLength_mono h_coeff_zero
  have h_tie : gaussVal r p₁ ≤ s₀ * (r : ℝ≥0) :=
    gaussVal_tiePolynomial_le T.ρ _ d O.toIntQpBar r
      ((Nat.mul_le_mul_left _ card_erase_le).trans hs₀)
  obtain ⟨y, hy, h_generic⟩ := exists_forall_ellVal_eval_eq_gaussVal r ![p₀, p₁]
  have hy₀ : ellVal (p₀.eval y).val = gaussVal r p₀ := h_generic 0
  have hy₁ : ellVal (p₁.eval y).val = gaussVal r p₁ := h_generic 1
  obtain ⟨O', hO, hy_mem⟩ := ((eventually_ge_atTop O).and (CoeffRing.eventually_mem y.2)).exists
  let y' : O'.val := ⟨y, hy_mem⟩
  have hy' : O'.toIntQpBar y' = y := rfl
  let x₀ (v : J) : intQpBar ℓ := O.toIntQpBar (lineDirection P₀ J d i v) * y
  obtain ⟨P, hP, h_dvd⟩ : ∃ P : MvPolynomial J O.val,
      BoundsSelmer ℓ M (fun v : J ↦ (d v).1.character) T.ρ (unionWithConj T.places J)
        T.classRelations P ∧
      MvPolynomial.eval x₀ (P.map O.toIntQpBar) ∣ p₀.eval y * p₁.eval y := by
    simpa only [CoeffRing.toIntQpBar_comp_inclusion, hy', ← hp₀, ← hp₁] using h_bound_dvd O'.val
      (inclusion hO).toRingHom O'.toIntQpBar y' O'.dvd_of_toIntQpBar_dvd (by rwa [hy'])
  refine ⟨P, x₀, fun v ↦ hy.trans (dvd_iff_ellVal_le.1 (dvd_mul_left y _)), ?_, hP⟩
  calc
    _ ≤ ellVal (p₀.eval y).val + ellVal (p₁.eval y).val := by
      simpa only [ellVal_val_mul] using dvd_iff_ellVal_le.1 h_dvd
    _ = gaussVal r p₀ + gaussVal r p₁ := by rw [hy₀, hy₁]
    _ ≤ O.normLength T.β + s₀ * (r : ℝ≥0) :=
      add_le_add ((gaussVal_le_eval_zero p₀).trans h_zero) h_tie

/-- Let `T` be a Selmer datum over a coefficient ring `O`, for the set `S₀` of places and the
element `g₀`: a lattice with Galois action, unramified outside `S = T.places ⊆ S₀`. Let `P` bound,
at all points, the length of the Selmer module modulo `ℓ ^ M` of the twist of `T` by the characters
`λ_v = lam v` to `ℤ / q`, unramified outside `S ∪ J ∪ J̄` and with the relations `T.classRelations`,
the local conditions above `ℓ` and vanishing at `T.γ` (`BoundsSelmer`). Let the `ζ_v ∈ ℤ̄_ℓ` be
`q`-th roots of unity, `x = (ζ_v - 1)_v` and `ψ = ∏ ζ_v ^ λ_v` (`pointChar`). If `v(P(x)) < M`,
where `v = ellVal` has `v(ℓ) = 1`, then over all large coefficient rings the normalised length of
`Sel_J(T ψ)` with divisible coefficients is at most `v(P(x))` (`TwistedLengthLe`). -/
lemma twistedLengthLe_pointChar {O : CoeffRing ℓ} (T : SelmerDatum ℓ S₀ g₀ O.val n)
    {σ : Type} [Fintype σ] {q : ℕ} [NeZero q]
    {lam : σ → Gal(Ω/E) →* Multiplicative (ZMod q)} {P : MvPolynomial σ O.val}
    (hP : BoundsSelmer ℓ M lam T.ρ (unionWithConj T.places J) T.classRelations P)
    (ζ : σ → intQpBar ℓ) (hζ : ∀ v : σ, (ζ v : PadicAlgCl ℓ) ^ q = 1)
    (h_lt : ellVal (MvPolynomial.eval (fun v : σ ↦ ζ v - 1) (P.map O.toIntQpBar)).val < M) :
    T.TwistedLengthLe J (pointChar lam (fun v : σ ↦ (ζ v : PadicAlgCl ℓ)) hζ)
      (ellVal (MvPolynomial.eval (fun v : σ ↦ ζ v - 1) (P.map O.toIntQpBar)).val) := by
  filter_upwards [eventually_ge_atTop O, CoeffRing.eventually_exists_toIntQpBar_eq ζ]
    with O' hO ⟨ζ', hζ'⟩
  obtain rfl : (fun v ↦ O'.toIntQpBar (ζ' v)) = ζ := funext hζ'
  have hζ'_pow (v : σ) : ζ' v ^ q = 1 := Subtype.ext (by simpa using hζ v)
  let value : O'.val := P.eval₂ (inclusion hO).toRingHom fun v ↦ ζ' v - 1
  have h_val : O'.normLength (addVal O'.val value) =
      ellVal (MvPolynomial.eval (fun v ↦ O'.toIntQpBar (ζ' v) - 1) (P.map O.toIntQpBar)).val := by
    simp only [value, CoeffRing.normLength_addVal_eval₂ hO, map_sub, map_one]
  have h_level : O'.normLength (addVal O'.val (ℓ ^ M)) = M := by simp
  have h_lt' : addVal O'.val value < addVal O'.val (ℓ ^ M) :=
    (CoeffRing.normLength_mono (O := O')).reflect_lt (by rwa [h_val, h_level])
  have h_len : T.divisibleLength J (inclusion hO).toRingHom (pointChar lam ζ' hζ'_pow) ≤
      addVal O'.val value :=
    T.divisibleLength_pointChar_le hP _ hζ'_pow h_lt'
  -- The character with values in `O'` has the given values in `ℚ̄_ℓ`.
  exact ⟨hO, pointChar lam ζ' hζ'_pow, fun g ↦ by simp,
    (CoeffRing.normLength_mono h_len).trans_eq h_val⟩

end SelmerDatum

end Choice

variable {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  {S₀ : Finset (FinPlace E)} {g₀ : Gal(Ω/E)}

/-- For `g` near `g₀`, the element `g` (for `b = true`) or its conjugate inverse `g^{-c}` (for
`b = false`) acts on the lattice of a Selmer datum `T` modulo `ℓ ^ M` as `g₀` or `g₀^{-c}` does. -/
lemma SelmerDatum.eventually_reduceModPow_idOrConjInv_eq {O n : Type} [CommRing O]
    [PadicIntegerRing O ℓ] [Fintype n] [DecidableEq n] (T : SelmerDatum ℓ S₀ g₀ O n) (M : ℕ)
    (b : Bool) :
    ∀ᶠ g : Gal(Ω/E) in nhds g₀,
      reduceModPow ℓ M T.ρ (idOrConjInv b g) = reduceModPow ℓ M T.ρ (idOrConjInv b g₀) := by
  have h_cont : Continuous (idOrConjInv b : Gal(Ω/E) → Gal(Ω/E)) := by
    cases b
    exacts [continuous_conjGal.inv, continuous_id]
  exact ((T.isLocallyConstant M).comp_continuous h_cont).eventually_eq g₀

variable {ι κ : Type} {n : ι → Type} [∀ i : ι, Fintype (n i)] [∀ i : ι, DecidableEq (n i)]
  {O : CoeffRing ℓ}

/-- `ℓ ^ M` is a suitable level of torsion for the Selmer data `T i`: the exponent `M` exceeds the
normalised numbers `β_T` by more than `1`, and the residue field of `O` is large. -/
structure IsTorsionLevel (T : ∀ i : ι, SelmerDatum ℓ S₀ g₀ O.val (n i)) (M : ℕ) : Prop where
  /-- `M > β_T + 1` for each datum, with `β_T` scaled so that `O / ℓ` has length `1`. -/
  β_lt (i : ι) : O.normLength (T i).β + 1 < M
  /-- The residue field has more than `2 rank(T i) len(O / ℓ ^ M) + 1` elements, which leaves room
  for the choice of slopes. -/
  lt_card_residueField (i : ι) :
    2 * Fintype.card (n i) * IsDiscreteValuationRing.addVal O.val (ℓ ^ M) + 1 <
      Nat.card (IsLocalRing.ResidueField O.val)

/-- Auxiliary primes, homomorphisms to `ℤ / ℓ ^ N`, and polynomials with points for Selmer data
`T i` and Stickelberger systems `Y k`, for an integer `s₀` and a radius `r`. Valuations are those
of `ellVal`, with `v(ℓ) = 1`. -/
structure TwistPolynomials (T : ∀ i : ι, SelmerDatum ℓ S₀ g₀ O.val (n i))
    (Y : κ → StickelbergerSystem ℓ S₀ g₀) (s₀ : ℕ) (r : ℚ≥0) (N : ℕ) where
  /-- The set `Q` of primes. -/
  auxPrimes : Finset (FinPlace E)
  /-- `Q` is auxiliary for `S₀`. -/
  auxiliary : IsAuxiliary S₀ auxPrimes
  /-- `Q` has at most `s₀ / 2` primes. -/
  two_mul_card_le : 2 * #auxPrimes ≤ s₀
  /-- The homomorphisms `λ_𝔮` to `ℤ / ℓ ^ N`, one for each prime `𝔮` of `Q`. -/
  primeChar : auxPrimes → Gal(Ω/E) →* Multiplicative (ZMod (ℓ ^ N))
  /-- `λ_𝔮` is continuous and `λ_𝔮(Art y) = η(y / ȳ)` for an idele class character `η` of tame
  level `𝔮` that is trivial above `ℓ`. So it is anticyclotomic, unramified outside `𝔮` and `𝔮̄`, and
  zero on the decomposition groups above `ℓ`. -/
  isFromU1_primeChar (v : auxPrimes) : IsFromU1 (placesDividing E ℓ) {v.val} (primeChar v)
  /-- `λ_𝔮` is onto on inertia at `𝔮`. -/
  exists_eq_ofAdd_one (v : auxPrimes) : ∃ g ∈ inertiaAbove {v.val},
    primeChar v g = Multiplicative.ofAdd 1
  /-- The polynomials of the data. -/
  datumPoly : ι → MvPolynomial auxPrimes (intQpBar ℓ)
  /-- The polynomials of the systems. -/
  systemPoly : κ → MvPolynomial auxPrimes (intQpBar ℓ)
  /-- The points of the data. -/
  datumPoint : ι → auxPrimes → intQpBar ℓ
  /-- The points of the systems. -/
  systemPoint : κ → auxPrimes → intQpBar ℓ
  /-- The coordinates of the point of a datum have valuation at least `r`. -/
  le_ellVal_datumPoint (i : ι) (v : auxPrimes) : (r : ℝ≥0) ≤ ellVal (datumPoint i v).val
  /-- The coordinates of the point of a system have valuation at least `r`. -/
  le_ellVal_systemPoint (k : κ) (v : auxPrimes) : (r : ℝ≥0) ≤ ellVal (systemPoint k v).val
  /-- At the point of a datum, `v(P) ≤ β_T + s₀ r`. -/
  ellVal_datumPoly_le (i : ι) :
    ellVal (eval (datumPoint i) (datumPoly i)).val ≤ O.normLength (T i).β + s₀ * (r : ℝ≥0)
  /-- At the point of a system, `v(P) ≤ β + s₀ r`. -/
  ellVal_systemPoly_le (k : κ) :
    ellVal (eval (systemPoint k) (systemPoly k)).val ≤ (Y k).β + s₀ * (r : ℝ≥0)
  /-- For `ℓ ^ N`-th roots of unity `ζ_𝔮`, `ψ = ∏ ζ_𝔮 ^ λ_𝔮` and `x = (ζ_𝔮 - 1)_𝔮`, the value of `ψ`
  at the element `Θ_Q` of a system is `P(x)`. -/
  groupRingEval_eq_eval (ζ : auxPrimes → intQpBar ℓ)
    (hζ : ∀ v : auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1) (k : κ) :
    groupRingEval (pointChar primeChar (fun v : auxPrimes ↦ (ζ v : PadicAlgCl ℓ)) hζ)
      ((Y k).element auxPrimes) =
      (eval (fun v : auxPrimes ↦ ζ v - 1) (systemPoly k) : intQpBar ℓ)
  /-- For the same `ψ` and `x`, the group `Sel_Q(T ψ)` has length at most `v(P(x))` if
  `v(P(x)) < β_T + 1`. -/
  length_le (ζ : auxPrimes → intQpBar ℓ) (hζ : ∀ v : auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1)
    (i : ι)
    (h_lt : ellVal (eval (fun v : auxPrimes ↦ ζ v - 1) (datumPoly i)).val <
      O.normLength (T i).β + 1) :
    (T i).TwistedLengthLe auxPrimes
      (pointChar primeChar (fun v : auxPrimes ↦ (ζ v : PadicAlgCl ℓ)) hζ)
      (ellVal (eval (fun v : auxPrimes ↦ ζ v - 1) (datumPoly i)).val)

/-- Let `T i` be Selmer data over a coefficient ring `O` and `Y k` Stickelberger systems. Let `J` be
a set of tied auxiliary primes with elements and slopes given by `d` and with a first prime `P₀`
whose Frobenius element lies in the set `W`, otherwise unused (`IsTiedPrimes`); where the slope for
`T i` is nonzero, the Frobenius element and its conjugate inverse act trivially on `T i` modulo
`ℓ ^ M`. Let the Selmer group of each `T i` modulo `ℓ ^ M` tied at all primes of `J` (`tiedSelmer`)
have length at most `globalTerm + placesTerm`, the global term of `T i` plus its local terms at the
places of `(T i).places` prime to `ℓ`; adding the term for `g₀` gives the number `β` of `T i`. Let
the Frobenius element `φ = (d P₀).1.frob` of `P₀` and its conjugate inverse act on each `T i` modulo
`ℓ ^ M` as `g₀` and its conjugate inverse do, and let `ϑ(φ) ≡ ϑ(g₀)` modulo `ℓ ^ M'` for the
character `ϑ = twistChar` of each `Y k`. Let `M > O.normLength β + 1` for each `T i` and
`M' > β + 1` for each `Y k`, where `β = v(1(Θ_∅)) + 2 m v(ϑ(g₀) - 1)`, `1(Θ_∅)` is the value of the
trivial character at the element `(Y k).element ∅` and `m` is the length of the list
`(Y k).exponents`. Let `c ≥ 1` bound the ranks of the `T i` and the lengths `m`, and let `s₀ ≥ 1`,
`2 c #J ≤ s₀`, `s₀ r < 1`, `M < N` and `M, M' ≤ N r`. Then `TwistPolynomials` is inhabited: there
are auxiliary primes (the proof takes `J`), homomorphisms to `ℤ / ℓ ^ N`, and for each datum and
system a polynomial `P` that controls its twists at roots of unity, with a point of valuation at
least `r` where `v(P) ≤ β + s₀ r`, with `O.normLength β` in place of `β` for the `T i`. -/
lemma nonempty_twistPolynomials_of_isTiedPrimes (T : ∀ i : ι, SelmerDatum ℓ S₀ g₀ O.val (n i))
    (Y : κ → StickelbergerSystem ℓ S₀ g₀) {M M' N c s₀ : ℕ} {r : ℚ≥0} {W : Set Gal(Ω/E)}
    {P₀ : FinPlace E} {J : Finset (FinPlace E)}
    {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O.val)}
    (h_primes : IsTiedPrimes ℓ S₀
      (fun (i : ι) (g : Gal(Ω/E)) ↦ reduceModPow ℓ M (T i).ρ g = 1) W N P₀ J d)
    (h_tied : ∀ i : ι,
      length O.val ((T i).tiedSelmer J J d i (ℓ ^ M)) ≤ (T i).globalTerm + (T i).placesTerm)
    (h_frob_datum : ∀ (i : ι) (b : Bool), reduceModPow ℓ M (T i).ρ (idOrConjInv b (d P₀).1.frob) =
      reduceModPow ℓ M (T i).ρ (idOrConjInv b g₀))
    (h_frob_system : ∀ k : κ,
      (M' : ℝ≥0∞) ≤ ellVal ((Y k).twistChar (d P₀).1.frob - (Y k).twistChar g₀ : PadicAlgCl ℓ))
    (hM : ∀ i : ι, O.normLength (T i).β + 1 < M) (hM' : ∀ k : κ, (Y k).β + 1 < M')
    (hc : 1 ≤ c) (h_rank : ∀ i : ι, Fintype.card (n i) ≤ c)
    (h_exps : ∀ k : κ, (Y k).exponents.length ≤ c) (hs₀ : 1 ≤ s₀) (h_card_le : 2 * c * #J ≤ s₀)
    (hr : s₀ * r < 1) (hMN : M < N) (hN : M ≤ N * r) (hN' : M' ≤ N * r) :
    Nonempty (TwistPolynomials T Y s₀ r N) := by
  let lam (v : J) : Gal(Ω/E) →* Multiplicative (ZMod (ℓ ^ N)) := (d v).1.character
  have hr_one : r ≤ 1 := (le_mul_of_one_le_left zero_le (mod_cast hs₀)).trans hr.le
  have h_card {c' : ℕ} (hc' : c' ≤ c) : 2 * c' * #J ≤ s₀ := le_trans (by gcongr) h_card_le
  have h_datum (i : ι) : ∃ (P : MvPolynomial J O.val) (x : J → intQpBar ℓ),
      (∀ v : J, (r : ℝ≥0) ≤ ellVal (x v).val) ∧
      ellVal (eval x (P.map O.toIntQpBar)).val ≤ O.normLength (T i).β + s₀ * (r : ℝ≥0) ∧
      BoundsSelmer ℓ M lam (T i).ρ (unionWithConj (T i).places J) (T i).classRelations P :=
    (T i).exists_boundsSelmer_ellVal_eval_le h_primes (Nat.ne_zero_of_lt hMN) i (fun _ hg ↦ hg)
      ((T i).length_tiedSelmer_erase_le h_primes hMN i (fun _ hg ↦ hg) (h_frob_datum i) (h_tied i))
      (h_card (h_rank i)) hr_one hN
  have h_system (k : κ) : ∃ x : J → intQpBar ℓ, (∀ v : J, (r : ℝ≥0) ≤ ellVal (x v).val) ∧
      ellVal (eval x (groupRingEval (universalChar lam) ((Y k).element J))).val ≤
        (Y k).β + s₀ * (r : ℝ≥0) :=
    (Y k).exists_point_ellVal_universalChar_le h_primes (hM' k) (h_frob_system k) hs₀
      (h_card (h_exps k)) hr hN'
  have h_inertia (v : J) : ∃ g ∈ inertiaAbove {v.val}, lam v g = Multiplicative.ofAdd 1 := by
    obtain ⟨hγ_inertia, hγ_one, -⟩ := (h_primes.isAuxPrimeDataAt v v.property).tame_gen
    exact ⟨(d v).1.tameGenerator,
      ⟨v, rfl, _, (h_primes.isAuxPrimeDataAt v v.property).isPlaceOver, hγ_inertia⟩, hγ_one⟩
  choose P x hx hP_val hP_bound using h_datum
  choose x' hx' hx'_val using h_system
  exact ⟨{
    auxPrimes := J
    auxiliary := h_primes.auxiliary
    two_mul_card_le := by simpa using h_card hc
    primeChar := lam
    isFromU1_primeChar v := (h_primes.isAuxPrimeDataAt v v.property).toIsFromU1
    exists_eq_ofAdd_one := h_inertia
    datumPoly i := (P i).map O.toIntQpBar
    systemPoly k := groupRingEval (universalChar lam) ((Y k).element J)
    datumPoint := x
    systemPoint := x'
    le_ellVal_datumPoint := hx
    le_ellVal_systemPoint := hx'
    ellVal_datumPoly_le := hP_val
    ellVal_systemPoly_le := hx'_val
    groupRingEval_eq_eval ζ hζ k := (coe_eval_groupRingEval_universalChar lam hζ _).symm
    length_le ζ hζ i h_lt :=
      (T i).twistedLengthLe_pointChar (hP_bound i) ζ hζ (h_lt.trans (hM i)) }⟩

/-- Let finitely many Selmer data `T i` and Stickelberger systems `Y k` be given, and let `g₀` lie
in an inertia group above a place of `S₀` prime to `ℓ`. Let `M > β_T + 1` for all data and let the
residue field of `O` have more than `2 rank(T i) len(O / ℓ ^ M) + 1` elements (`IsTorsionLevel`).
There is an integer `s₀ ≥ 1` such that for every rational `r > 0` with `s₀ r < 1` and every large
`N` the following exist (`TwistPolynomials`), where `v(ℓ) = 1` and `β_T` and the lengths of Selmer
groups are scaled so that `O / ℓ` has length `1`.
* A set `Q` of at most `s₀ / 2` primes of prime norm that lie outside `S₀`, with conjugates outside
  `S₀` and `Q` (`IsAuxiliary`).
* For each `𝔮 ∈ Q` a homomorphism `λ_𝔮` to `ℤ / ℓ ^ N` that is onto on inertia at `𝔮` and comes by
  `y ↦ y / ȳ` from an idele class character of modulus `𝔮` trivial above `ℓ` (`IsFromU1`).
* For each datum and each system a polynomial `P` over `ℤ̄_ℓ` in variables `X_𝔮`, and a point with
  coordinates of valuation at least `r` at which `v(P) ≤ β + s₀ r`, for the number `β` of that datum
  or system.

For `ℓ ^ N`-th roots of unity `ζ_𝔮` put `ψ = ∏ ζ_𝔮 ^ λ_𝔮` and `x = (ζ_𝔮 - 1)_𝔮`. For a system,
`P(x)` is the value of `ψ` at its element `Θ_Q`. For a datum `T` with `v(P(x)) < β_T + 1`, the
Selmer group `Sel_Q(T ψ)` with divisible coefficients has length at most `v(P(x))`. -/
theorem exists_twistPolynomials (T : ∀ i : ι, SelmerDatum ℓ S₀ g₀ O.val (n i))
    (Y : κ → StickelbergerSystem ℓ S₀ g₀) [Finite ι] [Finite κ]
    (hg₀ : g₀ ∈ inertiaAbove (S₀ \ placesDividing E ℓ)) {M : ℕ} (hM : IsTorsionLevel T M) :
    ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ r : ℚ≥0, 0 < r → s₀ * r < 1 →
      ∀ᶠ N : ℕ in atTop, Nonempty (TwistPolynomials T Y s₀ r N) := by
  -- Descend all data at once, with the Frobenius element of the first prime near `g₀`, and take the
  -- polynomials and points of the resulting set of tied primes.
  obtain ⟨c, hc, h_rank, h_exps⟩ : ∃ c : ℕ,
      1 ≤ c ∧ (∀ i : ι, Fintype.card (n i) ≤ c) ∧ ∀ k : κ, (Y k).exponents.length ≤ c :=
    ((eventually_ge_atTop 1).and <| (eventually_all.2 fun _ ↦ eventually_ge_atTop _).and <|
      eventually_all.2 fun _ ↦ eventually_ge_atTop _).exists
  obtain ⟨M', hM'⟩ : ∃ M' : ℕ, ∀ k : κ, (Y k).β + 1 < M' :=
    (eventually_all.2 fun k ↦ ENNReal.tendsto_nat_nhds_top.eventually
      (lt_mem_nhds (by simp [(Y k).β_ne_top.lt_top]))).exists
  have h_near : ∀ᶠ g : Gal(Ω/E) in nhds g₀,
      (∀ (i : ι) (b : Bool), reduceModPow ℓ M (T i).ρ (idOrConjInv b g) =
        reduceModPow ℓ M (T i).ρ (idOrConjInv b g₀)) ∧
      ∀ k : κ, (M' : ℝ≥0∞) ≤ ellVal ((Y k).twistChar g - (Y k).twistChar g₀ : PadicAlgCl ℓ) :=
    (eventually_all.2 fun i ↦ eventually_all.2 ((T i).eventually_reduceModPow_idOrConjInv_eq M)).and
      (eventually_all.2 fun k ↦ (Y k).eventually_le_ellVal_sub M')
  obtain ⟨W, hW, h_frob⟩ := h_near.exists_mem
  obtain ⟨s, h_descent⟩ : ∃ s : ℕ, ∀ N > M, ∃ (P₀ : FinPlace E) (J : Finset (FinPlace E))
      (d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O.val)),
      IsTiedPrimes ℓ S₀ (fun i g ↦ reduceModPow ℓ M (T i).ρ g = 1) W N P₀ J d ∧ #J ≤ s ∧
      ∀ i : ι, length O.val ((T i).tiedSelmer J J d i (ℓ ^ M)) ≤ (T i).globalTerm +
        (T i).placesTerm :=
    exists_isTiedPrimes_card_le_and_length_le T hg₀ M hM.lt_card_residueField hW
  -- The bound `s` includes the first prime; the summand `1` only makes `s₀` positive.
  have hs₀ : 1 ≤ 2 * c * (1 + s) := Nat.succ_le_of_lt (by positivity)
  refine ⟨2 * c * (1 + s), hs₀, fun r hr₀ hr ↦ ?_⟩
  have h_large (K : ℕ) : ∀ᶠ N : ℕ in atTop, K ≤ N * r :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hr₀).eventually_ge_atTop _
  filter_upwards [eventually_gt_atTop M, h_large M, h_large M'] with N hMN hN hN'
  obtain ⟨P₀, J, d, h_primes, h_card, h_tied⟩ := h_descent N hMN
  obtain ⟨h_frob_datum, h_frob_system⟩ := h_frob _ h_primes.first_frob_mem
  exact nonempty_twistPolynomials_of_isTiedPrimes T Y h_primes h_tied h_frob_datum h_frob_system
    hM.β_lt hM' hc h_rank h_exps hs₀ (Nat.mul_le_mul_left _ (by omega)) hr hMN hN hN'

end New.Selmer

end
