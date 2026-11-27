module

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Lib.GaloisRep.BaseChange.CommutingHeckeFamilies
import Lib.Adelic.Adeles.StrongApproximation
import Lib.ClassField.Global.AlbertBrauerHasseNoether
import Lib.ClassField.Global.ArtinMap
import Lib.ClassField.Global.CMSplittingCharacters
import Lib.ClassField.Global.ExistenceTheorem
import Lib.ClassField.Global.NormTheorems
import Lib.GaloisRep.Hilbert90.TameActions
import Lib.GaloisRep.Hilbert90.UnitaryGroups
import Lib.General.LinearAlgebra.MatrixPolynomials
import Lib.General.NumberTheory.CMFields
import Mathlib.Algebra.FiniteSupport.Basic
public import Lib.Adelic.AutomorphicForms.SmoothAlgebraicForms
import Lib.Adelic.AutomorphicForms.HeckeEigenforms
import Lib.Adelic.Landherr
import Lib.Adelic.Reduction.DefiniteClassSums
import Lib.GLn.SchurModule.SchurNorm
import Lib.General.LinearAlgebra.PartnerAlgebra
import Lib.Shimura.TraceFormula.DefiniteTrace

section
/-!
# Idele Hasse principle, unitary roots and rationality of adelic roots up to coboundary

The main setting is a cyclic extension `E'/E` of CM fields of prime degree with character `μ`
(`New.IsStep`: `μ` kills `Eˣ`, and each idele `t` of `E` with `μ (t * star t) = 1` is a norm from
`E'` times an element of `Eˣ`) and Galois automorphism `σ`. For a unitary matrix `γ` and a
polynomial `z`, `New.IsRootQuotient γ z a` means `a * z(γ)ᴴ = z(γ)`. The file proves a Hasse
principle for ideles in a single CM field `L` and develops the calculus of this relation. It
combines the two to show that an adelic root for a `σ`-fixed characteristic polynomial is rational
up to a coboundary.

## Main definitions and results

* `New.exists_isSelfAdjoint_principalIdele_mul`: an adele `w` with `w = x * star w`, `x` in `L`,
  becomes conjugation invariant after multiplication by an element of `Lˣ`.
* `New.IsStep.exists_isSelfAdjoint_of_mem_kerCompNorm`: the twisted form, for an idele in
  `kerCompNorm L μ` whose norm under a Galois automorphism `g` has this property, where `x` is fixed
  by `g` and `E'[x] = ⊤`. It uses the Artin map, Hasse's norm theorem and Hilbert 90 for ideles.
* `New.U.existsUnique_isRootQuotient`: if `z(γ)` is invertible there is exactly one unitary `a`.
* `New.exists_global_root`: let `z` be a root for `P`, where `P` is the characteristic polynomial of
  a unitary matrix over `E'` and is fixed by `σ`. Then there are a rational `w` and an adelic `c`
  with the following property. Let `x = w * z * σ c`. At every adelic unitary `γ` killed by the
  radical of `P`, `x(γ)` is invertible, and `a = x(γ) / x(γ)ᴴ` satisfies `a * c(γ)ᴴ = c(γ)`.

Notions from other files:
* `New.adeleMap`: For an embedding f: K → L of number fields, the induced ring homomorphism from the
  finite adeles of K to those of L.
* `New.kerCompNorm`: The group of finite ideles of E' whose norm to E is killed by μ.
* `New.U.mapEnd`: The endomorphism of the unitary group {g : gᴴg = 1} over R given by applying
  entrywise a ring endomorphism σ commuting with the involution.

## Relation to the literature

Known; see `Lib.GaloisRep.BaseChange.PrimeDegreeTransfer` for sources.
-/

@[expose] public section

/-!
## The Hasse principle for ideles in one CM field

The Hasse principle behind `New.exists_global_root`, in a single CM field `L`.
-/

section IdeleHassePrinciple

open Subgroup NumberField Algebra IntermediateField New.Cohomology IsGalois ComplexEmbedding Finset

/-- Let `L` be a CM field. If the finite adele `w` satisfies `w = x * star w` with `x` in `L`, then
`y * w` is invariant under conjugation for some `y` in `Lˣ`. -/
lemma New.exists_isSelfAdjoint_principalIdele_mul {L : Type*} [Field L] [NumberField L]
    [IsCMField L] (x : L) {w : 𝔸f L} (hw : w = (x : 𝔸f L) * star w) :
    ∃ y : Lˣ, IsSelfAdjoint ((principalIdele y : (𝔸f L)ˣ) * w) := by
  -- Take `y = star (z + x * star z)` with `z + x * star z ≠ 0`. Since `star x * w = star w`,
  -- `y * w = star z * w + z * star w`, which is invariant under conjugation.
  have h_star : algebraMap L (𝔸f L) (star x) * w = star w := by simpa using (congrArg star hw).symm
  obtain ⟨z, hz⟩ : ∃ z : L, IsUnit (z + x * star z) := by
    -- `z = 1` works unless `x = -1`, and then any `z ≠ star z` works
    by_cases hx : x = -1
    · simpa [hx, sub_eq_add_neg] using exists_isUnit_sub_star (E := L)
    · refine ⟨1, Ne.isUnit fun h ↦ hx ?_⟩
      rw [star_one, mul_one] at h
      exact eq_neg_of_add_eq_zero_right h
  have h_mul : (principalIdele hz.star.unit : (𝔸f L)ˣ) * w =
      star (z : 𝔸f L) * w + (z : 𝔸f L) * star w := by
    -- with `star w = star x * w`, both sides are `(star z + star x * z) * w`
    have h_ring : (algebraMap L (𝔸f L) (star z) +
          algebraMap L (𝔸f L) (star x) * algebraMap L (𝔸f L) z) * w =
        algebraMap L (𝔸f L) (star z) * w +
          algebraMap L (𝔸f L) z * (algebraMap L (𝔸f L) (star x) * w) := by
      ring
    simpa [← h_star] using h_ring
  refine ⟨hz.star.unit, ?_⟩
  rw [h_mul]
  simp [IsSelfAdjoint, add_comm, mul_comm]

/-- The norm from `L` to the fixed field of `g` is the product of the conjugates under the powers
of `g`. -/
lemma New.finAdeleIncl_adeleNorm_fixedField_zpowers {E L : Type} [Field E] [NumberField E] [Field L]
    [NumberField L] [Algebra E L] (g : Gal(L/E)) (w : 𝔸f L) :
    finAdeleIncl (fixedField (zpowers g)) L (adeleNorm (fixedField (zpowers g)) L w) =
      ∏ i ∈ range (orderOf g), adeleMap (↑(g ^ i) : L →+* L) w := by
  have : IsGalois (fixedField (zpowers g)) L := of_fixed_field L (zpowers g)
  let e : Fin (orderOf g) ≃ Gal(L/fixedField (zpowers g)) :=
    (finEquivZPowers (isOfFinOrder_of_finite g)).trans (subgroupEquivAlgEquiv (zpowers g)).toEquiv
  rw [finAdeleIncl_adeleNorm, prod_range]
  exact (e.prod_comp fun σ ↦ adeleMap (σ : L →+* L) w).symm

/-- Let `K` be the fixed field of `g ∈ Gal(L/E)`, and let `t` be a finite idele of `L` whose norm to
`K` is the principal idele of a totally positive `k`. Then `z / t * g c = c` for some `z` in `Lˣ`
and some invertible finite adele `c`. -/
lemma New.exists_principalIdele_div_mul_adeleMap_eq {E L : Type} [Field E] [NumberField E] [Field L]
    [NumberField L] [Algebra E L] {g : Gal(L/E)} {t : (𝔸f L)ˣ} {k : (fixedField (zpowers g))ˣ}
    (hk_pos : IsTotallyPositive (k : fixedField (zpowers g)))
    (hk : principalIdele k = t.map (adeleNorm (fixedField (zpowers g)) L)) :
    ∃ (z : Lˣ) (c : 𝔸f L), IsUnit c ∧
      ↑(principalIdele z / t) * adeleMap (g : L →+* L) c = c := by
  let K : IntermediateField E L := fixedField (zpowers g)
  have : IsGalois K L := of_fixed_field L (zpowers g)
  have : IsCyclic Gal(L/K) := (subgroupEquivAlgEquiv (zpowers g)).isCyclic.mp (isCyclic_zpowers g)
  -- `k` is the norm of an idele of `L`, so a local norm everywhere, so a norm from `L`
  obtain ⟨z, rfl⟩ : ∃ z : Lˣ, z.map (norm K) = k := by
    refine hasse_norm k (fun v ↦ ?_) hk_pos
    have hk_v : algebraMap K (LocField v) k = adeleNorm K L t v :=
      congrArg (fun x : (𝔸f K)ˣ ↦ (x : 𝔸f K) v) hk
    rw [hk_v]
    exact adeleNorm_mem_closure
  -- `z / t` has norm one, so Hilbert 90 for ideles applies
  refine ⟨z, hilbert90_finite_idele ?_⟩
  rw [← finAdeleIncl_adeleNorm_fixedField_zpowers, ← Units.coe_map, map_div, ← hk,
    map_adeleNorm_principalIdele, div_self', Units.val_one, map_one]

/-- Let `L` be a CM field and `g` an automorphism of `L` over the CM field `E`. Then the fixed field
of `g` is a CM field: it is stable under conjugation, which commutes with `g`. -/
lemma New.isCMField_fixedField_zpowers {E L : Type} [Field E] [NumberField E] [IsCMField E]
    [Field L] [NumberField L] [IsCMField L] [Algebra E L] (g : Gal(L/E)) :
    IsCMField (fixedField (zpowers g)) := by
  refine isCMField_of_forall_exists_conj E fun y : fixedField (zpowers g) ↦
    ⟨⟨star y.val, fun a ↦ ?_⟩, fun φ ↦ ?_⟩
  · -- `star y` is fixed by `g`, as `y` is and conjugation commutes with `g`
    exact (map_star_CM a.val.toRingHom y).trans (congrArg star (y.property a))
  · simp [← lift_algebraMap_apply L φ]

/-- Hasse principle in one CM field. Let `E'/E` be a step with character `μ` (`IsStep`): `E`
contains a primitive 5040th root of unity, `E'` is a CM field Galois over `E` of prime degree, and
`μ` is a finite idele character of `E` with open kernel, trivial on `Eˣ`. Let `L = E'[x]` be a CM
field, and let `g ∈ Gal(L/E)` fix `x` and have order `n`. Let `u` be a finite idele of `L` with
`μ (N_{L/E} u) = 1` whose norm `N = ∏_{i < n} g ^ i u` satisfies `N = x * star N`. Then
`star c * (z * u * g c)` is self-adjoint for `star` for some `z` in `Lˣ` and some invertible finite
adele `c`. -/
lemma New.IsStep.exists_isSelfAdjoint_of_mem_kerCompNorm {E E' L : Type} [Field E] [NumberField E]
    [IsCMField E] [Field E'] [NumberField E'] [IsCMField E'] [Field L] [NumberField L] [IsCMField L]
    [Algebra E E'] [Algebra E' L] [Algebra E L] [IsScalarTower E E' L]
    {μ : (𝔸f E)ˣ →* ℂˣ} (hμ : IsStep E' μ) {g : Gal(L/E)} {x : L}
    (hx : g x = x) (hL : E'[x] = ⊤) (u : (𝔸f L)ˣ) (hu : u ∈ kerCompNorm L μ)
    (hN :
      let N : 𝔸f L := ∏ i ∈ range (orderOf g), adeleMap (↑(g ^ i) : L →+* L) u
      N = (x : 𝔸f L) * star N) :
    ∃ (z : Lˣ) (c : 𝔸f L), IsUnit c ∧
      IsSelfAdjoint (star c * (↑(principalIdele z * u) * adeleMap (g : L →+* L) c)) := by
  -- Let `K` be the fixed field of `g`. The norm of `u` to `K` is `a / y * (w * star w)`; class
  -- field theory shows that `w` is a norm from `L` up to `Kˣ`, say of `s`. Hasse's norm theorem
  -- and Hilbert 90 for ideles then write `z * u / (s * star s)` as a coboundary.
  let K : IntermediateField E L := fixedField (zpowers g)
  -- an embedding of `L` into `Ω` places all four fields inside `Ω`
  algebraize [Ω.fieldEmb L, (Ω.fieldEmb L).comp (algebraMap E L),
    (Ω.fieldEmb L).comp (algebraMap E' L)]
  have : IsScalarTower E E' Ω := IsScalarTower.to₁₂₄ E E' L Ω
  lift x to K using fun a ↦ smul_eq_self_of_mem_zpowers a.property hx
  have : IsGalois K L := of_fixed_field L (zpowers g)
  have h_cyc : IsCyclic Gal(L/K) :=
    (subgroupEquivAlgEquiv (zpowers g)).isCyclic.mp (isCyclic_zpowers g)
  have : IsCMField K := isCMField_fixedField_zpowers g
  have h_norm : finAdeleIncl K L (adeleNorm K L u) =
      ∏ i ∈ range (orderOf g), adeleMap (↑(g ^ i) : L →+* L) u :=
    finAdeleIncl_adeleNorm_fixedField_zpowers g u
  -- the hypothesis on the norm, pulled back from `L` to `K`
  have hN_map : adeleMap (algebraMap K L) (adeleNorm K L u) =
      adeleMap (algebraMap K L) (x * star (adeleNorm K L u)) := by
    simpa [adeleMap_star, h_norm] using hN
  have hN' : adeleNorm K L u = x * star (adeleNorm K L u) :=
    adeleMap_injective (algebraMap K L) hN_map
  -- `y` times the norm of `u` is invariant under conjugation, and such an idele of the CM field `K`
  -- has the form `a * (w * star w)` (`exists_eq_principalIdele_mul_mul_star_of_star_eq`)
  obtain ⟨y, hy⟩ := exists_isSelfAdjoint_principalIdele_mul x hN'
  let : CMType K := {}
  obtain ⟨a, w, hw⟩ : ∃ (a : Kˣ) (w : (𝔸f K)ˣ),
      principalIdele y * u.map (adeleNorm K L) = principalIdele a * (w * star w) :=
    exists_eq_principalIdele_mul_mul_star_of_star_eq hy
  -- the characters `χ`, `ψ` cut out `E' / E` and `L / K`
  obtain ⟨χ, hχ⟩ : ∃ χ : QZChar Gal(Ω/E), IsProGalois (QZChar.ker χ) E' Ω :=
    exists_isProGalois_ker_of_isCyclic (isCyclic_of_prime_card (card_aut_eq_finrank E E'))
  obtain ⟨ψ, hψ⟩ : ∃ ψ : QZChar Gal(Ω/K), IsProGalois (QZChar.ker ψ) L Ω :=
    exists_isProGalois_ker_of_isCyclic h_cyc
  -- `μ` kills `Eˣ` and the norm of `u`, hence the norm of `w * star w`; by the definition of a step
  -- the norm of `w` to `E` is then a norm from `E'` up to `Eˣ`
  have h_step : ∃ (b : Eˣ) (v : (𝔸f E')ˣ), IsTotallyPositive (b : E) ∧
      w.map (adeleNorm E K) = principalIdele b * v.map (adeleNorm E E') := by
    have h_tower : (adeleNorm E K).comp (adeleNorm K L) = adeleNorm E L :=
      MonoidHom.ext adeleNorm_adeleNorm
    -- the norm of `u` to `E` is that of `w * star w` times principal ideles, which `μ` kills
    have h_ww : μ (w.map (adeleNorm E K) * star (w.map (adeleNorm E K))) = 1 := by
      have h_eq : u.map (adeleNorm K L) =
          (principalIdele y)⁻¹ * (principalIdele a * (w * star w)) :=
        eq_inv_mul_of_mul_eq hw
      have h_u : μ ((u.map (adeleNorm K L)).map (adeleNorm E K)) = 1 := by
        change μ (u.map (adeleNorm E L)) = 1 at hu
        rwa [← h_tower, Units.map_comp] at hu
      rw [h_eq, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, map_mul,
        map_adeleNorm_principalIdele, map_adeleNorm_principalIdele,
        hμ.apply_principal, inv_one, one_mul, hμ.apply_principal, one_mul,
        units_map_adeleNorm_star] at h_u
      exact h_u
    obtain ⟨b, v, hbv⟩ := (hμ.apply_norm_eq_one_iff _).mp h_ww
    exact ⟨b, v, isTotallyPositive_of_isTotallyComplex _, hbv⟩
  -- the Artin symbol `f` of `w` fixes `E'` and `x`, hence all of `L = E'[x]`
  have h_art : New.QZChar.abelianLift ψ (artinMap Gal(Ω/K) w) = 1 := by
    obtain ⟨f, hf⟩ := Quot.exists_rep (artinMap Gal(Ω/K) w)
    -- `f` is also the symbol of the norm of `w` to `E`, so it lies in the kernel of `χ`, the
    -- subgroup that fixes `E'`
    have hf_norm : artinMap Gal(Ω/E) (w.map (adeleNorm E K)) = f.restrictScalars E :=
      artinMap_map_adeleNorm hf.symm 1 (fun _ ↦ rfl) fun _ ↦ rfl
    have hf_ker : New.QZChar.abelianLift χ ↑(f.restrictScalars E) = 1 := by
      rwa [← hf_norm, abelianLift_artinMap_eq_one_iff]
    obtain ⟨χ_ker, -⟩ : QZChar.ker χ = fixingSubgroup Gal(Ω/E) (Set.range (algebraMap E' Ω)) ∧
        (QZChar.ker χ).index = Module.finrank E E' :=
      eq_fixingSubgroup_of_isProGalois (J := hχ)
    obtain ⟨ψ_ker, -⟩ : QZChar.ker ψ = fixingSubgroup Gal(Ω/K) (Set.range (algebraMap L Ω)) ∧
        (QZChar.ker ψ).index = Module.finrank K L :=
      eq_fixingSubgroup_of_isProGalois (J := hψ)
    have hf_E' (t : E') : f (algebraMap E' Ω t) = algebraMap E' Ω t :=
      χ_ker.le hf_ker ⟨algebraMap E' Ω t, Set.mem_range_self t⟩
    let f' : L →ₐ[E'] Ω := ⟨f.toRingHom.comp (algebraMap L Ω), hf_E'⟩
    have hf_L (t : L) : f (algebraMap L Ω t) = algebraMap L Ω t :=
      AlgHom.adjoin_le_equalizer f' (algHom E' L Ω) (Set.eqOn_singleton.mpr (f.commutes x))
        (hL.ge trivial)
    rw [← hf]
    exact ψ_ker.ge fun ⟨_, t, rfl⟩ ↦ hf_L t
  -- so `w = b * N s` with `b` in `Kˣ` and `s` an idele of `L`, and `N (s * star s / u)` is in `Kˣ`
  obtain ⟨b, s, -, rfl⟩ := (abelianLift_artinMap_eq_one_iff ψ w).mp h_art
  obtain ⟨k, hk⟩ : ∃ k : Kˣ, principalIdele k = (s * star s / u).map (adeleNorm K L) := by
    refine ⟨y / (a * b * star b), ?_⟩
    rw [map_div, map_mul, map_mul, map_div, map_mul, units_map_adeleNorm_star,
      div_eq_div_iff_mul_eq_mul, hw, star_mul]
    have h_sb : star (principalIdele b) = principalIdele (star b) :=
      Units.ext (star_algebraMap_finAdele (b : K))
    rw [h_sb]
    set S := (Units.map (adeleNorm K L)) s
    rw [mul_comm (star S) (principalIdele (star b)),
      ← mul_assoc (principalIdele b * S), mul_assoc (principalIdele b) S,
      mul_comm S (principalIdele (star b)), ← mul_assoc (principalIdele b),
      mul_assoc (principalIdele b * principalIdele (star b)),
      ← mul_assoc (principalIdele a), ← mul_assoc (principalIdele a),
      mul_comm (principalIdele a * principalIdele b * principalIdele (star b))]
  obtain ⟨z, c, hc, h_cob⟩ : ∃ (z : Lˣ) (c : 𝔸f L), IsUnit c ∧
      ↑(principalIdele z / (s * star s / u)) * adeleMap (g : L →+* L) c = c :=
    exists_principalIdele_div_mul_adeleMap_eq (isTotallyPositive_of_isTotallyComplex _) hk
  -- `z * u * g c = s * star s * c`, so the product is `star c * (s * star s * c)`
  have h_split : principalIdele z * u = s * star s * (principalIdele z / (s * star s / u)) := by
    rw [div_div_eq_mul_div, mul_div_cancel]
  refine ⟨z, c, hc, ?_⟩
  rw [h_split, Units.val_mul, mul_assoc, h_cob]
  -- `star c * (s * star s * c)` is its own adjoint, as `𝔸f L` is commutative
  simp only [IsSelfAdjoint, star_mul, star_star, Units.val_mul, Units.coe_star]
  ring

end IdeleHassePrinciple

/-! ## Unitary roots, twisted norms and products of matching pairs -/

namespace New

open Matrix Polynomial U

variable {R : Type*} {S : Type*}
  {n : Type*} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]
  {γ γ' a c : U (1 : Matrix n n R)} {σ : R →+* R} {z w : R[X]} {p : ℕ} {u v : R} {D : Subgroup Rˣ}
  {x y : Matrix n n R} [CommRing S] [StarRing S]
  {hσ : ∀ (x : R), σ (star x) = star (σ x)}

/-- A unitary matrix commutes with its adjoint, which is its inverse. -/
instance : IsStarNormal γ.val.val where
  star_comm_self := by simp [commute_iff_eq, star, ← inv_val_eq_conjTranspose]

/-! ### Roots -/

/-- Suppose `γ * c = c * γ'` in the unitary group and `a` satisfies `a * z(γ')ᴴ = z(γ')`
(`New.IsRootQuotient`). Then the conjugate `c * a * c⁻¹` satisfies the same relation for `γ`
and `z`. -/
lemma U.isRootQuotient_conj (hc : γ * c = c * γ') (ha : IsRootQuotient γ' z a) :
    IsRootQuotient γ z ↑(c * a * c⁻¹) := by
  have h_semiconj : SemiconjBy c.val.val γ'.val.val γ.val.val :=
    congrArg (fun g : U (1 : Matrix n n R) ↦ g.val.val) hc.symm
  have h_conj : c.val.val * aeval γ'.val.val z * c.val⁻¹.val = aeval γ.val.val z :=
    c.val.mul_inv_eq_iff_eq_mul.mpr (aeval_semiconj h_semiconj z)
  have ha_conj : c.val.val * (a.val.val * (aeval γ'.val.val z)ᴴ) * c.val⁻¹.val =
      c.val.val * aeval γ'.val.val z * c.val⁻¹.val :=
    congrArg (fun M : Matrix n n R ↦ c.val.val * M * c.val⁻¹.val) ha
  -- As `c` is unitary, `cᴴ = c⁻¹` and the inner factors `c⁻¹ * c` cancel.
  simpa [← h_conj, ← inv_val_eq_conjTranspose, IsRootQuotient, mul_assoc,
    conjTranspose_nonsing_inv] using ha_conj

/-- Let `f` be a ring homomorphism commuting with the involutions. If `a * z(γ)ᴴ = z(γ)`, then
applying `f` to `γ`, to `a` and to the coefficients of `z` preserves this relation. -/
lemma U.isRootQuotient_map {f : R →+* S} (hf : ∀ x : R, f (star x) = star (f x))
    (h_root : IsRootQuotient γ z a) :
    IsRootQuotient (map f hf (one_map_ringHom f) γ) (z.map f)
      (map f hf (one_map_ringHom f) a : U (1 : Matrix n n S)) := by
  have h_map : (a.val.val * (aeval γ.val.val z)ᴴ).map f = (aeval γ.val.val z).map f :=
    congrArg (fun M : Matrix n n R ↦ M.map f) h_root
  change (a.val.val).map f * (aeval ((γ.val.val).map f) (z.map f))ᴴ =
    aeval ((γ.val.val).map f) (z.map f)
  simpa [conjTranspose_map _ hf, map_aeval_matrix] using h_map

/-- If `z(γ)` is invertible, exactly one unitary `a` satisfies `a * z(γ)ᴴ = z(γ)`
(`New.IsRootQuotient`), namely `z(γ) * (z(γ)ᴴ)⁻¹`. -/
lemma U.existsUnique_isRootQuotient (h_unit : IsUnit (aeval γ.val.val z)) :
    ∃! a : U 1, IsRootQuotient γ z a.val.val := by
  let h_invertible : Invertible (aeval γ.val.val z) := h_unit.invertible
  -- The root is `z(γ) / z(γ)ᴴ`, which is unitary as `z(γ)` commutes with its adjoint.
  have h_unitary :
      (aeval γ.val.val z * ⅟(aeval γ.val.val z)ᴴ)ᴴ * 1 *
        (aeval γ.val.val z * ⅟(aeval γ.val.val z)ᴴ) = 1 := by
    simp [commute_conjTranspose_aeval, Commute.left_comm, conjTranspose_nonsing_inv, mul_assoc]
  refine ⟨of isUnit_one _ h_unitary,
    invOf_mul_cancel_right (aeval γ.val.val z) (aeval γ.val.val z)ᴴ, fun b hb ↦ ?_⟩
  exact Subtype.ext (Units.ext (mul_right_eq_iff_eq_mul_invOf.mp hb))

/-- If `x * z(γ)ᴴ = z(γ)` and `y * w(γ)ᴴ = w(γ)`, then `(x * y) * (z * w)(γ)ᴴ = (z * w)(γ)`: the
values of polynomials at `γ` commute with their adjoints. -/
lemma IsRootQuotient.mul (hx : IsRootQuotient γ z x) (hy : IsRootQuotient γ w y) :
    IsRootQuotient γ (z * w) (x * y) := by
  have h_comm :
      (aeval γ.val.val z)ᴴ * aeval γ.val.val w = aeval γ.val.val w * (aeval γ.val.val z)ᴴ :=
    (commute_conjTranspose_aeval γ.val.val).eq
  change x * y * (aeval γ.val.val (z * w))ᴴ = aeval γ.val.val (z * w)
  rw [map_mul, conjTranspose_mul, mul_assoc, ← mul_assoc y, hy, ← mul_assoc, mul_assoc x,
    ← h_comm, ← mul_assoc, hx]

/-! ### Matching pairs and norms -/

/-- Let `u`, `v` be orthogonal self-adjoint idempotents. If `(f, φ)` is a matching pair for `u` and
level `K` and `(f', φ')` one for `v` and level `L`, then the products `(f * f', φ * φ')` form a
matching pair for `u + v` and level `K ⊓ L`. -/
lemma IsMatchingPair.mul {A : Type*} {j : A → U (1 : Matrix n n R)}
    {K L : Subgroup (U (1 : Matrix n n R))} {f f' : A → ℂ} {φ φ' : U (1 : Matrix n n R) → ℂ}
    (h : IsMatchingPair hσ p u D j K f φ) (h' : IsMatchingPair hσ p v D j L f' φ')
    (huv : u * v = 0) (hu_idem : u * u = u) (hv_idem : v * v = v) (hu_star : star u = u)
    (hv_star : star v = v) :
    IsMatchingPair hσ p (u + v) D j (K ⊓ L) (f * f') (φ * φ') := by
  -- For orthogonal idempotents `u`, `v` the product `z * w` of the two roots is a root for `u + v`:
  -- it is `z` on the part cut out by `u`, `w` on the part cut out by `v`, and `1` elsewhere.
  obtain ⟨h_inv, h_match⟩ := h
  obtain ⟨h'_inv, h'_match⟩ := h'
  refine ⟨fun k hk δ ↦ ?_, fun P hP hPσ ↦ ?_⟩
  · -- Invariance under `K ⊓ L` holds factor by factor.
    obtain ⟨hk_K, hk_L⟩ : k ∈ K ∧ k ∈ L := Subgroup.mem_inf.mp hk
    simp only [Pi.mul_apply, h_inv k hk_K δ, h'_inv k hk_L δ]
  -- The supports of the products lie in those of the factors.
  have hP_of_support {f₀ : A → ℂ} {φ₀ : U (1 : Matrix n n R) → ℂ}
      (hf : (f * f').support ⊆ f₀.support) (hφ : (φ * φ').support ⊆ φ₀.support) :
      P ∈ (fun g : U (1 : Matrix n n R) ↦ g.val.val.charpoly) ''
        (j '' f₀.support ∪ twistedNorm (mapEnd hσ) p '' φ₀.support) :=
    Set.image_mono (Set.union_subset_union (Set.image_mono hf) (Set.image_mono hφ)) hP
  obtain ⟨z, ⟨hz_off, hz_root⟩, hz_match⟩ := h_match P (hP_of_support
    (Function.support_mul_subset_left f f') (Function.support_mul_subset_left φ φ')) hPσ
  obtain ⟨w, ⟨hw_off, hw_root⟩, hw_match⟩ := h'_match P (hP_of_support
    (Function.support_mul_subset_right f f') (Function.support_mul_subset_right φ φ')) hPσ
  refine ⟨z * w, ⟨?_, fun γ hγ ↦ ⟨?_, ?_⟩⟩, fun γ r hγ hr ↦ ?_⟩
  · -- `(1 - u) (1 - v) = 1 - (u + v)`.
    have h_off_mul : (1 - u) • z * (1 - v) • w = (1 - u) • (1 : R[X]) * (1 - v) • (1 : R[X]) := by
      rw [hz_off, hw_off]
    have h1uv : (1 - u) * (1 - v) = 1 - (u + v) := by
      rw [sub_mul, one_mul, mul_sub, mul_one, huv, sub_zero, sub_sub, add_comm v u]
    rw [smul_mul_smul, smul_mul_smul, mul_one, h1uv] at h_off_mul
    exact h_off_mul
  · -- The determinant of `(z * w)(γ)` is a product of two elements of `D`.
    intro m A hA
    obtain ⟨a, ha, ha_eq⟩ := (hz_root γ hγ).1 m A hA
    obtain ⟨b, hb, hb_eq⟩ := (hw_root γ hγ).1 m A hA
    exact ⟨a * b, D.mul_mem ha hb, by
      rw [map_mul, ha_eq, hb_eq, map_mul, det_mul]⟩
  · -- `(1 + u (γ - 1)) (1 + v (γ - 1)) = 1 + (u + v) (γ - 1)`.
    obtain ⟨-, hz_norm⟩ := hz_root γ hγ
    obtain ⟨-, hw_norm⟩ := hw_root γ hγ
    have h_norm_mul : twistedNorm (Polynomial.map σ) p (z * w) =
        twistedNorm (Polynomial.map σ) p z * twistedNorm (Polynomial.map σ) p w := by
      simp only [twistedNorm_map_eq_prod, Polynomial.map_mul, Finset.prod_mul_distrib]
    have h_factor : (1 + u • (γ.val.val - 1)) * (1 + v • (γ.val.val - 1)) =
        1 + (u + v) • (γ.val.val - 1) := by
      rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul, huv, zero_smul,
        add_zero, add_smul, add_assoc, add_comm (v • _)]
    rw [h_norm_mul, ← h_factor]
    exact hz_norm.mul hw_norm
  · -- A quotient `r` for `(u + v) z w` is one for `u z` and one for `v w`.
    have hw_off_u : z * u • ((1 - v) • w) = z * u • ((1 - v) • (1 : R[X])) := by
      rw [hw_off]
    have hz_off_v : v • ((1 - u) • z) * w = v • ((1 - u) • (1 : R[X])) * w := by
      rw [hz_off]
    have huzw : u • (z * w) = u • z := by
      rw [smul_smul, smul_smul, mul_sub, mul_one, huv, sub_zero, mul_smul_comm, mul_smul_comm,
        mul_one] at hw_off_u
      exact hw_off_u
    have hvzw : v • (z * w) = v • w := by
      rw [smul_smul, smul_smul, mul_sub, mul_one, mul_comm v u, huv, sub_zero, smul_mul_assoc,
        smul_mul_assoc, one_mul] at hz_off_v
      exact hz_off_v
    -- multiply the relation for `(u + v) • (z * w)` by `e = u`, and by `e = v`
    have hr_part {e : R} {f₀ : R[X]} (he : e * (u + v) = e) (he_star : star e = e)
        (h_part : e • (z * w) = e • f₀) : IsRootQuotient γ (e • f₀) r.val := by
      rw [← h_part]
      have h_e := congrArg (fun M : Matrix n n R ↦ e • M) hr
      change r.val * (aeval γ.val.val (e • (z * w)))ᴴ = aeval γ.val.val (e • (z * w))
      rw [smul_eq_C_mul, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        conjTranspose_smul, he_star]
      have h_lhs : e • (r.val * (aeval γ.val.val ((u + v) • (z * w)))ᴴ) =
          r.val * (e • (aeval γ.val.val (z * w))ᴴ) := by
        rw [smul_eq_C_mul, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
          one_mul, conjTranspose_smul, star_add, hu_star, hv_star, mul_smul_comm, smul_smul, he,
          mul_smul_comm]
      have h_rhs : e • aeval γ.val.val ((u + v) • (z * w)) = e • aeval γ.val.val (z * w) := by
        rw [smul_eq_C_mul, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
          one_mul, smul_smul, he]
      rw [h_lhs, h_rhs] at h_e
      exact h_e
    have hu_sum : u * (u + v) = u := by rw [mul_add, hu_idem, huv, add_zero]
    have hv_sum : v * (u + v) = v := by rw [mul_add, mul_comm v u, huv, hv_idem, zero_add]
    have hr_u : IsRootQuotient γ (u • z) r.val := hr_part hu_sum hu_star huzw
    have hr_v : IsRootQuotient γ (v • w) r.val := hr_part hv_sum hv_star hvzw
    refine ⟨fun g hg hnorm ↦ ?_, fun δ hδ hne ↦ ?_⟩
    · simp only [Pi.mul_apply, (hz_match γ r hγ hr_u).1 g hg hnorm,
        (hw_match γ r hγ hr_v).1 g hg hnorm]
    · exact ⟨(hz_match γ r hγ hr_u).2 δ hδ (left_ne_zero_of_mul hne),
        (hw_match γ r hγ hr_v).2 δ hδ (right_ne_zero_of_mul hne)⟩

/-- Let `z(γ)` be invertible, and let `a * z(γ)ᴴ = z(γ)`. Let `γ * N(γ)ᴴ = N(γ)` for
`N = twistedNorm (.map σ) p z = z * σ(z) * ⋯ * σ^(p-1)(z)` (likewise `twistedNorm (mapEnd hσ) p
c = c * σ(c) * ⋯ * σ^(p-1)(c)`), and let `c` conjugate `σ γ` to `γ`. Then the twisted norm of `c` is
`γ` times that of `a⁻¹ * c`. -/
lemma IsRootQuotient.twistedNorm_eq_mul
    (h_norm : IsRootQuotient γ (twistedNorm (Polynomial.map σ) p z) γ)
    (h_conj : γ * c = c * mapEnd hσ γ) (h_root_a : IsRootQuotient γ z a)
    (h_isUnit : IsUnit (aeval γ.val.val z)) :
    twistedNorm (mapEnd hσ) p c = γ * twistedNorm (mapEnd hσ) p (a⁻¹ * c) := by
  -- By induction on `q`, the quotient of the two norms of length `q` is the root for the norm
  -- of `z` of length `q`, whose value at `γ` is a unit. For `q = p` roots are unique.
  have h_quotient_root (q : ℕ) :
      IsUnit (aeval γ.val.val (twistedNorm (.map σ) q z)) ∧
      IsRootQuotient γ (twistedNorm (.map σ) q z)
        ↑(twistedNorm (mapEnd hσ) q c * (twistedNorm (mapEnd hσ) q (a⁻¹ * c))⁻¹) := by
    induction q with
    | zero => simp [twistedNorm, IsRootQuotient]
    | succ q ih =>
      obtain ⟨ih_unit, ih_root⟩ := ih
      -- Apply `σ`, conjugate by `c` back to `γ`, and multiply by the root `a` of `z`.
      have h_unit : IsUnit (c.val.val * σ.mapMatrix (aeval γ.val.val (twistedNorm (.map σ) q z))) :=
        c.val.isUnit.mul (ih_unit.map σ.mapMatrix)
      have h_root :
          IsRootQuotient γ ((twistedNorm (.map σ) q z).map σ * z)
            ((c *
              mapEnd hσ (twistedNorm (mapEnd hσ) q c * (twistedNorm (mapEnd hσ) q (a⁻¹ * c))⁻¹) *
              c⁻¹).val.val * a.val.val) :=
        (isRootQuotient_conj h_conj (isRootQuotient_map hσ ih_root)).mul h_root_a
      have h_succ : twistedNorm (Polynomial.map σ) (q + 1) z =
          (twistedNorm (Polynomial.map σ) q z).map σ * z :=
        (twistedNorm_succ' (mapRingHom σ).toMonoidHom q z).trans (mul_comm _ _)
      rw [h_succ]
      have h_semiconj : SemiconjBy c.val.val (γ.val.val.map σ) γ.val.val :=
        congrArg (fun g : U (1 : Matrix n n R) ↦ g.val.val) h_conj.symm
      refine ⟨?_, ?_⟩
      · rw [map_mul]
        have h_unit' : IsUnit (aeval γ.val.val ((twistedNorm (.map σ) q z).map σ)) := by
          have h_conj_eq : aeval γ.val.val ((twistedNorm (.map σ) q z).map σ) =
              c.val.val * σ.mapMatrix (aeval γ.val.val (twistedNorm (.map σ) q z)) *
                c.val⁻¹.val := by
            rw [RingHom.mapMatrix_apply, map_aeval_matrix, aeval_semiconj h_semiconj,
              mul_assoc, Units.mul_inv, mul_one]
          rw [h_conj_eq]
          exact h_unit.mul c.val⁻¹.isUnit
        exact h_unit'.mul h_isUnit
      · have h_grp :
            (c * mapEnd hσ (twistedNorm (mapEnd hσ) q c * (twistedNorm (mapEnd hσ) q (a⁻¹ * c))⁻¹) *
              c⁻¹) * a =
            twistedNorm (mapEnd hσ) (q + 1) c * (twistedNorm (mapEnd hσ) (q + 1) (a⁻¹ * c))⁻¹ := by
          rw [twistedNorm_succ', twistedNorm_succ', map_mul, map_inv, _root_.mul_inv_rev,
            _root_.mul_inv_rev, inv_inv]
          group
        rw [← h_grp]
        exact h_root
  obtain ⟨h_unit_p, h_root_p⟩ := h_quotient_root p
  exact eq_mul_of_mul_inv_eq ((existsUnique_isRootQuotient h_unit_p).unique h_root_p h_norm)

end New

/-!
## Rationality of adelic roots up to a coboundary

The global step of the comparison of traces for a cyclic extension `E'/E` of prime degree
(`New.IsStep`, with its character `μ`). A root (`New.IsNormRoot`) for a polynomial `P` is an adelic
polynomial `z` whose `σ`-norm `N` satisfies `γ = N(γ) / N(γ)ᴴ` at unitary `γ` with characteristic
polynomial `P`, with a determinant condition given by `μ`.

The proof of `New.exists_global_root` works in the CM fields `E'[X] / (q)` for the prime factors `q`
of `P`, applies the Hasse principle `New.IsStep.exists_isSelfAdjoint_of_mem_kerCompNorm` at each
prime factor fixed by `σ`, and glues along the orbits of `σ`.
-/

section GlobalRoot

open NumberField Matrix Polynomial UniqueFactorizationMonoid AdjoinRoot MulAction Function
  Norms.L2Operator Algebra AlgEquiv MulDistribMulAction Ideal ComplexConjugate Ring

/-- If `v(γ)` inverts the unitary matrix `γ`, the adjoint of `f(γ)` is obtained by conjugating the
coefficients of `f` and substituting `v` for `X`. -/
lemma New.U.conjTranspose_aeval {R n : Type} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]
    {γ : U (1 : Matrix n n R)} {v : R[X]}
    (hv : aeval (γ : Matrix n n R) v * (γ : Matrix n n R) = 1) (f : R[X]) :
    (aeval (γ : Matrix n n R) f)ᴴ = aeval (γ : Matrix n n R) ((f.map conj).comp v) := by
  have h_inv : (γ : Matrix n n R)ᴴ = aeval (γ : Matrix n n R) v := by
    simpa [star_eq_conjTranspose] using left_inv_eq_left_inv
        (mem_unitaryGroupOf_iff.1 γ.property) hv
  calc (aeval (γ : Matrix n n R) f)ᴴ = aeval (γ : Matrix n n R)ᴴ (f.map conj) :=
        star_aeval (R := R) (γ : Matrix n n R) f
    _ = aeval (γ : Matrix n n R) ((f.map conj).comp v) := by rw [h_inv, aeval_comp]

/-- The complex eigenvalues of a unitary matrix over a CM field have absolute value `1`. -/
lemma New.U.mul_star_eq_one_of_isRoot_charpoly {K n : Type} [Field K] [NumberField K]
    [IsCMField K] [Fintype n] [DecidableEq n] (γ : U (1 : Matrix n n K)) (φ : K →+* ℂ) {x : ℂ}
    (hx : ((γ : Matrix n n K).charpoly.map φ).IsRoot x) : x * star x = 1 := by
  have h_eigen : x ∈ spectrum ℂ ((γ : Matrix n n K).map φ) := by
    rw [← charpoly_map] at hx
    exact mem_spectrum_of_isRoot_charpoly hx
  have h_unitary : (γ : Matrix n n K).map φ ∈ unitaryGroup n ℂ :=
    U_one_mem_unitaryGroup (U.map φ (by simp) (one_map_ringHom φ) γ)
  exact Unitary.mul_star_self_of_mem (spectrum_subset_unitary_of_mem_unitary h_unitary h_eigen)

open scoped Classical in
/-- The Chinese remainder theorem for the prime factors of `P`, after a change of coefficients. -/
lemma New.exists_forall_map_dvd_sub {K S : Type} [Field K] [CommRing S] (f : K →+* S) (P : K[X])
    (x : primeFactors P → S[X]) : ∃ r : S[X], ∀ q : primeFactors P, q.val.map f ∣ r - x q := by
  have h_coprime : Pairwise fun q q' : primeFactors P ↦
      IsCoprime (span {q.val.map f}) (span {q'.val.map f}) := by
    intro q q' h_ne
    have h_rel : IsRelPrime q.val q'.val :=
      pairwise_primeFactors_isRelPrime q.property q'.property (Subtype.coe_injective.ne h_ne)
    rw [isCoprime_span_singleton_iff]
    exact h_rel.isCoprime.map (mapRingHom f)
  obtain ⟨r, hr⟩ : ∃ r : S[X], ∀ q : primeFactors P, r - x q ∈ span {q.val.map f} :=
    exists_forall_sub_mem_ideal h_coprime x
  exact ⟨r, fun q ↦ mem_span_singleton.mp (hr q)⟩

open scoped Classical in
/-- Polynomials congruent modulo every prime factor of `P` agree at an element killed by the
radical of `P`. -/
lemma New.aeval_eq_of_forall_map_dvd_sub {K S A : Type} [Field K] [CommRing S] [Ring A]
    [Algebra S A] (f : K →+* S) {P : K[X]} {a : A}
    (ha : aeval a ((UniqueFactorizationMonoid.radical P).map f) = 0) {g g' : S[X]}
    (hg : ∀ q ∈ primeFactors P, q.map f ∣ g - g') : aeval a g = aeval a g' := by
  have h_coprime : (primeFactors P : Set K[X]).Pairwise fun q q' ↦ IsCoprime (q.map f) (q'.map f) :=
    pairwise_primeFactors_isRelPrime.imp fun q q' h_rel ↦ h_rel.isCoprime.map (mapRingHom f)
  have h_dvd : ∏ q ∈ primeFactors P, q.map f ∣ g - g' := Finset.prod_dvd_of_coprime h_coprime hg
  -- the radical of `P` is the product of its prime factors
  have h_rad_dvd : (radical P).map f ∣ g - g' := by
    rw [UniqueFactorizationMonoid.radical, Polynomial.map_prod]
    exact h_dvd
  have h_zero : aeval a (g - g') = 0 := aeval_eq_zero_of_dvd_aeval_eq_zero h_rad_dvd ha
  rwa [map_sub, sub_eq_zero] at h_zero

/-- Each orbit of a permutation `τ` of a finite type has a representative `r a`, and the position
`j a` of `a` on its orbit, counted from `r a`, grows by one modulo the period under `τ`. -/
lemma New.exists_orbit_representatives {α : Type} [Finite α] (τ : α ≃ α) :
    ∃ (r : α → α) (j : α → ℕ),
      (∀ a : α, r (τ a) = r a) ∧
      (∀ a : α, j a < minimalPeriod τ (r a)) ∧
      (∀ a : α, a = τ^[j a] (r a)) ∧
      ∀ a : α, j (τ a) = (j a + 1) % minimalPeriod τ (r a) := by
  let r (a : α) : α :=
    haveI : Nonempty α := ⟨a⟩
    invFun (periodicOrbit τ) (periodicOrbit τ a)
  have h_mem (a : α) : r (τ a) = r a ∧ a ∈ periodicOrbit τ (r a) := by
    simp [r, τ.injective.mem_periodicPts, invFun_eq, periodicOrbit_apply_eq]
  have h_orbit (a : α) : r (τ a) = r a ∧ ∃ j < minimalPeriod τ (r a), a = τ^[j] (r a) := by
    simpa [periodicOrbit] using h_mem a
  choose r_τ j j_lt hr using h_orbit
  refine ⟨r, j, r_τ, j_lt, hr, fun a ↦ ?_⟩
  rw [← r_τ a]
  -- both sides are the position of `τ a` on the orbit of `r (τ a)`
  have h_iter : τ^[j (τ a)] (r (τ a)) = τ^[(j a + 1) % minimalPeriod τ (r (τ a))] (r (τ a)) := by
    rw [← hr (τ a), iterate_mod_minimalPeriod_eq, r_τ, iterate_succ_apply', ← hr a]
  exact iterate_injOn_Iio_minimalPeriod (j_lt (τ a)) (Nat.mod_lt _ (j_lt (τ a)).pos) h_iter

/-- Transport along the orbits of `τ`. Let `θ a` read `B` in a star ring `A a`, with
`θ (τ a) (T b) = u (τ a) * g a (θ a b)` for units `u`. If at each `a` some `b` with `θ a b` a unit
and `y` in `Y a` make `star (θ a b) * (ι a y * θ a (T^[period of a] b))` self-adjoint, then some
`y a`, `c a` make `ι a (y a) * θ a (T b)` a unit and `star (θ a b)` times it self-adjoint, at every
`a`, whenever `θ a b = θ a (c a)` for all `a`. -/
lemma New.exists_isSelfAdjoint_along_orbits {α B : Type} [Finite α] {A Y : α → Type}
    [∀ a : α, CommRing (A a)] [∀ a : α, StarRing (A a)] [∀ a : α, Monoid (Y a)] (τ : α ≃ α)
    (θ : ∀ a : α, B → A a) (ι : ∀ a : α, Y a →* (A a)ˣ) (g : ∀ a : α, A a →+* A (τ a))
    {u : ∀ a : α, A a} (hu : ∀ a : α, IsUnit (u a)) {T : B → B}
    (hT : ∀ (a : α) (b : B), θ (τ a) (T b) = u (τ a) * g a (θ a b))
    (h_period : ∀ a : α, ∃ (y : Y a) (b : B), IsUnit (θ a b) ∧
      IsSelfAdjoint (star (θ a b) * ((ι a y).val * θ a (T^[minimalPeriod τ a] b)))) :
    ∃ (y : ∀ a : α, Y a) (c : α → B), ∀ b : B, (∀ a : α, θ a b = θ a (c a)) → ∀ a : α,
      IsUnit ((ι a (y a)).val * θ a (T b)) ∧
        IsSelfAdjoint (star (θ a b) * ((ι a (y a)).val * θ a (T b))) := by
  -- With `a = τ^[j a] (r a)`, take `c a = T^[j a] (b₀ (r a))`, and the given factor at the
  -- representatives of the orbits, `1` elsewhere.
  choose y b₀ b₀_unit b₀_adj using h_period
  obtain ⟨r, j, r_τ, j_lt, hr, j_succ⟩ := exists_orbit_representatives τ
  refine ⟨fun a ↦ if j a = 0 then y a else 1, fun a ↦ T^[j a] (b₀ (r a)), fun b hb a ↦ ?_⟩
  obtain ⟨a, rfl⟩ := τ.surjective a
  have T_unit (i : ℕ) : IsUnit (θ (τ^[i] (r a)) (T^[i] (b₀ (r a)))) := by
    induction i with
    | zero => exact b₀_unit _
    | succ i ih =>
      rw [iterate_succ_apply', iterate_succ_apply', hT]
      exact (hu _).mul (ih.map _)
  have τ_eq : τ a = τ^[j a + 1] (r a) := by rw [iterate_succ_apply', ← hr]
  have T_eq : θ (τ a) (T b) = θ (τ a) (T^[j a + 1] (b₀ (r a))) := by
    rw [hT, hb, ← hT, iterate_succ_apply']
  have T_succ_unit : IsUnit (θ (τ a) (T^[j a + 1] (b₀ (r a)))) := by
    rw [τ_eq]
    exact T_unit _
  beta_reduce at hb ⊢
  rw [T_eq, hb, r_τ]
  refine ⟨(Units.isUnit _).mul T_succ_unit, ?_⟩
  obtain h_eq | h_lt := Nat.eq_or_lt_of_le (j_lt a)
  · -- `τ a` is the representative
    have hj : j (τ a) = 0 := by rw [j_succ, Nat.add_one, h_eq, Nat.mod_self]
    have h_back : τ a = r a := by rw [τ_eq, Nat.add_one, h_eq, iterate_minimalPeriod]
    rw [ite_eq_left hj, hj, Nat.add_one, h_eq, h_back]
    exact b₀_adj (r a)
  · -- elsewhere the element has the form `star t * t`
    have hj : j (τ a) = j a + 1 := by rw [j_succ, Nat.mod_eq_of_lt h_lt]
    rw [hj, ite_eq_right (Nat.succ_ne_zero _), map_one, Units.val_one, one_mul]
    exact .star_mul_self _

/-- An automorphism of `E'[X] / (q)` that extends `σ` and fixes the root has the prime order
of `σ`. -/
lemma New.orderOf_eq_of_semiconj {E E' : Type} [Field E] [Field E'] [Algebra E E'] {p : ℕ}
    (hp : p.Prime) {σ : Gal(E'/E)} (hσ_pow : σ ^ p = 1) (hσ : σ ≠ 1) {q : E'[X]}
    [Fact (Irreducible q)] {g : AdjoinRoot q ≃ₐ[E] AdjoinRoot q} (hg : Semiconj (of q) σ g)
    (hg_root : g (root q) = root q) : orderOf g = p := by
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have g_pow : g ^ p = 1 := by
    apply coe_toAlgHom_injective
    ext
    · simp [← coe_pow σ, ← hg.iterate_right p _, hσ_pow]
    · simp [iterate_fixed hg_root]
  have g_ne : g ≠ 1 := by
    intro h_one
    apply hσ
    ext x
    have h_of : of q (σ x) = of q x := by simpa [h_one] using hg x
    exact coe_injective' h_of
  exact orderOf_eq_prime g_pow g_ne

/-- If `γ * N(γ)ᴴ = N(γ)` and `v(γ)` inverts `γ`, the same relation holds for the polynomial `N`
up to nilpotents modulo the characteristic polynomial of `γ`. -/
lemma New.IsRootQuotient.charpoly_dvd_pow {R n : Type} [CommRing R] [StarRing R] [Fintype n]
    [DecidableEq n] {γ : U (1 : Matrix n n R)} {v N : R[X]}
    (hv : aeval (γ : Matrix n n R) v * (γ : Matrix n n R) = 1)
    (hN : IsRootQuotient γ N (γ : Matrix n n R)) :
    (γ : Matrix n n R).charpoly ∣ (X * (N.map conj).comp v - N) ^ Fintype.card n := by
  let D : R[X] := X * (N.map conj).comp v - N
  have h_vanish : aeval (γ : Matrix n n R) D = 0 := by
    rw [map_sub, map_mul, aeval_X, ← U.conjTranspose_aeval hv, hN, sub_self]
  -- `charpoly γ` divides `(charpoly D(γ)).comp D`, and `charpoly 0 = X ^ Fintype.card n`
  have h_dvd : (γ : Matrix n n R).charpoly ∣ (aeval (γ : Matrix n n R) D).charpoly.comp D :=
    charpoly_dvd_charpoly_aeval_comp D
  rwa [h_vanish, charpoly_zero, X_pow_comp] at h_dvd

/-- Let the maps `θ i` detect equality of values at `γ`, and let `β` represent both the adjoint at
`γ` and `star` under each `θ i`. If `x` has an inverse `x'` and `star c * x` is self-adjoint
under every `θ i`, then `x(γ)` is invertible, and every `a` with `a * x(γ)ᴴ = x(γ)` also has
`a * c(γ)ᴴ = c(γ)`. -/
lemma New.isUnit_and_isRootQuotient_of_isSelfAdjoint {R n ι : Type} [CommRing R] [StarRing R]
    [Fintype n] [DecidableEq n] {A : ι → Type} [∀ i : ι, CommRing (A i)]
    [∀ i : ι, StarRing (A i)] [∀ i : ι, Algebra R (A i)] {γ : U (1 : Matrix n n R)}
    (θ : ∀ i : ι, R[X] →ₐ[R] A i)
    (h_glue : ∀ {f f' : R[X]}, (∀ i : ι, θ i f = θ i f') →
      aeval (γ : Matrix n n R) f = aeval (γ : Matrix n n R) f')
    {β : R[X] → R[X]}
    (hβ_adjoint : ∀ f : R[X], (aeval (γ : Matrix n n R) f)ᴴ = aeval (γ : Matrix n n R) (β f))
    (hβ_star : ∀ (i : ι) (f : R[X]), θ i (β f) = star (θ i f)) {x x' c : R[X]}
    (h_inv : ∀ i : ι, θ i x * θ i x' = 1)
    (h_adj : ∀ i : ι, IsSelfAdjoint (star (θ i c) * θ i x)) :
    IsUnit (aeval (γ : Matrix n n R) x) ∧
      ∀ a : Matrix n n R, IsRootQuotient γ x a → IsRootQuotient γ c a := by
  have h_inv_γ : aeval (γ : Matrix n n R) x * aeval (γ : Matrix n n R) x' = 1 := by
    simpa only [map_mul, map_one] using
      (h_glue (f := x * x') (f' := 1) fun i ↦ by rw [map_mul, h_inv, map_one])
  refine ⟨.of_mul_eq_one _ h_inv_γ, fun a ha ↦ ?_⟩
  have β_eq : aeval (γ : Matrix n n R) (β c) = aeval (γ : Matrix n n R) (β x * (c * x')) := by
    refine h_glue fun i ↦ ?_
    have h_swap : star (θ i x) * θ i c = star (θ i c) * θ i x := by
      rw [← (h_adj i).star_eq, star_mul, star_star]
    rw [map_mul, map_mul, hβ_star, hβ_star, ← mul_assoc, h_swap, mul_assoc, h_inv, mul_one]
  calc
    a * (aeval (γ : Matrix n n R) c)ᴴ =
        a * (aeval (γ : Matrix n n R) x)ᴴ * aeval (γ : Matrix n n R) (c * x') := by
      rw [hβ_adjoint, hβ_adjoint, β_eq, map_mul, mul_assoc]
    _ = aeval (γ : Matrix n n R) (c * (x * x')) := by rw [ha, ← map_mul, mul_left_comm]
    _ = aeval (γ : Matrix n n R) c := by
      rw [map_mul, map_mul, h_inv_γ, mul_one]

/-- The complex roots of a factor `q` of the characteristic polynomial `P` of a unitary matrix over
a CM field have absolute value `1`. -/
lemma New.U.mul_star_eq_one_of_mem_roots_of_dvd {K n : Type} [Field K] [NumberField K]
    [IsCMField K] [Fintype n] [DecidableEq n] (γ : U (1 : Matrix n n K)) (φ : K →+* ℂ)
    {P q : K[X]} (hP : (γ : Matrix n n K).charpoly = P) (hq : q ∣ P) {x : ℂ}
    (hx : x ∈ (q.map φ).roots) :
    x * star x = 1 := by
  have h_root : ((γ : Matrix n n K).charpoly.map φ).IsRoot x := by
    rw [hP]
    exact (isRoot_of_mem_roots hx).dvd (map_dvd φ hq)
  exact U.mul_star_eq_one_of_isRoot_charpoly γ φ h_root

open scoped Classical in
/-- An automorphism `σ` of `E'` over `E` that fixes the nonzero polynomial `P` maps each prime
factor of `P` to a prime factor of `P`. -/
lemma New.smul_mem_primeFactors_of_smul_eq {E E' : Type} [Field E] [Field E'] [Algebra E E']
    {σ : Gal(E'/E)} {P q : E'[X]} (hP_ne : P ≠ 0) (hP_fix : σ • P = P) (hq : q ∈ primeFactors P) :
    σ • q ∈ primeFactors P := by
  have mem_fac {f : E'[X]} : f ∈ primeFactors P ↔ Irreducible f ∧ f.Monic ∧ f ∣ P :=
    mem_primeFactors.trans (Polynomial.mem_normalizedFactors_iff hP_ne)
  obtain ⟨h_irred, h_monic, h_dvd⟩ := mem_fac.mp hq
  refine mem_fac.mpr ⟨h_irred.map (toMulEquiv _ σ), ?_, ?_⟩
  · simpa [smul_eq_map] using h_monic
  · exact (_root_.map_dvd (toMulEquiv _ σ) h_dvd).trans hP_fix.dvd

/-- Let `z` be a norm root for `P` over `R` with `u = 1` (`New.IsNormRoot`), let `γ` be a unitary
matrix with characteristic polynomial `P`, and let `v' * P + v * X = 1`. Then `P` divides a power
of `X * N̄(v) - N`, where `N` is the twisted norm of `z` under `σ` and `N̄` has conjugated
coefficients. -/
lemma New.IsNormRoot.dvd_pow_of_charpoly_eq {R n : Type} [CommRing R] [StarRing R] [Fintype n]
    [DecidableEq n] {σ : R →+* R} {p : ℕ} {D : Subgroup Rˣ} {P z : R[X]}
    (hz : IsNormRoot n σ p 1 D P z) {γ : U (1 : Matrix n n R)}
    (hγ : (γ : Matrix n n R).charpoly = P)
    {v v' : R[X]} (hv : v' * P + v * X = 1) :
    P ∣ (X * ((twistedNorm (.map σ) p z).map conj).comp v - twistedNorm (.map σ) p z) ^
      Fintype.card n := by
  obtain ⟨-, hz_roots⟩ := hz
  obtain ⟨-, h_quot⟩ := hz_roots γ hγ
  have cayley : aeval (γ : Matrix n n R) P = 0 := by rw [← hγ, aeval_self_charpoly]
  have v_inv : aeval (γ : Matrix n n R) v * (γ : Matrix n n R) = 1 := by
    have h_bezout : aeval (γ : Matrix n n R) (v' * P + v * X) = 1 := by rw [hv, map_one]
    simpa [cayley] using h_bezout
  have h_quot_γ : IsRootQuotient γ (twistedNorm (.map σ) p z) (γ : Matrix n n R) := by
    simpa using h_quot
  rw [← hγ]
  exact IsRootQuotient.charpoly_dvd_pow v_inv h_quot_γ

/-- Let `A` be a finite free algebra over `R` and `D` a subgroup of `Rˣ`. If `det z(M)` lies in `D`
for every square matrix `M` over `R` with `P(M) = 0`, then the norm of `z(a)` from `A` to `R` lies
in `D` for every `a` in `A` with `P(a) = 0`. -/
theorem exists_mem_coe_eq_norm_aeval_of_forall_det_aeval_mem {R A : Type*} [CommRing R]
    [Nontrivial R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A] {P z : R[X]}
    {D : Subgroup Rˣ}
    (hz : ∀ (m : ℕ) (M : Matrix (Fin m) (Fin m) R), aeval M P = 0 →
      (aeval M z).det ∈ D.toSubmonoid.map (Units.coeHom R))
    {a : A} (ha : aeval a P = 0) : ∃ d ∈ D, (d : R) = Algebra.norm R (aeval a z) := by
  -- apply the hypothesis to the matrix of multiplication by `a` in a basis of `A`
  let b : Module.Basis (Fin (Module.finrank R A)) R A := Module.finBasis R A
  have h_P : aeval (leftMulMatrix b a) P = 0 := by rw [aeval_algHom_apply, ha, map_zero]
  obtain ⟨d, hd, hd_det⟩ := hz _ (leftMulMatrix b a) h_P
  refine ⟨d, hd, ?_⟩
  rw [Algebra.norm_eq_matrix_det b, ← aeval_algHom_apply]
  exact hd_det

/-- The finite idele of `y` in `Lˣ` is the image of `y` in the finite adeles. -/
private lemma New.coe_principalIdele {L : Type*} [Field L] [NumberField L] (y : Lˣ) :
    ((principalIdele y : (𝔸f L)ˣ) : 𝔸f L) = algebraMap L (𝔸f L) y :=
  rfl

/-- The Hasse principle at one prime factor `q`, for the step `E'/E` with character `μ` and `σ` of
prime order `p`. Here `θ` presents the adeles of the CM field `L = E'[X] / (q)` as adelic
polynomials modulo `q`, and `T c = z * σ c`. Here `θ (f̄(v)) = star (θ f)`, `θ z` is a unit with
norm in `kerCompNorm E' μ`, and `q` divides `(X * N̄(v) - N) ^ m` for the twisted norm `N` of `z`.
For `l = p`, or `l = 1` when `σ` fixes `q`, some `y` in `Lˣ` and `c` with `θ c` a unit make
`star (θ c) * (y * θ (T^[l] c))` self-adjoint. -/
private lemma New.IsStep.exists_isSelfAdjoint_principalIdele_of_dvd_pow {E E' : Type} [Field E]
    [CMType E] [Field E'] [NumberField E'] [IsCMField E'] [Algebra E E'] {p : ℕ}
    {μ : (𝔸f E)ˣ →* ℂˣ} [hμ : IsStep (E := E) E' μ]
    {σ : Gal(E'/E)} (hp : p.Prime) (hσ_pow : σ ^ p = 1) (hσ : σ ≠ 1) {q v : E'[X]}
    [Fact (Irreducible q)] [IsCMField (AdjoinRoot q)]
    {θ : (𝔸f E')[X] →ₐ[𝔸f E'] 𝔸f (AdjoinRoot q)} (hθ : θ = aeval (root q : 𝔸f (AdjoinRoot q)))
    (hθ_surj : Surjective θ)
    (hθ_dvd : ∀ f : (𝔸f E')[X], q.map (algebraMap E' (𝔸f E')) ∣ f → θ f = 0)
    (hθ_star : ∀ f : (𝔸f E')[X],
      θ ((f.map conj).comp (v.map (algebraMap E' (𝔸f E')))) = star (θ f))
    {z : (𝔸f E')[X]} (hz_unit : IsUnit (θ z))
    (hz_norm : ∃ d ∈ kerCompNorm E' μ, d.val = Algebra.norm (𝔸f E') (θ z))
    {T : (𝔸f E')[X] → (𝔸f E')[X]}
    (hT : T = fun c : (𝔸f E')[X] ↦ z * mapRingHom (adeleMap σ.toRingHom) c) {m : ℕ}
    (h_dvd : q.map (algebraMap E' (𝔸f E')) ∣
      (X * ((twistedNorm (.map (adeleMap σ)) p z).map conj).comp
        (v.map (algebraMap E' (𝔸f E'))) - twistedNorm (.map (adeleMap σ)) p z) ^ m)
    {l : ℕ} (hl : σ • q = q ∧ l = 1 ∨ l = p) :
    ∃ (y : (AdjoinRoot q)ˣ) (c : (𝔸f E')[X]), IsUnit (θ c) ∧
      IsSelfAdjoint (star (θ c) * ((principalIdele y).val * θ (T^[l] c))) := by
  -- the twisted norm `N` of `z` is `T^[p] 1`
  have norm_eq : T^[p] 1 = twistedNorm (.map (adeleMap σ)) p z := by
    rw [hT, iterate_mul_apply, map_one, mul_one, twistedNorm_map_eq_prod]
    exact Finset.prod_congr rfl fun i _ ↦ Polynomial.mapRingHom_pow_apply _ i z
  -- the adeles of `L` have no nilpotents, so `N = root * star N` holds in them
  have h_reduced : IsReduced (𝔸f (AdjoinRoot q)) :=
    isReduced_of_injective (RingHom.pi (evalAt (E := AdjoinRoot q))) DFunLike.coe_injective
  have θ_X : θ X = root q := by rw [hθ, aeval_X]
  set D : (𝔸f E')[X] :=
    X * ((T^[p] 1).map conj).comp (v.map (algebraMap E' (𝔸f E'))) - T^[p] 1 with hD
  have h_pow : θ D ^ m = 0 := by
    rw [← map_pow, hD, norm_eq]
    exact hθ_dvd _ h_dvd
  have h_zero : θ D = 0 := IsNilpotent.eq_zero ⟨m, h_pow⟩
  have h_norm : root q * star (θ (T^[p] 1)) = θ (T^[p] 1) := by
    rwa [hD, map_sub, map_mul, θ_X, hθ_star, sub_eq_zero] at h_zero
  obtain ⟨h_fix, rfl⟩ | rfl := hl
  · -- `σ` fixes `q`: it extends to an automorphism `g` of `L` of order `p` that fixes the root,
    -- and the Hasse principle for `g` applies to the idele `θ z`
    rw [smul_eq_map E' σ] at h_fix
    let g : AdjoinRoot q ≃ₐ[E] AdjoinRoot q := mapAlgEquiv σ q q (.of_eq h_fix)
    have g_conj : Semiconj (of q) σ g := by simp [g, Semiconj]
    have g_root : g (root q) = root q := by simp [g]
    have g_ord : orderOf g = p := orderOf_eq_of_semiconj hp hσ_pow hσ g_conj g_root
    obtain ⟨d, hd, hd_norm⟩ := hz_norm
    -- the norm of `θ z` from `L` to `E` is that of `d` from `E'` to `E`
    have h_norm_eq : Units.map (adeleNorm E (AdjoinRoot q)) hz_unit.unit =
        Units.map (adeleNorm E E') d := by
      ext
      simp [hd_norm]
    have z_mem : hz_unit.unit ∈ kerCompNorm (AdjoinRoot q) μ := (congrArg μ h_norm_eq).trans hd
    have T_conj : Semiconj θ T fun a ↦ θ z * adeleMap g a := by
      intro f
      simp [hθ, hT, g, aeval_def, hom_eval₂, eval₂_map, algebraMap_eq_finAdeleIncl, RingHom.comp]
    have T_iterate : θ (T^[p] 1) = ∏ i ∈ Finset.range (orderOf g),
        adeleMap (↑(g ^ i) : AdjoinRoot q →+* AdjoinRoot q) (θ z) := by
      rw [g_ord, T_conj.iterate_right p 1, map_one, iterate_mul_apply, map_one, mul_one]
      simp only [adeleMap_gal_pow]
    set N : 𝔸f (AdjoinRoot q) := ∏ i ∈ Finset.range (orderOf g),
      adeleMap (↑(g ^ i) : AdjoinRoot q →+* AdjoinRoot q) (hz_unit.unit : 𝔸f (AdjoinRoot q))
      with hN
    have h_prod : N = (root q : 𝔸f (AdjoinRoot q)) * star N := by
      rw [hN, IsUnit.unit_spec, ← T_iterate]
      exact h_norm.symm
    obtain ⟨y, c, hc, h_adj⟩ :=
      hμ.exists_isSelfAdjoint_of_mem_kerCompNorm g_root adjoinRoot_eq_top _ z_mem h_prod
    obtain ⟨c, rfl⟩ := hθ_surj c
    refine ⟨y, c, hc, ?_⟩
    have h_eq : (principalIdele y).val * θ (T^[1] c) =
        (principalIdele y * hz_unit.unit).val * adeleMap g (θ c) := by
      rw [iterate_one, T_conj c, Units.val_mul, IsUnit.unit_spec, mul_assoc]
    rw [h_eq]
    exact h_adj
  · -- `l = p`, and `θ (T^[p] 1)` is the norm `N`: take `c = 1`, and `y` from `N = root * star N`
    -- alone
    obtain ⟨y, hy⟩ := exists_isSelfAdjoint_principalIdele_mul _ h_norm.symm
    refine ⟨y, 1, by simp, ?_⟩
    rw [map_one, star_one, one_mul]
    exact hy

open scoped Classical in
/-- Transport along the orbits of `σ` (as `τ` on the prime factors `q` of `P`). `θ q` evaluates at
the root of `q` in `𝔸f (E'[X] / (q))`, and `T c = z * σ c` with all `θ q z` units. If at each `q`
some unit `y` and `c` with `θ q c` a unit make `star (θ q c) * (y * θ q (T^[period of q] c))`
self-adjoint, then some `y q`, `c₀ q` make `y q * θ q (T c)` a unit and `star (θ q c)` times it
self-adjoint at all `q`, for every `c` with `θ q c = θ q (c₀ q)` for all `q`. -/
private lemma New.exists_isSelfAdjoint_principalIdele_of_forall_minimalPeriod {E E' : Type}
    [Field E] [Field E'] [NumberField E'] [Algebra E E'] {P : E'[X]}
    [∀ q : primeFactors P, Fact (Irreducible q.val)]
    [∀ q : primeFactors P, IsCMField (AdjoinRoot q.val)]
    (θ : ∀ q : primeFactors P, (𝔸f E')[X] →ₐ[𝔸f E'] 𝔸f (AdjoinRoot q.val))
    (hθ : ∀ q : primeFactors P, θ q = aeval (root q.val : 𝔸f (AdjoinRoot q.val)))
    {σ : Gal(E'/E)} (τ : primeFactors P ≃ primeFactors P)
    (hτ : ∀ q : primeFactors P, σ • q.val = (τ q).val)
    {z : (𝔸f E')[X]} (hz_unit : ∀ q : primeFactors P, IsUnit (θ q z)) {T : (𝔸f E')[X] → (𝔸f E')[X]}
    (hT : T = fun c : (𝔸f E')[X] ↦ z * mapRingHom (adeleMap σ.toRingHom) c)
    (h_hasse : ∀ q : primeFactors P, ∃ (y : (AdjoinRoot q.val)ˣ) (c : (𝔸f E')[X]),
      IsUnit (θ q c) ∧
        IsSelfAdjoint (star (θ q c) * ((principalIdele y).val * θ q (T^[minimalPeriod τ q] c)))) :
    ∃ (y : ∀ q : primeFactors P, (AdjoinRoot q.val)ˣ) (c₀ : primeFactors P → (𝔸f E')[X]),
      ∀ c : (𝔸f E')[X], (∀ q : primeFactors P, θ q c = θ q (c₀ q)) → ∀ q : primeFactors P,
        IsUnit ((principalIdele (y q)).val * θ q (T c)) ∧
          IsSelfAdjoint (star (θ q c) * ((principalIdele (y q)).val * θ q (T c))) := by
  -- `σ` induces `g q : L q ≃ L (τ q)`, which carries `T` to a twisted multiplication by `z`
  have τ_map (q : primeFactors P) : Associated (q.val.map σ) (τ q).val := by
    have h_smul : σ • q.val = (τ q).val := hτ q
    rw [smul_eq_map E' σ] at h_smul
    exact .of_eq h_smul
  let g (q : primeFactors P) : AdjoinRoot q.val ≃ₐ[E] AdjoinRoot (τ q).val :=
    mapAlgEquiv σ q (τ q) (τ_map q)
  have θ_T (q : primeFactors P) (f : (𝔸f E')[X]) :
      θ (τ q) (T f) = θ (τ q) z * adeleMap (g q) (θ q f) := by
    simp [hθ, g, hT, aeval_def, hom_eval₂, eval₂_map, algebraMap_eq_finAdeleIncl, RingHom.comp]
  exact exists_isSelfAdjoint_along_orbits τ (fun q f ↦ θ q f) (fun _ ↦ principalIdele)
    (fun q ↦ adeleMap (g q)) hz_unit θ_T h_hasse

open scoped Classical in
/-- From solutions on the orbits to one global solution: transport along the orbits of `σ`, which
permutes the prime factors `q` of `P` as `τ`, then glue by the Chinese remainder theorem. Here
`v * X ≡ 1` mod `P`, and `θ q` presents the adeles of `E'[X] / (q)` as adelic polynomials modulo
`q`. Also `z` is a unit mod each `q` and `T c = z * σ c`. For each `q`, some unit `y` of `E'[X]/(q)`
and some `c` that is a unit mod `q` make `star c · y · T^[k] c` self-adjoint mod `q`, where `k` is
the length of the `τ`-orbit of `q`. Then some `w` over `E'` and adelic `c` make `x = w * T c`
satisfy, at each adelic unitary `γ` killed by the radical of `P`: `x(γ)` is a unit, and
`a * x(γ)ᴴ = x(γ)` implies `a * c(γ)ᴴ = c(γ)`. -/
private lemma New.exists_isUnit_aeval_and_isRootQuotient_of_isSelfAdjoint {E E' n : Type} [Field E]
    [Field E'] [NumberField E'] [IsCMField E'] [Algebra E E'] [Fintype n] [DecidableEq n]
    {P v v' : E'[X]} (hv : v' * P + v * X = 1) [∀ q : primeFactors P, Fact (Irreducible q.val)]
    [∀ q : primeFactors P, IsCMField (AdjoinRoot q.val)]
    (θ : ∀ q : primeFactors P, (𝔸f E')[X] →ₐ[𝔸f E'] 𝔸f (AdjoinRoot q.val))
    (hθ : ∀ q : primeFactors P, θ q = aeval (root q.val : 𝔸f (AdjoinRoot q.val)))
    (hθ_surj : ∀ q : primeFactors P, Surjective (θ q))
    (hθ_ker : ∀ (q : primeFactors P) (f : (𝔸f E')[X]),
      θ q f = 0 ↔ q.val.map (algebraMap E' (𝔸f E')) ∣ f)
    (hθ_rat : ∀ (q : primeFactors P) (f : E'[X]),
      θ q (f.map (algebraMap E' (𝔸f E'))) = AdjoinRoot.mk q.val f)
    (hθ_star : ∀ (q : primeFactors P) (f : (𝔸f E')[X]),
      θ q ((f.map conj).comp (v.map (algebraMap E' (𝔸f E')))) = star (θ q f))
    {σ : Gal(E'/E)} (τ : primeFactors P ≃ primeFactors P)
    (hτ : ∀ q : primeFactors P, σ • q.val = (τ q).val)
    {z : (𝔸f E')[X]} (hz_unit : ∀ q : primeFactors P, IsUnit (θ q z)) (T : (𝔸f E')[X] → (𝔸f E')[X])
    (hT : T = fun c : (𝔸f E')[X] ↦ z * mapRingHom (adeleMap σ.toRingHom) c)
    (h_hasse : ∀ q : primeFactors P, ∃ (y : (AdjoinRoot q.val)ˣ) (c : (𝔸f E')[X]),
      IsUnit (θ q c) ∧
        IsSelfAdjoint (star (θ q c) * ((principalIdele y).val * θ q (T^[minimalPeriod τ q] c)))) :
    ∃ (w : E'[X]) (c : (𝔸f E')[X]), ∀ γ : Gf E' n,
      aeval γ.val.val ((radical P).map (algebraMap E' (𝔸f E'))) = 0 →
      IsUnit (aeval γ.val.val (w.map (algebraMap E' (𝔸f E')) * T c)) ∧
        ∀ a : Matrix n n (𝔸f E'), IsRootQuotient γ (w.map (algebraMap E' (𝔸f E')) * T c) a →
          IsRootQuotient γ c a := by
  -- transport along the orbits of `τ`
  obtain ⟨y, c₀, h_local⟩ :=
    exists_isSelfAdjoint_principalIdele_of_forall_minimalPeriod θ hθ τ hτ hz_unit hT h_hasse
  -- choose `c` and `w` by the Chinese remainder theorem, and an inverse `x'` of `x` modulo each `q`
  obtain ⟨c, hc⟩ : ∃ c : (𝔸f E')[X], ∀ q : primeFactors P,
      q.val.map (algebraMap E' (𝔸f E')) ∣ c - c₀ q :=
    exists_forall_map_dvd_sub (algebraMap E' (𝔸f E')) P c₀
  obtain ⟨w, hw⟩ : ∃ w : E'[X], ∀ q : primeFactors P,
      q.val.map (RingHom.id E') ∣ w - (y q).val.out :=
    exists_forall_map_dvd_sub (RingHom.id E') P fun q ↦ (y q).val.out
  refine ⟨w, c, fun γ hγ ↦ ?_⟩
  set x : (𝔸f E')[X] := w.map (algebraMap E' (𝔸f E')) * T c with hx
  obtain ⟨x', hx'⟩ : ∃ x' : (𝔸f E')[X], ∀ q : primeFactors P,
      q.val.map (algebraMap E' (𝔸f E')) ∣ x' - surjInv (hθ_surj q) (θ q x)⁻¹ʳ :=
    exists_forall_map_dvd_sub (algebraMap E' (𝔸f E')) P fun q ↦ surjInv (hθ_surj q) (θ q x)⁻¹ʳ
  -- read the congruences modulo `q` as equalities in `AdjoinRoot q.val` and its adeles
  have hc_eq (q : primeFactors P) : θ q c = θ q (c₀ q) := by
    simpa only [← hθ_ker, map_sub, sub_eq_zero] using hc q
  have hw_eq (q : primeFactors P) : AdjoinRoot.mk q.val w = (y q).val := by
    have h_mk : AdjoinRoot.mk q.val w = AdjoinRoot.mk q.val (y q).val.out := by
      simpa only [Polynomial.map_id, ← mk_eq_mk] using hw q
    exact h_mk.trans (Quot.out_eq _)
  have hx'_eq (q : primeFactors P) : θ q x' = (θ q x)⁻¹ʳ := by
    simpa only [← hθ_ker, map_sub, sub_eq_zero, surjInv_eq] using hx' q
  have local_prop (q : primeFactors P) :
      IsUnit (θ q x) ∧ IsSelfAdjoint (star (θ q c) * θ q x) := by
    have θ_x : θ q x = (principalIdele (y q)).val * θ q (T c) := by
      rw [hx, map_mul, hθ_rat, hw_eq, coe_principalIdele]
    rw [θ_x]
    exact h_local c hc_eq q
  choose x_unit x_adj using local_prop
  -- an identity under all `θ q` holds modulo the radical of `P`, hence at `γ`
  have glue {f f' : (𝔸f E')[X]} (h_eq : ∀ q : primeFactors P, θ q f = θ q f') :
      aeval γ.val.val f = aeval γ.val.val f' := by
    refine aeval_eq_of_forall_map_dvd_sub _ hγ fun q hq ↦ (hθ_ker ⟨q, hq⟩ _).mp ?_
    rw [map_sub, h_eq, sub_self]
  -- `P` is a multiple of its radical, so `γ` is a root of `P`
  have hγP : aeval γ.val.val (P.map (algebraMap E' (𝔸f E'))) = 0 :=
    aeval_eq_zero_of_dvd_aeval_eq_zero (Polynomial.map_dvd _ (radical_dvd_self (a := P))) hγ
  -- `v` inverts `X` modulo `P`, so `f ↦ f̄(v)` represents the adjoint at `γ`
  have v_inv : aeval γ.val.val (v.map (algebraMap E' (𝔸f E'))) * γ.val.val = 1 := by
    have h_bezout : aeval γ.val.val ((v' * P + v * X).map (algebraMap E' (𝔸f E'))) = 1 := by
      rw [hv, Polynomial.map_one, map_one]
    simpa [hγP] using h_bezout
  have h_inv (q : primeFactors P) : θ q x * θ q x' = 1 := by
    rw [hx'_eq, mul_inverse_cancel _ (x_unit q)]
  exact isUnit_and_isRootQuotient_of_isSelfAdjoint θ glue (U.conjTranspose_aeval v_inv) hθ_star
    h_inv x_adj

open scoped Classical in
/-- Let `E'/E` be a step with character `μ`, `σ ≠ 1` with `σ ^ p = 1`, `p` prime, `P` the `σ`-fixed
characteristic polynomial of a unitary matrix over `E'`, and `z` a norm root for `P` (its twisted
norm `N` has `γ * N(γ)ᴴ = N(γ)` at adelic unitary `γ` with charpoly `P`;
`det z(A) ∈ kerCompNorm E' μ` if `P(A) = 0`). Then some `w` over `E'` and adelic `c` make
`x = w * z * σ c` satisfy, at each `γ` killed by the radical of `P`: `x(γ)` is a unit, and
`a * x(γ)ᴴ = x(γ)` gives `a * c(γ)ᴴ = c(γ)`. -/
lemma New.exists_global_root {E E' n : Type} [Field E] [CMType E] [Field E'] [NumberField E']
    [IsCMField E'] [Algebra E E'] [Fintype n] [DecidableEq n] {p : ℕ} {μ : (𝔸f E)ˣ →* ℂˣ}
    [hμ : IsStep (E := E) E' μ]
    {σ : Gal(E'/E)} (hp : p.Prime) (hσ_pow : σ ^ p = 1) (hσ : σ ≠ 1) {P : E'[X]}
    (hP : ∃ γ' : U (1 : Matrix n n E'), γ'.val.val.charpoly = P) (hP_fix : σ • P = P)
    {z : (𝔸f E')[X]}
    (hz : IsNormRoot n (adeleMap σ) p 1 (kerCompNorm E' μ) (P.map (algebraMap E' (𝔸f E'))) z) :
    ∃ (w : E'[X]) (c : (𝔸f E')[X]),
      let x : (𝔸f E')[X] := w.map (algebraMap E' (𝔸f E')) * (z * c.map (adeleMap σ))
      ∀ γ : Gf E' n,
        aeval γ.val.val ((UniqueFactorizationMonoid.radical P).map (algebraMap E' (𝔸f E'))) = 0 →
        IsUnit (aeval γ.val.val x) ∧
          ∀ a : Matrix n n (𝔸f E'), IsRootQuotient γ x a → IsRootQuotient γ c a := by
  -- Work in the CM fields `L q = E'[X] / (q)` for the prime factors `q` of `P`, permuted by `σ`.
  -- At each `q` the Hasse principle gives a rational `y` and an adelic `c` making
  -- `y * T^[period] c / c` invariant under conjugation; transport these along the orbits of `σ`,
  -- and glue by the Chinese remainder theorem.
  obtain ⟨γ', hγ'⟩ := hP
  have hp_fact : Fact p.Prime := ⟨hp⟩
  let k : E' →+* 𝔸f E' := algebraMap E' (𝔸f E')
  let T (c : (𝔸f E')[X]) : (𝔸f E')[X] := z * mapRingHom (adeleMap σ.toRingHom) c
  -- `γ₀`, the image of `γ'`, is an adelic unitary element with characteristic polynomial `P`
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : Gf E' n, γ₀.val.val.charpoly = P.map k :=
    ⟨U.map k (fun x : E' ↦ (star_algebraMap_finAdele x).symm) (one_map_ringHom k) γ',
      (charpoly_map γ'.val.val k).trans (congrArg (Polynomial.map k) hγ')⟩
  -- `γ'` is invertible, so `v' * P + v * X = 1` for some `v'` and `v`
  obtain ⟨v', v, hv⟩ : IsCoprime P X := by
    rw [← hγ']
    exact isUnit_aeval_iff_isCoprime.mp (by simp)
  have P_ne : P ≠ 0 := by
    rw [← hγ']
    exact (charpoly_monic _).ne_zero
  have fac (q : primeFactors P) : Fact (Irreducible q.val) ∧ q.val.Monic ∧ q.val ∣ P := by
    have h_mem : q.val ∈ normalizedFactors P := mem_primeFactors.mp q.property
    exact ((Polynomial.mem_normalizedFactors_iff P_ne).mp h_mem).imp_left Fact.mk
  choose irred monic dvd_P using fac
  -- `σ` permutes the prime factors of `P`
  let τ : primeFactors P ≃ primeFactors P :=
    (toPerm σ).subtypePermOfFintype fun q hq ↦ smul_mem_primeFactors_of_smul_eq P_ne hP_fix hq
  -- the twisted norm `N` of `z` has `N = X * N̄(v)` at `γ₀`; `P` divides a power of the difference
  have hv_map : v'.map k * P.map k + v.map k * X = 1 := by
    simpa using congrArg (Polynomial.map k) hv
  have norm_dvd : P.map k ∣ (X * ((twistedNorm (.map (adeleMap σ)) p z).map conj).comp (v.map k) -
      twistedNorm (.map (adeleMap σ)) p z) ^ Fintype.card n :=
    IsNormRoot.dvd_pow_of_charpoly_eq hz hγ₀ hv_map
  -- the roots of `P` have absolute value `1`, so each `L q` is a CM field
  have unit_root (q : primeFactors P) (φ : E' →+* ℂ) (x : ℂ) (hx : x ∈ (q.val.map φ).roots) :
      x * star x = ((1 : ℚ) : ℂ) := by
    exact_mod_cast U.mul_star_eq_one_of_mem_roots_of_dvd γ' φ hγ' (dvd_P q) hx
  -- `θ q` is evaluation at the root of `q`, an adele of `L q`; it presents the adeles of `L q` as
  -- the adelic polynomials modulo `q`
  let θ (q : primeFactors P) : (𝔸f E')[X] →ₐ[𝔸f E'] 𝔸f (AdjoinRoot q.val) :=
    aeval (root q.val : 𝔸f (AdjoinRoot q.val))
  have h_presentation (q : primeFactors P) : ∃ _ : IsCMField (AdjoinRoot q.val),
      root q.val * star (root q.val) = ((1 : ℚ) : AdjoinRoot q.val) ∧
      IsFinAdelePresentation q.val (θ q) :=
    adjoinRoot_cm_presentation (monic q) (unit_root q)
  choose isCM root_star θ_presents using h_presentation
  have surj (q : primeFactors P) : Surjective (θ q) := (θ_presents q).surjective
  have ker (q : primeFactors P) (f : (𝔸f E')[X]) : θ q f = 0 ↔ q.val.map k ∣ f :=
    (θ_presents q).eq_zero_iff f
  have θ_rat (q : primeFactors P) (f : E'[X]) : θ q (f.map k) = mk q.val f :=
    (θ_presents q).apply_map f
  have θ_comp_v_eq_star (q : primeFactors P) (f : (𝔸f E')[X]) :
      θ q ((f.map conj).comp (v.map k)) = star (θ q f) := by
    have h_bezout : mk q.val (v' * P + v * X) = 1 := by rw [hv, map_one]
    have h_inv : mk q.val v * root q.val = 1 := by
      rw [map_add, map_mul, map_mul, mk_eq_zero.mpr (dvd_P q), mul_zero, zero_add, mk_X] at h_bezout
      exact h_bezout
    have h_star : root q.val * star (root q.val) = 1 := by
      simpa only [Rat.cast_one] using root_star q
    exact (θ_presents q).apply_map_conj_comp (left_inv_eq_right_inv h_inv h_star) f
  -- `θ q z` is an idele of `L q` whose norm to the ideles of `E'` lies in `kerCompNorm E' μ`
  have z_norm (q : primeFactors P) :
      ∃ d ∈ kerCompNorm E' μ, d.val = Algebra.norm (𝔸f E') (θ q z) := by
    obtain ⟨-, hz_roots⟩ := hz
    obtain ⟨h_det, -⟩ := hz_roots γ₀ hγ₀
    exact exists_mem_coe_eq_norm_aeval_of_forall_det_aeval_mem h_det
      ((ker q _).mpr (map_dvd k (dvd_P q)))
  have z_unit (q : primeFactors P) : IsUnit (θ q z) := by
    obtain ⟨d, -, hd_norm⟩ := z_norm q
    exact lmul_isUnit_iff.mp ((LinearMap.isUnit_iff_isUnit_det _).mpr ⟨d, hd_norm⟩)
  -- the Hasse principle at `q`, for `T` iterated once round the orbit of `q`
  have hasse (q : primeFactors P) : ∃ (y : (AdjoinRoot q.val)ˣ) (c : (𝔸f E')[X]), IsUnit (θ q c) ∧
      IsSelfAdjoint (star (θ q c) * ((principalIdele y).val * θ q (T^[minimalPeriod τ q] c))) := by
    have τ_pow : (τ ^ p) q = q := by simp [τ, ← toPermHom_apply, ← map_pow, hσ_pow]
    have h_period : σ • q.val = q.val ∧ minimalPeriod τ q = 1 ∨ minimalPeriod τ q = p := by
      obtain h_fix | h_move := eq_or_ne (τ q) q
      · exact .inl ⟨congrArg Subtype.val h_fix, minimalPeriod_eq_one_iff_isFixedPt.mpr h_fix⟩
      · exact .inr (minimalPeriod_eq_prime τ_pow h_move)
    exact IsStep.exists_isSelfAdjoint_principalIdele_of_dvd_pow hp hσ_pow hσ rfl (surj q)
      (fun f hf ↦ (ker q f).mpr hf) (θ_comp_v_eq_star q) (z_unit q) (z_norm q) rfl
      ((map_dvd k (dvd_P q)).trans norm_dvd) h_period
  -- transport along the orbits of `τ`, and glue by the Chinese remainder theorem
  exact exists_isUnit_aeval_and_isRootQuotient_of_isSelfAdjoint (n := n) hv θ (fun _ ↦ rfl) surj
    ker θ_rat θ_comp_v_eq_star τ (fun _ ↦ rfl) z_unit T rfl hasse

end GlobalRoot
end
end

/-!
# Twisted trace identity for a step E'/E of CM fields of prime degree

The main result is `New.twisted_trace_identity`. For a step `E'/E` (`New.IsStep`) of prime degree,
it compares a `σ`-twisted trace on forms over `E'` with a trace on forms over `E`, on the definite
unitary groups of `New.stdSpace`, for matching pairs of test functions. Both sides are expanded by
`New.Space.isSampleTotal_twisted_trace` as weighted sums over samples of pairs
(`New.IsSampleTotal`).

## Main definitions and results

* `New.IsSampleTotal`: a number `a` is a weighted sum of `F` over finitely many points, and the
  weighted number of moves from these points to each relevant point is `c`.
* `New.IsSampleTotal.mul_eq_mul_of_bijOn`: two such sums `a`, `b` with weights `c`, `d` satisfy
  `b * c = d * a` when a map between the point sets matches values and moves.
* `New.Weight.baseChange`: the weight of `E'` that has at each infinite place the data of `κ` at the
  place below.
* `New.exists_trace_mul_weightRep_eq_of_twistedNorm_eq`: the twisted character of `κ.baseChange` at
  `δ` is the character of `κ` at the norm of `δ`.

Notions from other files:
* `New.Space.forms V κ`: the forms of weight `κ` on a space `V`, smooth functions `ψ` on the finite
  adelic unitary group `Gf E n` (`U (1 : Matrix n n (𝔸f E))`; `U V.J` is the rational one) with
  `ψ (V.embFin γ * g) = ρ γ (ψ g)` for rational `γ`, where `ρ` is `V.weightRep κ.fst κ.snd` and
  `V.embFin` embeds the rational unitary group; `V.formTranslation κ` is right translation on them.
* `levelSpace π L`: the vectors fixed by `π k` for every `k ∈ L`.
* `New.IsOperatorOf π L T φ`: `T` is the Hecke operator of `φ` on the `L`-fixed vectors.
* `New.stdSpace`: the definite space `I_n`, the sum of `n` norms with its standard lattice.
* `New.twistedNorm τ p δ`: the product `δ * τ δ * ⋯ * τ^[p - 1] δ`.

## Relation to the literature

Known; see `Lib.GaloisRep.BaseChange.PrimeDegreeTransfer` for sources.
-/

@[expose] public section

/-! ## Double counting of moves between weighted samples of pairs -/

section MoveCounting

open Set Finsupp

/-- There are finitely many points `p i` with complex weights `w i` such that
`a = ∑ w i * F (p i)`, and `∑ w i * #(M (p i) y) = c` for every point `y` such that `F x ≠ 0`
whenever there is a move in `M x y`. Here `M x y` is thought of as the set of moves from `x` to
`y`, and `Set.ncard` is `0` on infinite sets. -/
def New.IsSampleTotal {P A : Type*} (M : P → P → Set A) (F : P → ℂ) (c a : ℂ) : Prop :=
  ∃ w : P →₀ ℂ,
    a = lift ℂ ℂ P F w ∧
    ∀ y : P, (∀ x : P, ∀ g ∈ M x y, F x ≠ 0) → lift ℂ ℂ P (fun x ↦ (M x y).ncard) w = c

/-- Double counting of moves. `IsSampleTotal M F c a` says that, for finitely many points `p i` with
complex weights `w i`, `a = ∑ w i * F (p i)` and `∑ w i * #(M (p i) y) = c` for every `y` such that
`F x ≠ 0` whenever `M x y` (the set of moves from `x` to `y`, with `#` equal to `0` if infinite) is
nonempty. Let `a`, `b` be such totals of `F`, `F'` with weights `c`, `d` for the moves `M`, `N`, and
suppose: `F` vanishes off `S`; `F' y = F x` when `x ∈ S` and `y` has a move to `m x`; and for each
`y` with `F' y ≠ 0`, some `z` and `J` map, for every `x`, the moves from `x` to `z` bijectively onto
the moves from `y` to `m x` (onto `∅` if `x ∉ S`). Then `b * c = d * a`. -/
lemma New.IsSampleTotal.mul_eq_mul_of_bijOn {P Q A B : Type*} {c d a b : ℂ} {M : P → P → Set A}
    {N : Q → Q → Set B} {F : P → ℂ} (F' : Q → ℂ) (h_tot : IsSampleTotal M F c a)
    (h_tot' : IsSampleTotal N F' d b) (m : P → Q) (S : Set P)
    (hF_supp : ∀ x : P, F x ≠ 0 → x ∈ S)
    (hF'_eq : ∀ x ∈ S, ∀ y : Q, ∀ g ∈ N y (m x), F' y = F x)
    (h_bij : ∀ y : Q, F' y ≠ 0 →
      ∃ (z : P) (J : A → B), ∀ x : P, BijOn J (M x z) {g ∈ N y (m x) | x ∈ S}) :
    b * c = d * a := by
  -- Count twice the moves from the points `y` of the second sample to the images `m x` of the
  -- first: summing over `x` first gives `b * c`, summing over `y` first gives `d * a`.
  obtain ⟨w, rfl, hw⟩ := h_tot
  obtain ⟨u, rfl, hu⟩ := h_tot'
  simp only [lift_apply, Finsupp.sum, smul_eq_mul] at hw hu ⊢
  -- If `F' y ≠ 0`, the moves from `y` are counted by the moves to the point `z` of `h_bij`.
  have sum_from (y : Q) :
      F' y * c = F' y * ∑ x ∈ w.support, w x * {g ∈ N y (m x) | x ∈ S}.ncard := by
    by_cases hy : F' y = 0
    · simp [hy]
    obtain ⟨z, J, hJ⟩ := h_bij y hy
    -- a move from `x` to `z` gives one from `y` to `m x` with `x ∈ S`, so `F x = F' y ≠ 0`
    have hF_ne_zero : ∀ x : P, ∀ g ∈ M x z, F x ≠ 0 := fun x g hg ↦ by
      obtain ⟨hg_move, hx_mem⟩ := (hJ x).mapsTo hg
      rwa [← hF'_eq x hx_mem y (J g) hg_move]
    simp only [← hw z hF_ne_zero, (hJ _).ncard_eq]
  -- If `F x ≠ 0`, then `F'` is nonzero at every point with a move to `m x`.
  have sum_to (x : P) : d * F x = F x * ∑ y ∈ u.support, u y * (N y (m x)).ncard := by
    by_cases hx : F x = 0
    · simp [hx]
    rw [← hu (m x) fun y g hg ↦ by rwa [hF'_eq x (hF_supp x hx) y g hg], mul_comm]
  -- The terms agree: a move from `y` to `m x`, `x ∈ S`, gives `F' y = F x`, and `F x = 0` off `S`.
  have term_eq (x : P) (y : Q) :
      F' y * {g ∈ N y (m x) | x ∈ S}.ncard = F x * (N y (m x)).ncard := by
    by_cases hx : x ∈ S
    · obtain h_empty | ⟨g, hg⟩ := (N y (m x)).eq_empty_or_nonempty
      · simp [h_empty]
      · simp [hx, hF'_eq x hx y g hg]
    · simp [hx, not_imp_comm.mp (hF_supp x) hx]
  calc
    _ = ∑ y ∈ u.support, u y * (F' y * c) := by simp only [Finset.sum_mul, mul_assoc]
    _ = ∑ y ∈ u.support, ∑ x ∈ w.support,
          w x * u y * (F' y * {g ∈ N y (m x) | x ∈ S}.ncard) := by
      simp only [sum_from, Finset.mul_sum, mul_assoc, mul_left_comm]
    _ = ∑ x ∈ w.support, ∑ y ∈ u.support, w x * u y * (F x * (N y (m x)).ncard) := by
      simp only [term_eq]
      exact Finset.sum_comm
    _ = ∑ x ∈ w.support, w x * (d * F x) := by
      simp only [sum_to, Finset.mul_sum, mul_assoc, mul_left_comm]
    _ = _ := by simp only [Finset.mul_sum, mul_left_comm]

end MoveCounting

/-!
## The twisted trace of a Hecke operator as a sum over a sample

The moves from a pair `(x, γ)` to a pair `(y, δ)` are the rational `g` with `y⁻¹ * j g * x ∈ K`
and `g⁻¹ * δ * τ g = γ`, where `j` is `V.embFin`.
-/

section TwistedTraceSum

open Subgroup LinearMap New.Variety DoubleCoset New.HasFiniteType Finset

variable {E n : Type} [Field E] [New.CMType E] [Fintype n] [DecidableEq n]
  (V : New.Space E n 1) (κ : New.Weight E)

/-- The twist `ψ ↦ s ∘ ψ ∘ σ⁻¹` maps forms of weight `κ` on `V` to forms. Here `σ` is an
automorphism of the finite adelic group with continuous inverse, `τ` an automorphism of the
rational unitary group with `V.embFin (τ γ) = σ (V.embFin γ)`, and `s` a linear map of the
coefficient space with `s * ρ γ = ρ (τ γ) * s` for `ρ = V.weightRep κ.fst κ.snd`. -/
private lemma New.Space.compLeft_comp_funLeft_mem_forms (σ : Gf E n ≃* Gf E n)
    (hσ_cont : Continuous σ.symm) (τ : U V.J ≃* U V.J)
    (hτ : ∀ γ : U V.J, V.embFin (τ γ) = σ (V.embFin γ))
    (s : (WeylIndex n κ.fst → ℂ) →ₗ[ℂ] WeylIndex n κ.fst → ℂ)
    (hs : ∀ γ : U V.J, s * V.weightRep κ.fst κ.snd γ = V.weightRep κ.fst κ.snd (τ γ) * s)
    {ψ : Gf E n → WeylIndex n κ.fst → ℂ} (hψ : ψ ∈ V.forms κ) :
    (s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm) ψ ∈ V.forms κ := by
  obtain ⟨hψ_smooth, hψ_equivariant⟩ := hψ
  refine ⟨?_, ?_⟩
  · -- the twist is fixed by the preimage under `σ⁻¹` of the right stabiliser of `ψ`, which is open
    have h_stab : (rightStabilizer ψ).comap σ.symm.toMonoidHom ≤
        rightStabilizer ((s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm) ψ) := by
      intro k (hk : ∀ g : Gf E n, ψ (g * σ.symm k) = ψ g)
      simp [hk]
    exact Subgroup.isOpen_mono h_stab (hσ_cont.isOpen_preimage _ hψ_smooth)
  · -- equivariance under `τ γ` follows from that of `ψ` under `γ`, by `hτ` and `hs`
    refine τ.toEquiv.forall_congr_right.mp fun γ g ↦ ?_
    simp_all [DFunLike.ext_iff]

/-- The twist `ψ ↦ s ∘ ψ ∘ σ⁻¹` of forms of weight `κ` (a map of `V.forms κ` by `h_forms`) maps
forms fixed by `L` to forms fixed by `L`, when the automorphism `σ` maps `L` onto itself. -/
private lemma New.Space.restrict_compLeft_comp_funLeft_mem_levelSpace {L : Subgroup (Gf E n)}
    (σ : Gf E n ≃* Gf E n) (hσ : L.comap σ = L)
    (s : (WeylIndex n κ.fst → ℂ) →ₗ[ℂ] WeylIndex n κ.fst → ℂ)
    (h_forms : ∀ x ∈ V.forms κ,
      (s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm) x ∈ V.forms κ)
    {ψ : V.forms κ} (hψ : ψ ∈ levelSpace (V.formTranslation κ) L) :
    ((s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm).restrict h_forms) ψ ∈
      levelSpace (V.formTranslation κ) L := by
  intro k
  -- `ψ` is fixed by `σ⁻¹ k ∈ L`, and the twist turns right translation by `σ⁻¹ k` into that by `k`
  have h_fixed (g : Gf E n) :
      (ψ : Gf E n → WeylIndex n κ.fst → ℂ) (g * σ.symm k) =
        (ψ : Gf E n → WeylIndex n κ.fst → ℂ) g := by
    simpa using congrFun (congrArg Subtype.val (hψ ⟨σ.symm k, hσ.le (by simp)⟩)) g
  ext g i
  simp [LinearMap.restrict, h_fixed]

open Classical in
/-- A weighted count of transporters. Let `L ≤ J` be subgroups of `Gf E n` of finite type for the
rational points `V.Γf`, and let `S g h` be finite sets with `#(S g h) = #(classAut V.Γf J g)` if `g`
and `h` lie in one double coset (`Γ g J = Γ h J`), and `0` otherwise. Then for every `x` the sum
over the double cosets `i` in `Γ \ G / L` of `#(S x i.out) / #(classAut V.Γf L i.out)` is the
index `[J : L]`. -/
private lemma New.Space.sum_inv_card_classAut_mul_card_eq_relIndex {L J : Subgroup (Gf E n)}
    [HasFiniteType V.Γf L] [HasFiniteType V.Γf J] (hJ : L ≤ J)
    (S : Gf E n → Gf E n → Finset (U V.J))
    (h_card : ∀ g h : Gf E n, #(S g h) =
      if DoubleCoset.mk V.Γf J g = DoubleCoset.mk V.Γf J h then Nat.card (classAut V.Γf J g) else 0)
    (x : Gf E n) :
    ∑ i : DoubleCoset.Quotient V.Γf L,
      (((Nat.card (classAut V.Γf L i.out) : ℚ)⁻¹ : ℚ) : ℂ) * #(S x i.out) = L.relIndex J := by
  -- The sum is the class sum of `#(S x ·)` at level `L`, which is `[J : L]` times that at level
  -- `J`; to the latter only the class of `x` contributes, with value `1`.
  have h_sum : classSum V.Γf L (fun y ↦ (#(S x y) : ℂ)) =
      (L.relIndex J : ℚ) • classSum V.Γf J fun y ↦ (#(S x y) : ℂ) :=
    classSum_eq_relIndex_smul hJ 1 (Subgroup.ext (by simp)) fun y ↦ by
      rw [h_card, h_card, out_eq', mul_one]
  -- `-mem_classAut` and `-MonoidHom.coe_range` keep `classAut` folded, and `↓` moves its order to
  -- the representative of the class of `x` before the sum is split
  have h_one : ∑ i : DoubleCoset.Quotient V.Γf J,
      (((Nat.card (classAut V.Γf J i.out) : ℚ)⁻¹ : ℚ) : ℂ) * #(S x i.out) = 1 := by
    simp [h_card, out_eq', ↓card_classAut_out x, -mem_classAut, -MonoidHom.coe_range]
  simp_rw [classSum, finsum_eq_sum_of_fintype, Rat.smul_def] at h_sum
  rw [h_sum, h_one]
  simp

/-- The `L`-fixed forms of weight `κ` on `V`, seen as functions on `Gf E n`, are the functions that
are equivariant for `ρ = V.weightRep κ.fst κ.snd` (`ψ (V.embFin γ * g) = ρ γ (ψ g)`) and right
invariant under the open subgroup `L`. The factor `Submodule.pi ∅ ⊥` (no vanishing condition) is
the form in which `New.trace_eq_weighted_sum` takes this space. -/
private lemma New.Space.range_domRestrict_levelSpace_eq_coindV_inf {L : Subgroup (Gf E n)}
    (hL_open : L.IsOpen) :
    LinearMap.range ((V.forms κ).subtype.domRestrict (levelSpace (V.formTranslation κ) L)) =
      (V.weightRep κ.fst κ.snd).coindV V.embFin ⊓ Submodule.pi (∅ : Set (Gf E n)) ⊥ ⊓
        levelSpace (rightRegular ℂ (Gf E n) (WeylIndex n κ.fst → ℂ)) L := by
  refine le_antisymm ?_ fun F hF ↦ ?_
  · rintro _ ⟨⟨⟨ψ, hψ_smooth, hψ_equivariant⟩, hψ_fixed⟩, rfl⟩
    exact ⟨⟨hψ_equivariant, by simp⟩, fun k ↦ congrArg Subtype.val (hψ_fixed k)⟩
  · obtain ⟨⟨hF_equivariant, _⟩, hF_fixed⟩ := hF
    exact ⟨⟨⟨F, mem_smoothFunctions_of_eigen _ hL_open hF_fixed, hF_equivariant⟩,
        fun k ↦ Subtype.ext (hF_fixed k)⟩, rfl⟩

/-- Twisted trace formula on a definite space `V`. Let `σ` be an automorphism of `Gf E n` with
continuous inverse, `L ≤ K ≤ stdLevel E n` with `L` open and `σ`-stable, `τ` a lift of `σ` to the
rational unitary group along `j = V.embFin`, and `s * ρ γ = ρ (τ γ) * s` for
`ρ = V.weightRep κ.fst κ.snd`. Then `ψ ↦ s ∘ ψ ∘ σ⁻¹` preserves forms and `L`-fixed forms, and for
some `c ≠ 0` the trace of each Hecke operator `T` of `φ` at level `L` composed with it is a sample
sum of weight `c` over pairs. -/
lemma New.Space.isSampleTotal_twisted_trace {K L : Subgroup (Gf E n)} (σ : Gf E n ≃* Gf E n)
    (hσ_cont : Continuous σ.symm) (hK : K ≤ stdLevel E n) (hL : L ≤ K) (hL_open : L.IsOpen)
    (hσ : L.comap σ = L) (τ : U V.J ≃* U V.J) :
    let j := V.embFin
    let ρ := V.weightRep κ.fst κ.snd
    (∀ γ : U V.J, j (τ γ) = σ (j γ)) →
    ∀ s : (WeylIndex n κ.fst → ℂ) →ₗ[ℂ] WeylIndex n κ.fst → ℂ,
      (∀ γ : U V.J, s * ρ γ = ρ (τ γ) * s) →
      ∃ c ≠ (0 : ℂ), ∃ (h : ∀ x ∈ V.forms κ,
        (s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm) x ∈ V.forms κ)
        (h' : ∀ x ∈ levelSpace (V.formTranslation κ) L,
          ((s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm).restrict h)
            x ∈ levelSpace (V.formTranslation κ) L),
        ∀ {φ : Gf E n → ℂ} {T : Module.End ℂ (levelSpace (V.formTranslation κ) L)},
        IsOperatorOf (V.formTranslation κ) L T φ →
        IsSampleTotal
          -- the moves from the pair `p` to the pair `q`
          (fun p q : Gf E n × U V.J ↦
            {g : U V.J | q.fst⁻¹ * j g * p.fst ∈ K ∧ g⁻¹ * q.snd * τ g = p.snd})
          -- the term of a pair
          (fun y : Gf E n × U V.J ↦
            φ (y.fst⁻¹ * j y.snd * σ y.fst) * (ρ y.snd * s).trace ℂ (WeylIndex n κ.fst → ℂ)) c
          -- the trace of `T` composed with `ψ ↦ s ∘ ψ ∘ σ⁻¹`
          ((T *
              ((s.compLeft (Gf E n) ∘ₗ funLeft ℂ (WeylIndex n κ.fst → ℂ) σ.symm).restrict
                h).restrict h').trace ℂ (levelSpace (V.formTranslation κ) L)) := by
  classical
  -- The twist preserves forms and `L`-fixed forms by the two lemmas above. By
  -- `trace_eq_weighted_sum` the trace is a sum over the classes `i` of `Γ \ G / L`, with weights
  -- `1 / #classAut`, and over `γ`. The pairs `(i.out, γ)` with nonzero term form the sample; the
  -- moves from it to a given pair are counted by transporters, whose weighted number is
  -- `c = [K : L]`.
  intro j ρ hτ s hs
  have hK_fin : HasFiniteType V.Γf K := V.hasFiniteType_of_isLevel.of_le hK (isOpen_mono hL hL_open)
  have hL_fin : HasFiniteType V.Γf L := hK_fin.of_le hL hL_open
  refine ⟨L.relIndex K, Nat.cast_ne_zero.2 (hK_fin.isCompact.relIndex_ne_zero hL_open),
    fun ψ hψ ↦ V.compLeft_comp_funLeft_mem_forms κ σ hσ_cont τ hτ s hs hψ,
    fun ψ hψ ↦ V.restrict_compLeft_comp_funLeft_mem_levelSpace κ σ hσ s _ hψ, ?_⟩
  rintro φ T ⟨a, rfl, hT⟩
  -- the transporter `S J g h` is the finite set of rational `γ` with `g⁻¹ * j γ * h ∈ J` (`hS`);
  -- it has `#(classAut V.Γf J g)` elements if `Γ g J = Γ h J` and is empty otherwise (`h_card`)
  have h_transporter (J : Subgroup (Gf E n)) [HasFiniteType V.Γf J] (g h : Gf E n) :
      ∃ S : Finset (U V.J), (∀ γ : U V.J, γ ∈ S ↔ V.embFin γ ∈ V.Γf ∧ g⁻¹ * V.embFin γ * h ∈ J) ∧
        #S = if DoubleCoset.mk V.Γf J g = DoubleCoset.mk V.Γf J h then
          Nat.card (classAut V.Γf J g) else 0 :=
    exists_transporter V.Γf Fact.out .rfl J g h
  choose S hS h_card using h_transporter
  let wt (i : DoubleCoset.Quotient V.Γf L) : ℂ := ((Nat.card (classAut V.Γf L i.out) : ℚ)⁻¹ : ℚ)
  -- `cosetFn L a` lives on finitely many cosets `q`, and each is met by finitely many `γ`
  have h_fin (x : Gf E n) :
      (fun γ : U V.J ↦ cosetFn L a (x⁻¹ * j γ * σ x) *
        (ρ γ * s).trace ℂ (WeylIndex n κ.fst → ℂ)).HasFiniteSupport := by
    refine .mul_left ((cosetFn L a).hasFiniteSupport.preimage' fun q _ ↦
      .ofFinset (S L (x * q.out) (σ x)) fun γ ↦ ?_) _
    rw [hS, mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc x⁻¹, ← QuotientGroup.eq]
    exact ⟨fun ⟨_, h⟩ ↦ h.symm.trans (Quotient.out_eq q),
      fun h ↦ ⟨⟨γ, rfl⟩, (Quotient.out_eq q).trans h.symm⟩⟩
  refine ⟨∑ i, ∑ γ ∈ (h_fin i.out).toFinset, .single (i.out, γ) (wt i), ?_, ?_⟩
  · -- apply `trace_eq_weighted_sum` to the forms of level `L`, seen as functions on the group
    refine (trace_eq_weighted_sum (e := j) (ρ := ρ) (s := s) (D := ∅) (a := a)
      (domRestrict (Submodule.subtype _) _) (Subtype.val_injective.comp Subtype.val_injective)
      (V.range_domRestrict_levelSpace_eq_coindV_inf κ hL_open) (fun i ↦ i.out) wt
      (fun i g ↦ S L g i.out)
      -- the side condition stays inline, since it elaborates only against the expected type that
      -- `trace_eq_weighted_sum` supplies
      (by simp [j, hS, mul_assoc]) (by simp) (fun g _ ↦ ?_) σ hσ fun ψ ↦ ?_).2.trans ?_
    · -- at level `L` the weighted number of transporters is `1`
      simpa only [wt, Rat.cast_inv, Rat.cast_natCast, relIndex_self, Nat.cast_one] using
        V.sum_inv_card_classAut_mul_card_eq_relIndex le_rfl (S L) (h_card L) g
    · -- `T` acts on the `L`-fixed forms through the group ring element `a`
      have h_T_val (v : levelSpace (V.formTranslation κ) L) :
          ((T v : V.forms κ) : Gf E n → WeylIndex n κ.fst → ℂ) =
            ((V.formTranslation κ).asAlgebraHom a v : V.forms κ) :=
        congrArg Subtype.val (hT v)
      -- `using!`: the twist of `ψ` is `g ↦ s (ψ (σ⁻¹ g))` only by unfolding `restrict`
      simpa only [mul_apply_eq_comp, domRestrict_apply, Submodule.subtype_apply,
        asAlgebraHom_eq_sum_support, LinearMap.coe_sum, LinearMap.coe_smul, Finset.sum_apply,
        Pi.smul_apply, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul,
        formTranslation_apply_apply_coe] using! h_T_val _
    · -- reindex by `τ`, using `hτ` and `hs`
      have h_reindex (x : Gf E n) :
          ∑ᶠ γ : U V.J, cosetFn L a (x⁻¹ * j (τ γ) * σ x) *
              (ρ (τ γ) * s).trace ℂ (WeylIndex n κ.fst → ℂ) =
            ∑ γ ∈ (h_fin x).toFinset,
              cosetFn L a (x⁻¹ * j γ * σ x) * (ρ γ * s).trace ℂ (WeylIndex n κ.fst → ℂ) :=
        (finsum_comp _ τ.bijective).trans (finsum_eq_sum _ (h_fin x))
      simp only [← hτ, hs, h_reindex, Function.support_mul, mul_sum, map_sum, Finsupp.lift_apply,
        smul_eq_mul, zero_mul, Finsupp.sum_single_index, j, ρ]
  · -- sort the transporter from `x` to `y` by the second coordinate `g⁻¹ * δ * τ g`
    rintro ⟨y, δ⟩ hy
    have h_fibre (x : Gf E n) : #(S K y x) =
        ∑ γ ∈ (h_fin x).toFinset, #{g ∈ S K y x | g⁻¹ * δ * τ g = γ} := by
      exact card_eq_sum_card_fiberwise fun g hg ↦ (h_fin x).mem_toFinset.2
        (hy (x, g⁻¹ * δ * τ g) g ⟨((hS K y x g).mp hg).right, rfl⟩)
    -- `↓`: `h_fibre` must rewrite the card before `← Set.ncard_coe_finset` turns it into an ncard
    calc _ = ∑ i, wt i * (#(S K y i.out) : ℂ) := by
          simp only [Function.support_mul, map_sum, Finsupp.lift_apply, smul_eq_mul, zero_mul,
            Finsupp.sum_single_index, ↓h_fibre, ← Set.ncard_coe_finset, coe_filter, hS,
            MonoidHom.mem_range, exists_apply_eq_apply, true_and, Nat.cast_sum, mul_sum, j]
      _ = L.relIndex K := V.sum_inv_card_classAut_mul_card_eq_relIndex hL (S K) (h_card K) y

end TwistedTraceSum

/-!
## Base change of weights and twisted characters at the norm

A weight `κ` (`New.Weight`) is a Young diagram `κ.fst` and a power `κ.snd` of the determinant at
each infinite place, and `New.Space.weightRep` is the representation of the rational unitary
group that it defines.
-/

section BaseChangeWeight

open NumberField Matrix ComplexEmbedding ComplexConjugate Finset Module Fin RingHom Equiv Function

variable {E E' n : Type} [Field E] [Field E'] [Algebra E E'] [IsGalois E E'] [Fintype n]
    {σ : Gal(E'/E)}

/-- The base change of a weight: at an infinite place of `E'`, the diagram and the power of the
determinant that `κ` has at the place of `E` below it. -/
noncomputable def New.Weight.baseChange (κ : Weight E) : Weight E' :=
  (fun u ↦ κ.1 (u.comap (algebraMap E E')), fun u ↦ κ.2 (u.comap (algebraMap E E')))

/-- Twisted characters of a base changed weight. For `E'/E` Galois of prime degree `p` with
compatible CM types and `σ ≠ 1` in its Galois group, let `ω` apply `σ` to entries and `ρ` be the
representation of the base change of `κ`. Some `s` satisfies `s * ρ δ = ρ (ω δ) * s`, and when the
twisted norm `δ * ω δ * ⋯ * ω^[p - 1] δ` is the image `j γ` of `γ` over `E`, the trace of `s * ρ δ`
is the character of `κ` at `γ`. -/
lemma New.exists_trace_mul_weightRep_eq_of_twistedNorm_eq [DecidableEq n] (hσ : σ ≠ 1)
    [hp : Fact (finrank E E').Prime] [CMType E] [hCM : CMTypeOver E E'] (κ : Weight E) :
    let j : U (1 : Matrix n n E) →* U (1 : Matrix n n E') :=
      U.map (algebraMap E E') (map_star_CM (algebraMap E E')) (map_one (algebraMap E E').mapMatrix)
    let ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E') := U.mapEnd (map_star_CM σ)
    let ρ : Representation ℂ (U (stdSpace E' n).J) (WeylIndex n κ.baseChange.fst → ℂ) :=
      (stdSpace E' n).weightRep κ.baseChange.fst κ.baseChange.snd
    ∃ s : (WeylIndex n κ.baseChange.fst → ℂ) →ₗ[ℂ] WeylIndex n κ.baseChange.fst → ℂ,
      -- (a) `s` intertwines `ρ` and its twist by `σ`
      (∀ δ : U (stdSpace E' n).J, s * ρ δ = ρ (ω δ) * s) ∧
      -- (b) the twisted character at `δ` is the character of the weight at the norm of `δ`
      ∀ (δ : U (1 : Matrix n n E')) (γ : U (1 : Matrix n n E)),
        twistedNorm ω (Module.finrank E E') δ = j γ →
        (s * ρ δ).trace ℂ (WeylIndex n κ.baseChange.fst → ℂ) =
          ((stdSpace E n).weightRep κ.fst κ.snd γ).trace ℂ (WeylIndex n κ.fst → ℂ) := by
  -- The places of `E'` are pairs (power of `σ`, place of `E`), so `ρ` is the tensor product of the
  -- twists `G l` of the weight `κ` by `σ ^ l`. The operator `s` rotates the factors, and the trace
  -- of `s * ρ δ` is a sum over cycles, the trace of the product of the `G l δ`.
  obtain ⟨k, hE⟩ : ∃ k : ℕ, finrank E E' = k + 1 := Nat.exists_eq_add_one.2 hp.out.pos
  intro j ω ρ
  -- `φ v` extends `(Φ v).comp conj` to `E'`; so does `(Φ u).comp conj` for `u` above `v`.
  let φ (v : InfinitePlace E) : E' →+* ℂ := lift E' ((Φ v).comp conj)
  have h_agree (u : InfinitePlace E') : (φ (u.comap (algebraMap E E'))).comp (algebraMap E E') =
      ((Φ u).comp conj).comp (algebraMap E E') := by
    have hΦ : ∀ x : E, Φ u (algebraMap E E' x) = Φ (u.comap (algebraMap E E')) x := by
      simpa [RingHom.ext_iff] using hCM.eq_chosen_iff (Φ u)
    ext x
    simp [φ, hΦ, starRingEnd_apply (R := E), starRingEnd_apply (R := E')]
  -- Two embeddings that agree on `E` differ by a power of `σ`: `(Φ u).comp conj = φ v ∘ σ ^ i u`.
  have h_pow_bij : Bijective fun l : Fin (k + 1) ↦ σ ^ (l : ℕ) := by
    simpa [← hE] using bijective_pow_of_ne_one_of_prime_finrank hσ
  have h_exists (u : InfinitePlace E') : ∃ l : Fin (k + 1),
      (φ (u.comap (algebraMap E E'))).comp ((σ ^ (l : ℕ) : Gal(E'/E)) : E' →+* E') =
        (Φ u).comp conj :=
    (AlgEquiv.symm_bijective.comp h_pow_bij).surjective.exists.mp
      (exists_comp_symm_eq_of_comp_eq _ _ (h_agree u))
  choose i hi using h_exists
  -- `u ↦ (i u, v)` is injective, so bijective by counting: the infinite places are unramified.
  have h_unram : IsUnramifiedAtInfinitePlaces E E' := ⟨by simp [InfinitePlace.IsUnramified]⟩
  have h_bij : Bijective fun u ↦
      (⟨i u, u.comap (algebraMap E E')⟩ : Σ _ : Fin (k + 1), InfinitePlace E) := by
    refine (Nat.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
    · -- equal pairs give `(Φ u).comp conj = (Φ u').comp conj` by `hi`; cancel `conj`, then `mk_Φ`
      intro u u' h_pair
      have h1 : i u = i u' := congrArg Sigma.fst h_pair
      have h2 : u.comap (algebraMap E E') = u'.comap (algebraMap E E') := congrArg Sigma.snd h_pair
      have hΦ : (Φ u).comp conj = (Φ u').comp conj := by rw [← hi u, ← hi u', h1, h2]
      rw [← mk_Φ u, ← mk_Φ u']
      exact congrArg InfinitePlace.mk (RingHom.ext fun x ↦ by
        have h := DFunLike.congr_fun hΦ (conj x)
        simpa only [RingHom.comp_apply, starRingEnd_self_apply] using h)
    · simp [mul_comm, hE, h_unram.card_infinitePlace]
  let e : InfinitePlace E' ≃ Σ _ : Fin (k + 1), InfinitePlace E := ofBijective _ h_bij
  -- A basis index of `ρ` is a family of `k + 1` basis indices of the weight `κ`.
  let A : WeylIndex n (κ.baseChange : Weight E').fst ≃ (Fin (k + 1) → WeylIndex n κ.fst) :=
    .trans (.symm (.piCongrLeft' _ e.symm)) (.piCurry _)
  -- `G l` is the weight `κ` at the embeddings `φ v ∘ σ ^ l`.
  let G (l : ℕ) : GL n E' →* Matrix (WeylIndex n κ.fst) (WeylIndex n κ.fst) ℂ :=
    (weylRep κ.fst κ.snd).comp (.pi fun v ↦ GeneralLinearGroup.map ((φ v).comp (σ ^ l).toRingHom))
  have h_G_succ (l : ℕ) (δ : U (1 : Matrix n n E')) : G l (ω δ) = G (l + 1) δ := rfl
  have h_tensor (δ : U (1 : Matrix n n E')) :
      ρ δ = toLin' (of fun a b ↦ ∏ l : Fin (k + 1), G l δ (A a l) (A b l)) := by
    refine (LinearMap.ext (stdSpace_weightRep_apply δ)).trans (congrArg _ (ext ?_))
    -- Schur matrices and determinants are products over the places, reindexed by `e`; the two
    -- sides then agree entrywise by the definitions of `e`, `A` and `κ.baseChange`.
    simp only [weylRep, ← hi, GeneralLinearGroup.map_comp, GeneralLinearGroup.map_comp_apply,
      MonoidHom.coe_mk, OneHom.coe_mk, GeneralLinearGroup.val_map_apply, coe_coe, AlgEquiv.coe_pow,
      Matrix.map_map, Matrix.smul_apply, FitsRanks.refl, schur_apply_eq_prod (Φ := InfinitePlace _),
      RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, MonoidHom.coe_comp,
      Function.comp_apply, MonoidHom.pi_apply, prod_smul, ← Fintype.prod_sigma', ← e.prod_comp,
      of_apply, A.forall_congr_left, apply_symm_apply, G]
    exact fun _ _ ↦ rfl
  have h_norm (m : ℕ) (δ : U (1 : Matrix n n E')) :
      twistedNorm ω (m + 1) δ = δ * twistedNorm ω m (ω δ) := by simp [twistedNorm]
  -- Summing over the inner vertices of a cycle multiplies the matrices.
  have h_cycle (m : ℕ) (δ : U (1 : Matrix n n E'))
      (M : Matrix (WeylIndex n κ.fst) (WeylIndex n κ.fst) ℂ) :
      trace (M * G 0 ((twistedNorm ω m (ω δ) : U (1 : Matrix n n E')) : GL n E')) =
        ∑ x : Fin (m + 1) → WeylIndex n κ.fst,
          M (x (last m)) (x 0) * ∏ l : Fin m, G (l + 1) δ (x l.castSucc) (x l.succ) := by
    induction m generalizing δ M with
    | zero =>
      simp [twistedNorm, trace, reindex_equiv (consEquiv _), Fintype.sum_prod_type_right,
        univ_eq_empty]
    | succ m ih =>
      -- Use `ih` for `ω δ` and `M * G 0 (ω δ)`; by definition `G l (ω δ) = G (l + 1) δ`.
      simp [h_norm, ← (consEquiv fun _ : Fin (m + 2) ↦ _).sum_comp, ← mul_assoc, Matrix.mul_apply,
        sum_mul, Fintype.sum_prod_type_right, prod_univ_succ, ih]
      rfl
  -- `s` permutes the basis by rotating the index `Fin (k + 1)`.
  refine ⟨(submatrix 1 (A.trans ((finRotate _).piCongrLeft' _)) A).toLin',
    fun (δ : U (1 : Matrix n n E')) ↦ ?_, fun δ γ h_norm_eq ↦ ?_⟩
  · -- Rotate the product; the last factor returns to the first because `σ ^ (k + 1) = 1`.
    simp_rw [h_tensor, End.mul_eq_comp, ← toLin'_mul, mul_submatrix_one, one_submatrix_mul]
    refine congrArg _ (ext fun a b ↦ (Equiv.prod_comp (finRotate _) _).symm.trans ?_)
    simp only [h_G_succ]
    simp [G, val_add, ← hE, ← IsGalois.card_aut_eq_finrank]
  · -- Both traces are the sum of `h_cycle` for `M = G 0 δ`.
    have h_char : ((stdSpace E n).weightRep κ.fst κ.snd γ).trace ℂ (WeylIndex n κ.fst → ℂ) =
        trace (G 0 (j γ)) := by
      rw [LinearMap.ext (g := toLin' _) (stdSpace_weightRep_apply γ), trace_toLin'_eq]
      refine congrArg (fun g ↦ trace (weylRep κ.fst κ.snd g)) (funext fun v ↦ Units.ext ?_)
      ext a b
      change ((Φ v).comp conj) ((γ : Matrix n n E) a b) =
        (φ v) ((σ ^ 0 : Gal(E'/E)) (algebraMap E E' ((γ : Matrix n n E) a b)))
      rw [pow_zero, AlgEquiv.one_apply, lift_algebraMap_apply]
    -- by `h_norm_eq`, `j γ = δ * twistedNorm ω k (ω δ)`
    rw [h_char, ← h_norm_eq, hE, h_norm, Subgroup.coe_mul, (G 0).map_mul, h_cycle k δ (G 0 δ)]
    -- the trace of `s * ρ δ` unfolds to the same cycle sum
    simp_rw [h_tensor, End.mul_eq_comp, ← toLin'_mul, trace_toLin'_eq, one_submatrix_mul]
    simp [trace, ← A.symm.sum_comp, prod_univ_succ, ← cycleRange_last]

end BaseChangeWeight

/-!
## The twisted trace identity for matching pairs

Conventions: `New.galoisGf σ` is the action of `σ` on `New.Gf E' n`, `New.baseChangeGf` the
inclusion of `New.Gf E n` into `New.Gf E' n`, and `New.IsMatchingPair` the matching condition
between a function `f` over `E` and a function `φ` over `E'` (on `New.Gf E' n`, written `U 1`).
-/

section TwistedTraceIdentity

open Matrix Polynomial Module Function New U Space

attribute [local implicit_reducible] stdSpace

/-- Let `x` and `δ` be finite adelic unitary points over `E'`. The twisted norm (for the action
`galoisGf σ` of `σ`, with `[E' : E]` factors) of the twisted conjugate `x⁻¹ * δ * σ x` is the
conjugate `x⁻¹ * N δ * x` of the twisted norm `N δ` of `δ`. This uses `σ ^ [E' : E] = 1`. -/
lemma New.twistedNorm_inv_mul_mul_galoisGf {E E' n : Type*} [Field E] [CMType E] [Field E']
    [Algebra E E']
    [Fintype n] [DecidableEq n] {σ : Gal(E'/E)} [CMTypeOver E E'] [IsGalois E E'] (x δ : Gf E' n) :
    twistedNorm (galoisGf σ) (finrank E E') (x⁻¹ * δ * galoisGf σ x) =
      x⁻¹ * twistedNorm (galoisGf σ) (finrank E E') δ * x := by
  -- `galoisGf σ` applies `adeleMap σ` to the entries, so its `k`-th iterate applies
  -- `adeleMap σ ^ k`.
  have h_iter (k : ℕ) (y : Gf E' n) :
      ((galoisGf σ)^[k] y).val = y.val.map (adeleMap ↑σ ^ k) := by
    induction k generalizing y with
    | zero => rfl
    | succ k ih => exact ih (galoisGf σ y)
  refine twistedNorm_conj _ _ (Subtype.ext ?_) _
  rw [h_iter, adeleMap_pow_finrank_eq_one]
  rfl

/-- A global completion of a norm root `z` of the characteristic polynomial `P` of a rational
unitary `δ` over `E'`, when `σ` fixes `P`: for some rational `z₀` and adelic `b`,
`x = z₀ * σ b * z` is invertible at `e ν` for every rational `ν` of characteristic polynomial `P`,
and every root quotient `r` of `x` at `e ν` (`r * x(e ν)ᴴ = x(e ν)`) is one of `b` (`e` the
inclusion of rational into adelic points). -/
private lemma New.exists_isUnit_aeval_and_isRootQuotient_le {E E' n : Type} [Field E] [CMType E]
    [Field E'] [Algebra E E'] [Fintype n] [DecidableEq n] {σ : Gal(E'/E)} (hσ : σ ≠ 1)
    {μ : (𝔸f E)ˣ →* ℂˣ} [CMTypeOver E E'] [IsStep (E := E) E' μ] {δ : U (1 : Matrix n n E')}
    (h_fixed : σ • (δ : Matrix n n E').charpoly = (δ : Matrix n n E').charpoly)
    {z : (𝔸f E')[X]} (hz : IsNormRoot n (adeleMap σ) (finrank E E') 1 (kerCompNorm E' μ)
      ((δ : Matrix n n E').charpoly.map (algebraMap E' (𝔸f E'))) z) :
    let e : U (1 : Matrix n n E') →* Gf E' n :=
      U.map (algebraMap E' (𝔸f E')) (fun x : E' ↦ (star_algebraMap_finAdele x).symm)
        (map_one (algebraMap E' (𝔸f E')).mapMatrix)
    ∃ (z₀ : E'[X]) (b : (𝔸f E')[X]), ∀ ν : U (1 : Matrix n n E'),
      (ν : Matrix n n E').charpoly = (δ : Matrix n n E').charpoly →
        let x : (𝔸f E')[X] := z₀.map (algebraMap E' (𝔸f E')) * (b.map (adeleMap ↑σ) * z)
        IsUnit (aeval (e ν : Matrix n n (𝔸f E')) x) ∧
          IsRootQuotient (e ν) x ≤ IsRootQuotient (e ν) b := by
  intro e
  have hσ_pow : σ ^ finrank E E' = 1 := by simp [← IsGalois.card_aut_eq_finrank]
  obtain ⟨z₀, b, hb⟩ := exists_global_root Fact.out hσ_pow hσ ⟨δ, rfl⟩ h_fixed hz
  rw [mul_comm z] at hb
  refine ⟨z₀, b, fun ν hν ↦ hb (e ν) ?_⟩
  -- A unitary matrix is normal, so the radical of its characteristic polynomial kills it.
  exact (map_aeval_matrix _ _ _).symm.trans (by simp [← hν])

/-- Let `C` be a class of `σ`-fixed polynomials over `E'` with norm roots `z P` (`IsNormRoot`: among
other things, the twisted norm `z * σ z * ⋯` of `z P` has root quotient `g` at each adelic `g` of
characteristic polynomial `P`). To each rational `ν` with characteristic polynomial `q ν` in `C`
belong a rational `A ν` and an adelic `B ν`, compatible with conjugation, such that for `δ` with
`δ * ω ν = ν * δ` (`ω` the action of `σ`) a root quotient `r` of `z (q ν)` at `e ν`
(`r * z(e ν)ᴴ = z(e ν)`) makes `r⁻¹ * e δ` the twisted conjugate of `e (A ν * δ)` by `B ν`; `e`
includes rational into finite adelic unitary points, and `U 1` is the rational unitary group
`U (1 : Matrix n n E')`. -/
lemma New.exists_isRootQuotient_of_isNormRoot {E E' n : Type} [Field E] [CMType E] [Field E']
  [Algebra E E']
    [Fintype n] [DecidableEq n] {σ : Gal(E'/E)} (hσ : σ ≠ 1) {μ : (𝔸f E)ˣ →* ℂˣ} [CMTypeOver E E']
    [IsStep (E := E) E' μ] {C : E'[X] → Prop} {z : E'[X] → (𝔸f E')[X]}
    (hC : ∀ P : E'[X], C P → σ • P = P) (hz : ∀ P : E'[X], C P →
      IsNormRoot n (adeleMap σ) (finrank E E') 1 (kerCompNorm E' μ) (P.map (algebraMap E' (𝔸f E')))
        (z P)) :
    let e : U (1 : Matrix n n E') →* Gf E' n :=
      U.map (algebraMap E' (𝔸f E')) (fun x : E' ↦ (star_algebraMap_finAdele x).symm)
        (map_one (algebraMap E' (𝔸f E')).mapMatrix)
    let ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E') := U.mapEnd (map_star_CM σ)
    let q (δ : U (1 : Matrix n n E')) : E'[X] := (δ : Matrix n n E').charpoly
    ∃ (A : U (1 : Matrix n n E') → U (1 : Matrix n n E')) (B : U (1 : Matrix n n E') → Gf E' n),
      (∀ {ν ν' : U (1 : Matrix n n E')} (g : U (1 : Matrix n n E')), C (q ν) → SemiconjBy g ν ν' →
        C (q ν') ∧ A ν' = g * A ν * g⁻¹ ∧ B ν' = e g * B ν * (e g)⁻¹) ∧
      ∀ {ν δ : U (1 : Matrix n n E')}, C (q ν) → SemiconjBy δ (ω ν) ν → ∃ r : Gf E' n,
        IsUnit (aeval (e ν : Matrix n n (𝔸f E')) (z (q ν))) ∧
        IsRootQuotient (e ν) (z (q ν)) r ∧
        r⁻¹ * e δ = (B ν)⁻¹ * e (A ν * δ) * galoisGf σ (B ν) := by
  intro e ω q
  have e_ω (δ : U 1) : e (ω δ) = galoisGf σ (e δ) := by
    simp +zetaDelta [U.map, Gf.val_ext_iff, Units.ext_iff, ← ext_iff]
  -- `exists_isUnit_aeval_and_isRootQuotient_le` completes `z P` to `x = z₀ * σ b * z P` with `z₀`
  -- rational and `x` invertible at `e ν` when `P = q ν`. Put `A ν = z₀(ν) / z₀(ν)ᴴ` and
  -- `B ν = x(ν) / x(ν)ᴴ`, the roots (`IsRootQuotient`) for `z₀` and `x`; `B ν` is also a root for
  -- `b`.
  have h_global (P : E'[X]) (hP : ∃ δ : U 1, q δ = P ∧ C (q δ)) := by
    have h_eq : (hP.choose : Matrix n n E').charpoly = P := hP.choose_spec.1
    have h_eval := New.exists_isUnit_aeval_and_isRootQuotient_le hσ
      (hC _ hP.choose_spec.2) (hz _ hP.choose_spec.2)
    rwa [h_eq] at h_eval
  choose! z₀ b hb using h_global
  replace hb {ν : U 1} (hν_C : C (q ν)) := hb (q ν) ⟨ν, rfl, hν_C⟩ ν rfl
  -- `x(e ν)` is a product of commuting matrices, so each factor is invertible.
  have h_unit {ν : U 1} (hν_C : C (q ν)) :
      IsUnit (aeval (e ν : Matrix n n (𝔸f E')) (z₀ (q ν))) ∧
        IsUnit (aeval (e ν : Matrix n n (𝔸f E')) ((b (q ν)).map (adeleMap (σ : E' →+* E')))) ∧
        IsUnit (aeval (e ν : Matrix n n (𝔸f E')) (z (q ν))) := by
    simpa using (hb hν_C).left
  have h_unit_rat {ν : U 1} (hν_C : C (q ν)) : IsUnit (aeval (ν : Matrix n n E') (z₀ (q ν))) := by
    -- `e ν` is `ν` with `algebraMap E' (𝔸f E')` applied to the entries.
    refine isUnit_of_mapMatrix (algebraMap E' (𝔸f E')) ?_
    rw [RingHom.mapMatrix_apply, map_aeval_matrix]
    simpa [e, U.map] using (h_unit hν_C).left
  -- `A ν` and `B ν` are the unique roots for `z₀` at `ν` and for `x` at `e ν`.
  choose! A hA hA_uniq using fun ν (hν_C : C (q ν)) ↦ existsUnique_isRootQuotient (h_unit_rat hν_C)
  choose! B hB hB_uniq using fun ν (hν_C : C (q ν)) ↦ existsUnique_isRootQuotient (hb hν_C).left
  refine ⟨A, B, fun {ν ν'} g hν_C hg ↦ ?_, fun {ν δ} hν_C hν ↦ ?_⟩
  · -- Conjugate elements have the same `q`, and roots are unique.
    have hq : q ν = q ν' := by simp [q, ← mul_inv_eq_of_eq_mul hg]
    have hν'_C : C (q ν') := by rwa [← hq]
    refine ⟨hν'_C, (hA_uniq _ hν'_C _ ?_).symm, (hB_uniq _ hν'_C _ ?_).symm⟩
    · simpa only [← hq, Subgroup.coe_mul, InvMemClass.coe_inv, Units.val_mul, coe_units_inv] using
        isRootQuotient_conj hg.symm (hA ν hν_C)
    · simpa only [← hq, Gf.coe_mul, Gf.coe_inv, Units.val_mul, coe_units_inv, Subgroup.coe_mul,
        InvMemClass.coe_inv] using isRootQuotient_conj (hg.map e).symm (hB ν hν_C)
  · -- Roots multiply: the roots for the three factors of `x` have product `B ν`.
    obtain ⟨-, -, h_unit_z⟩ := h_unit hν_C
    obtain ⟨r, hr, -⟩ := existsUnique_isRootQuotient h_unit_z
    have h_comm : e ν * e δ = e δ * galoisGf σ (e ν) := by
      simpa only [map_mul, e_ω] using congrArg e hν.symm
    have h_σb :
        IsRootQuotient (e ν) ((b (q ν)).map (adeleMap ↑σ)) ↑(e δ * galoisGf σ (B ν) * (e δ)⁻¹) :=
      isRootQuotient_conj h_comm (isRootQuotient_map _ ((hb hν_C).right _ (hB ν hν_C)))
    have h_prod : e (A ν) * (e δ * galoisGf σ (B ν) * (e δ)⁻¹ * r) = B ν :=
      hB_uniq _ hν_C _ ((isRootQuotient_map _ (hA ν hν_C)).mul (h_σb.mul hr))
    refine ⟨r, h_unit_z, hr, ?_⟩
    rw [map_mul, mul_assoc, eq_inv_mul_iff_mul_eq]
    nth_rw 1 [← h_prod]
    group

section MatchingRoots

variable {E E' n : Type} [Field E] [CMType E] [Field E'] [Algebra E E'] [Fintype n] [DecidableEq n]
  [CMTypeOver E E']

/-- Facts about the maps between unitary points over `E` and `E'` in `New.twisted_trace_identity`:
`j` is base change of rational points from `E` to `E'`, `ω` the action of `σ` on rational points
over `E'`, `e` the inclusion of rational into finite adelic points. The maps `j` and `e` are
injective, the three maps are compatible with `σ` and with base change, Galois descent holds for
adelic and for rational points, and a rational cocycle of twisted norm one that splits adelically
splits (Hasse principle). -/
private structure New.IsBaseChangeMaps (σ : Gal(E'/E))
    (j : U (1 : Matrix n n E) →* U (1 : Matrix n n E'))
    (ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E')) (e : U (1 : Matrix n n E') →* Gf E' n) :
    Prop where
  j_injective : Injective j
  e_injective : Injective e
  map_apply_eq_galoisGf (δ : U (1 : Matrix n n E')) : e (ω δ) = galoisGf σ (e δ)
  map_apply_eq_baseChangeGf (γ : U (1 : Matrix n n E)) :
    e (j γ) = baseChangeGf ((stdSpace E n).embFin γ)
  map_apply_eq_self (γ : U (1 : Matrix n n E)) : ω (j γ) = j γ
  galoisGf_baseChangeGf (g : Gf E n) : galoisGf σ (baseChangeGf g) = baseChangeGf g
  /-- Galois descent for finite adelic points. -/
  exists_baseChangeGf_eq (g : Gf E' n) : galoisGf σ g = g → ∃ k : Gf E n, baseChangeGf k = g
  /-- Galois descent for rational points. -/
  exists_j_eq (δ : U (1 : Matrix n n E')) : ω δ = δ → ∃ γ : U (1 : Matrix n n E), j γ = δ
  /-- The Hasse principle: a rational cocycle of twisted norm one that splits adelically splits. -/
  exists_ω_eq_inv_mul (s : U (1 : Matrix n n E')) (u : Gf E' n) :
    e s = u * (galoisGf σ u)⁻¹ → twistedNorm ω (finrank E E') s = 1 →
      ∃ g : U (1 : Matrix n n E'), ω g = s⁻¹ * g

/-- Facts about a matching pair `(f, φ)` used by the double counting in
`New.twisted_trace_identity`. `Good ν` marks the rational `ν` over `E'` whose characteristic
polynomial occurs in the matching condition, with a rational root quotient `A ν` and an adelic one
`B ν`. The fields: twisted invariance of `φ` under `K`, goodness at non-zero terms, compatibility
with conjugation, the twisted norm through `A ν` and `B ν`, and matching of values and of `K`. -/
private structure New.IsMatchingRoots (σ : Gal(E'/E)) (K : Subgroup (Gf E' n)) (f : Gf E n → ℂ)
    (φ : U (1 : Matrix n n (𝔸f E')) → ℂ) (j : U (1 : Matrix n n E) →* U (1 : Matrix n n E'))
    (ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E')) (e : U (1 : Matrix n n E') →* Gf E' n)
    (Good : U (1 : Matrix n n E') → Prop) (A : U (1 : Matrix n n E') → U (1 : Matrix n n E'))
    (B : U (1 : Matrix n n E') → Gf E' n) : Prop where
  apply_inv_mul_mul_galoisGf (k : Gf E' n) (hk : k ∈ K) (δ : Gf E' n) :
    φ (k⁻¹ * δ * galoisGf σ k) = φ δ
  good_of_apply_ne_zero (x : Gf E n) (γ : U (1 : Matrix n n E)) :
    f (x⁻¹ * (stdSpace E n).embFin γ * x) ≠ 0 → Good (j γ)
  good_twistedNorm (x : Gf E' n) (δ : U (1 : Matrix n n E')) :
    φ (x⁻¹ * e δ * galoisGf σ x) ≠ 0 → Good (twistedNorm ω (finrank E E') δ)
  good_and_conj_of_semiconjBy {ν ν' : U (1 : Matrix n n E')} (g : U (1 : Matrix n n E')) :
    Good ν → SemiconjBy g ν ν' →
    Good ν' ∧ A ν' = g * A ν * g⁻¹ ∧ B ν' = e g * B ν * (e g)⁻¹
  map_twistedNorm_eq {ν δ : U (1 : Matrix n n E')} : Good ν → SemiconjBy δ (ω ν) ν →
    e (twistedNorm ω (finrank E E') δ) =
      e ν * ((B ν)⁻¹ * e (twistedNorm ω (finrank E E') (A ν * δ)) * B ν)
  exists_inv_mul_eq {ν δ : U (1 : Matrix n n E')} : Good ν → SemiconjBy δ (ω ν) ν →
    ∃ r : Gf E' n, r⁻¹ * e δ = (B ν)⁻¹ * e (A ν * δ) * galoisGf σ (B ν) ∧
      ∀ y : Gf E' n,
        (∀ g : Gf E n, baseChangeGf g = y⁻¹ * e ν * y →
          twistedNorm (galoisGf σ) (finrank E E') (y⁻¹ * r * y) = y⁻¹ * e ν * y →
          f g = φ (y⁻¹ * r * y)) ∧
        ∀ δ' : Gf E' n, twistedNorm (galoisGf σ) (finrank E E') δ' = y⁻¹ * e ν * y → φ δ' ≠ 0 →
          (y⁻¹ * r * y)⁻¹ * δ' ∈ K

variable {σ : Gal(E'/E)} {j : U (1 : Matrix n n E) →* U (1 : Matrix n n E')}
  {ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E')} {e : U (1 : Matrix n n E') →* Gf E' n}
  {K : Subgroup (Gf E' n)} {f : Gf E n → ℂ} {φ : U (1 : Matrix n n (𝔸f E')) → ℂ}
  {Good : U (1 : Matrix n n E') → Prop} {A : U (1 : Matrix n n E') → U (1 : Matrix n n E')}
  {B : U (1 : Matrix n n E') → Gf E' n}

/-- If `δ * ω ν = ν * δ` for the action `ω` of `σ` on rational points over `E'`, then the
characteristic polynomial of `ν` is fixed by `σ`. -/
private lemma New.smul_charpoly_eq_of_semiconjBy {ν δ : U (1 : Matrix n n E')}
    (hν : SemiconjBy δ (U.mapEnd (map_star_CM σ) ν) ν) :
    σ • (ν : Matrix n n E').charpoly = (ν : Matrix n n E').charpoly := by
  -- `ω ν` is conjugate to `ν` by `δ`, and its matrix is that of `ν` with `σ` on the entries.
  have h_map : ((ν : Matrix n n E').map σ).charpoly = (ν : Matrix n n E').charpoly := by
    simpa [U.map, ← mul_assoc] using
      congrArg (fun g : U (1 : Matrix n n E') ↦ ((δ⁻¹ * g : U 1) : Matrix n n E').charpoly) hν.eq
  rwa [smul_eq_map, ← charpoly_map]

/-- The maps of `New.twisted_trace_identity` satisfy `IsBaseChangeMaps` for `σ ≠ 1` over a step
`E'/E`: base change `j` of rational points, the action `ω` of `σ` on rational points over `E'`, and
the inclusion `e` of rational into finite adelic points. -/
private lemma New.isBaseChangeMaps (μ : (𝔸f E)ˣ →* ℂˣ) [IsStep (E := E) E' μ] (hσ : σ ≠ 1) :
    let j : U (1 : Matrix n n E) →* U (1 : Matrix n n E') :=
      U.map (algebraMap E E') (map_star_CM (algebraMap E E')) (map_one (algebraMap E E').mapMatrix)
    let ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E') := U.mapEnd (map_star_CM σ)
    let e : U (1 : Matrix n n E') →* Gf E' n :=
      U.map (algebraMap E' (𝔸f E')) (fun x : E' ↦ (star_algebraMap_finAdele x).symm)
        (map_one (algebraMap E' (𝔸f E')).mapMatrix)
    New.IsBaseChangeMaps σ j ω e := by
  intro j ω e
  have hσ_alg : (σ : E' →+* E').comp (algebraMap E E') = algebraMap E E' :=
    RingHom.ext σ.commutes
  refine ⟨fun γ₁ γ₂ h ↦ Subtype.ext (Units.ext (Matrix.ext fun a b ↦
      (algebraMap E E').injective
        (congr_fun₂ (congrArg (fun u : U (1 : Matrix n n E') ↦ (u : Matrix n n E')) h) a b))),
    fun δ₁ δ₂ h ↦ Subtype.ext (Units.ext (Matrix.ext fun a b ↦
      (algebraMap E' (𝔸f E')).injective
        (congr_fun₂ (congrArg (fun u : Gf E' n ↦ (u : Matrix n n (𝔸f E'))) h) a b))),
    fun δ ↦ Subtype.ext (Units.ext (Matrix.ext fun a b ↦
      (adeleMap_algebraMap (σ : E' →+* E') ((δ : Matrix n n E') a b)).symm)),
    fun γ ↦ Subtype.ext (Units.ext (Matrix.ext fun a b ↦ by
      have h_std : (((stdSpace E n).embFin γ : Gf E n) : Matrix n n (𝔸f E)) =
          (γ : Matrix n n E).map (algebraMap E (𝔸f E)) := by
        change (((stdSpace E n).ratEmbed γ).2 : Matrix n n (𝔸f E)) = _
        dsimp only [Space.ratEmbed, Space.toRatCoords, stdSpace, G.toUnitary,
          MonoidHom.comp_apply, MulEquiv.symm_trans_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.coe_mk, Equiv.coe_fn_symm_mk]
        simp only [U.map, U.conj, inv_one, one_mul, mul_one]
        rfl
      change algebraMap E' (𝔸f E') (algebraMap E E' ((γ : Matrix n n E) a b)) =
        adeleMap (algebraMap E E') ((((stdSpace E n).embFin γ : Gf E n) : Matrix n n (𝔸f E)) a b)
      rw [h_std, Matrix.map_apply, adeleMap_algebraMap])),
    fun γ ↦ Subtype.ext (Units.ext (Matrix.ext fun a b ↦ σ.commutes ((γ : Matrix n n E) a b))),
    fun g ↦ Subtype.ext (Units.ext (Matrix.ext fun a b ↦
      (adeleMap_adeleMap _ _ _).trans (congrArg (fun f ↦ adeleMap f _) hσ_alg))),
    fun g hg ↦ ?_, fun δ hδ ↦ ?_,
    fun s u hs hN ↦ hasse_principle_coboundary hσ u hs hN⟩
  · -- Galois descent for adelic points, entry by entry.
    have h_entry (a b : n) : adeleMap (σ : E' →+* E') ((g : Matrix n n (𝔸f E')) a b) =
        (g : Matrix n n (𝔸f E')) a b :=
      congr_fun₂ (congrArg (fun h : Gf E' n ↦ (h : Matrix n n (𝔸f E'))) hg) a b
    have h_desc (a b : n) : (g : Matrix n n (𝔸f E')) a b ∈ (finAdeleIncl E E').range :=
      mem_range_finAdeleIncl_of_adeleMap_eq hσ (h_entry a b)
    choose M hM using h_desc
    obtain ⟨k, -, hk⟩ := mem_range_map (adeleMap_star (algebraMap E E')) (adeleMap_injective _)
      isUnit_one _ (M := M) (ext hM)
    exact ⟨k, hk⟩
  · -- Galois descent for rational points, entry by entry.
    have h_entry (a b : n) : σ ((δ : Matrix n n E') a b) = (δ : Matrix n n E') a b :=
      congr_fun₂ (congrArg (fun h : U (1 : Matrix n n E') ↦ (h : Matrix n n E')) hδ) a b
    have h_desc (a b : n) : (δ : Matrix n n E') a b ∈ (algebraMap E E').range :=
      mem_range_algebraMap_of_fixed_of_prime hσ (h_entry a b)
    choose M hM using h_desc
    obtain ⟨γ, -, hγ⟩ :=
      mem_range_map _ (algebraMap E E').injective isUnit_one _ (M := M) (ext hM)
    exact ⟨γ, hγ⟩

/-- The twisted norm for `galoisGf σ` of a twisted conjugate `x⁻¹ * e δ * σ x` of a rational point
`δ` over `E'` is the conjugate by `x` of `e` applied to the twisted norm of `δ` for `ω`. -/
private lemma New.IsBaseChangeMaps.twistedNorm_conj [IsGalois E E']
    (H : New.IsBaseChangeMaps σ j ω e) (x : Gf E' n) (δ : U (1 : Matrix n n E')) :
    twistedNorm (galoisGf σ) (finrank E E') (x⁻¹ * e δ * galoisGf σ x) =
      x⁻¹ * e (twistedNorm ω (finrank E E') δ) * x := by
  rw [map_twistedNorm e H.map_apply_eq_galoisGf, twistedNorm_inv_mul_mul_galoisGf]

/-- A rational point `δ` over `E'` and its twisted norm `ν` for `ω` satisfy `δ * ω ν = ν * δ`. -/
private lemma New.IsBaseChangeMaps.semiconjBy_twistedNorm [IsGalois E E']
    (H : New.IsBaseChangeMaps σ j ω e) (δ : U (1 : Matrix n n E')) :
    SemiconjBy δ (ω (twistedNorm ω (finrank E E') δ)) (twistedNorm ω (finrank E E') δ) := by
  apply H.e_injective
  -- Conjugate the twisted norm of `e δ` by `e δ` itself.
  have h_conj : e δ * twistedNorm (galoisGf σ) (finrank E E') ((e δ)⁻¹ * e δ * galoisGf σ (e δ)) =
      e δ * ((e δ)⁻¹ * e (twistedNorm ω (finrank E E') δ) * e δ) := by
    rw [H.twistedNorm_conj]
  rw [inv_mul_cancel, one_mul, ← H.map_apply_eq_galoisGf,
    ← map_twistedNorm e H.map_apply_eq_galoisGf, ← map_twistedNorm ω (fun _ ↦ rfl),
    mul_assoc (e δ)⁻¹, mul_inv_cancel_left, ← map_mul, ← map_mul] at h_conj
  exact h_conj

/-- `(A ν)⁻¹` commutes with a good `ν`: take `g = ν' = ν` in
`IsMatchingRoots.good_and_conj_of_semiconjBy`. -/
private lemma New.IsMatchingRoots.commute_inv (R : New.IsMatchingRoots σ K f φ j ω e Good A B)
    {ν : U (1 : Matrix n n E')} (h_good : Good ν) : Commute (A ν)⁻¹ ν := by
  obtain ⟨-, hA, -⟩ := R.good_and_conj_of_semiconjBy ν h_good rfl
  exact Commute.inv_left (mul_eq_of_eq_mul_inv hA)

/-- For a good base change `j γ`, `(A (j γ))⁻¹ * ω (j γ) = j γ * (A (j γ))⁻¹` (`ω` fixes `j γ`). -/
private lemma New.IsMatchingRoots.semiconjBy_inv (R : New.IsMatchingRoots σ K f φ j ω e Good A B)
    (H : New.IsBaseChangeMaps σ j ω e) {γ : U (1 : Matrix n n E)} (h_good : Good (j γ)) :
    SemiconjBy (A (j γ))⁻¹ (ω (j γ)) (j γ) := by
  rw [H.map_apply_eq_self]
  exact R.commute_inv h_good

/-- For a good base change `j γ`, the twisted norm of `(A (j γ))⁻¹` is `j γ`. -/
private lemma New.IsMatchingRoots.twistedNorm_inv (R : New.IsMatchingRoots σ K f φ j ω e Good A B)
    (H : New.IsBaseChangeMaps σ j ω e) {γ : U (1 : Matrix n n E)} (h_good : Good (j γ)) :
    twistedNorm ω (finrank E E') (A (j γ))⁻¹ = j γ := by
  apply H.e_injective
  rw [R.map_twistedNorm_eq h_good (R.semiconjBy_inv H h_good)]
  simp [twistedNorm]

/-- For a good base change `j γ` and `x` over `E`, the value of `f` at `x⁻¹ * γ * x` is the value of
`φ` at the twisted conjugate of `e (A (j γ))⁻¹` by `y = (B (j γ))⁻¹ * baseChangeGf x`. -/
private lemma New.IsMatchingRoots.apply_inv_mul_embFin_mul_eq [IsGalois E E']
    (R : New.IsMatchingRoots σ K f φ j ω e Good A B) (H : New.IsBaseChangeMaps σ j ω e)
    (x : Gf E n) (γ : U (1 : Matrix n n E)) (h_good : Good (j γ)) :
    f (x⁻¹ * (stdSpace E n).embFin γ * x) =
      φ (((B (j γ))⁻¹ * baseChangeGf x)⁻¹ * e (A (j γ))⁻¹ *
        galoisGf σ ((B (j γ))⁻¹ * baseChangeGf x)) := by
  -- Take `δ = (A (j γ))⁻¹` in `exists_inv_mul_eq`; its twisted norm is `j γ`.
  have h_semi : SemiconjBy (A (j γ))⁻¹ (ω (j γ)) (j γ) := R.semiconjBy_inv H h_good
  obtain ⟨r, hrδ, h_match⟩ := R.exists_inv_mul_eq h_good h_semi
  have h_comm_B : Commute (B (j γ)) (e (j γ)) := by
    obtain ⟨-, -, hB⟩ := R.good_and_conj_of_semiconjBy (j γ) h_good rfl
    exact mul_eq_of_eq_mul_inv hB
  set y : Gf E' n := (B (j γ))⁻¹ * baseChangeGf x
  have hr_eq : r = e (A (j γ))⁻¹ * (galoisGf σ (B (j γ)))⁻¹ * B (j γ) := by
    simpa [eq_inv_mul_iff_mul_eq, eq_mul_inv_iff_mul_eq, mul_assoc] using congrArg Inv.inv hrδ
  have h_eq : y⁻¹ * r * y = y⁻¹ * e (A (j γ))⁻¹ * galoisGf σ y := by
    simp [y, hr_eq, H.galoisGf_baseChangeGf, mul_assoc]
  have h_norm : twistedNorm (galoisGf σ) (finrank E E') (y⁻¹ * r * y) = y⁻¹ * e (j γ) * y := by
    rw [h_eq, H.twistedNorm_conj, R.twistedNorm_inv H h_good]
  have h_bc : baseChangeGf (x⁻¹ * (stdSpace E n).embFin γ * x) = y⁻¹ * e (j γ) * y := by
    simp [y, ← H.map_apply_eq_baseChangeGf, h_comm_B.left_comm, mul_assoc]
  obtain ⟨h_value, -⟩ := h_match y
  rw [h_value _ h_bc h_norm, h_eq]

/-- For a matching pair `(f, φ)` (`IsMatchingPair`) over a step `E'/E`, with `e` the inclusion of
rational into finite adelic unitary points over `E'`, `ω` the action of `σ` on rational points
and `j` base change from `E` (`IsBaseChangeMaps`), there are a class `Good` of rational points and
root quotients `A`, `B` with the properties of `IsMatchingRoots`. -/
private lemma New.exists_isMatchingRoots (hσ : σ ≠ 1) {μ : (𝔸f E)ˣ →* ℂˣ} [IsStep (E := E) E' μ]
    (h_pair : IsMatchingPair (adeleMap_star σ) (finrank E E') 1 (kerCompNorm E' μ) baseChangeGf K f
      φ) :
    let e : U (1 : Matrix n n E') →* Gf E' n :=
      U.map (algebraMap E' (𝔸f E')) (fun x : E' ↦ (star_algebraMap_finAdele x).symm)
        (map_one (algebraMap E' (𝔸f E')).mapMatrix)
    let ω : U (1 : Matrix n n E') →* U (1 : Matrix n n E') := U.mapEnd (map_star_CM σ)
    ∀ _h_maps : New.IsBaseChangeMaps σ j ω e,
      ∃ (Good : U (1 : Matrix n n E') → Prop) (A : U (1 : Matrix n n E') → U (1 : Matrix n n E'))
        (B : U (1 : Matrix n n E') → Gf E' n), New.IsMatchingRoots σ K f φ j ω e Good A B := by
  intro e ω H
  obtain ⟨h_inv, h_pair⟩ := h_pair
  -- `C P`: the rational polynomial `P` is `σ`-fixed and is one of those that `IsMatchingPair`
  -- speaks of; `q δ` is the characteristic polynomial of a rational `δ`.
  let q (δ : U (1 : Matrix n n E')) : E'[X] := (δ : Matrix n n E').charpoly
  have charpoly_e (δ : U (1 : Matrix n n E')) :
      (e δ : Matrix n n (𝔸f E')).charpoly = (q δ).map (algebraMap E' (𝔸f E')) := charpoly_map _ _
  have charpoly_conj (x : Gf E' n) (ν : U (1 : Matrix n n E')) :
      ((x⁻¹ * e ν * x : Gf E' n) : Matrix n n (𝔸f E')).charpoly =
        (q ν).map (algebraMap E' (𝔸f E')) := by
    rw [← charpoly_e ν, Subgroup.coe_mul, Units.val_mul, Matrix.charpoly_mul_comm,
      ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_left]
  let supp : Set (Gf E' n) :=
    baseChangeGf '' support f ∪ twistedNorm (galoisGf σ) (finrank E E') '' support φ
  let C (P : E'[X]) : Prop := P.map (algebraMap E' (𝔸f E')) ∈
    (fun g : Gf E' n ↦ (g : Matrix n n (𝔸f E')).charpoly) '' supp ∧ σ • P = P
  have fixed_of_C (P : E'[X]) (hP : C P) : σ • P = P := hP.right
  have h_C {ν : U (1 : Matrix n n E')} (δ : U (1 : Matrix n n E')) (hν : SemiconjBy δ (ω ν) ν)
      (x : Gf E' n) (hx : x⁻¹ * e ν * x ∈ supp) : C (q ν) :=
    ⟨⟨x⁻¹ * e ν * x, hx, charpoly_conj x ν⟩, New.smul_charpoly_eq_of_semiconjBy hν⟩
  -- `z P` is the adelic polynomial that `IsMatchingPair` gives for `P`: a norm root (`hz`) whose
  -- root quotients match the values of `f` and `φ` (`hz_match`).
  have h_fixed (P : E'[X]) (hP : C P) :
      (P.map (algebraMap E' (𝔸f E'))).map (adeleMap (σ : E' →+* E')) =
        P.map (algebraMap E' (𝔸f E')) := by
    rw [Polynomial.map_map]
    have h_eq : (adeleMap (σ : E' →+* E')).comp (algebraMap E' (𝔸f E')) =
        (algebraMap E' (𝔸f E')).comp (σ : E' →+* E') :=
      RingHom.ext fun x ↦ adeleMap_algebraMap (σ : E' →+* E') x
    have hσP := fixed_of_C P hP
    rw [smul_eq_map] at hσP
    rw [h_eq, ← Polynomial.map_map]
    exact congrArg (Polynomial.map (algebraMap E' (𝔸f E'))) hσP
  choose! z hz hz_match using fun (P : E'[X]) (hP : C P) ↦ h_pair _ hP.left (h_fixed P hP)
  -- `A ν` is a rational and `B ν` an adelic root quotient at `ν`.
  obtain ⟨A, B, h_conj, h_root⟩ := exists_isRootQuotient_of_isNormRoot hσ fixed_of_C hz
  refine ⟨fun ν ↦ C (q ν), A, B,
    { apply_inv_mul_mul_galoisGf := h_inv
      good_of_apply_ne_zero := fun x γ hf ↦ ?_
      good_twistedNorm := fun x δ hφ ↦ ?_
      good_and_conj_of_semiconjBy := h_conj
      map_twistedNorm_eq := fun {ν δ} hν_C hν ↦ ?_
      exists_inv_mul_eq := fun {ν δ} hν_C hν ↦ ?_ }⟩
  · -- `j γ` is fixed by `ω`, and `e (j γ)` is conjugate to the base change of `x⁻¹ * γ * x`.
    have h_mem : (baseChangeGf x)⁻¹ * e (j γ) * baseChangeGf x ∈ supp :=
      Or.inl ⟨x⁻¹ * (stdSpace E n).embFin γ * x, hf,
        by rw [map_mul, map_mul, map_inv, ← H.map_apply_eq_baseChangeGf]⟩
    exact h_C 1 (by rw [SemiconjBy, one_mul, mul_one, H.map_apply_eq_self]) (baseChangeGf x) h_mem
  · have h_mem : x⁻¹ * e (twistedNorm ω (finrank E E') δ) * x ∈ supp :=
      Or.inr ⟨x⁻¹ * e δ * galoisGf σ x, hφ, H.twistedNorm_conj x δ⟩
    exact h_C δ (H.semiconjBy_twistedNorm δ) x h_mem
  · -- `IsRootQuotient.twistedNorm_eq_mul` splits off the root `r` for `z`, which contributes `e ν`
    -- to the norm.
    obtain ⟨r, h_unit, hr, hrδ⟩ := h_root hν_C hν
    obtain ⟨-, h_norm_root⟩ := hz (q ν) hν_C
    obtain ⟨-, h_root_norm⟩ := h_norm_root (e ν) (charpoly_e ν)
    have h_pol : IsRootQuotient (e ν)
        (twistedNorm (Polynomial.map (adeleMap ↑σ)) (finrank E E') (z (q ν))) (e ν) := by
      simpa using h_root_norm
    have h_comm : e ν * e δ = e δ * galoisGf σ (e ν) := by
      rw [← H.map_apply_eq_galoisGf, (hν.map e).eq]
    rw [← H.twistedNorm_conj, ← hrδ, map_twistedNorm e H.map_apply_eq_galoisGf]
    exact IsRootQuotient.twistedNorm_eq_mul h_pol h_comm hr h_unit
  · -- What `IsMatchingPair` says at a conjugate `y⁻¹ * e ν * y`, whose root for `z` is
    -- `y⁻¹ * r * y`.
    obtain ⟨r, -, hr, hrδ⟩ := h_root hν_C hν
    refine ⟨r, hrδ, fun y ↦ ?_⟩
    have hr_conj : IsRootQuotient (y⁻¹ * e ν * y) ((1 : 𝔸f E') • z (q ν))
        ((y⁻¹ * r * y : Gf E' n) : Matrix n n (𝔸f E')) := by
      simpa only [one_smul, inv_inv] using
        isRootQuotient_conj (mul_inv_cancel_right (y⁻¹ * e ν) y) hr
    exact hz_match _ hν_C _ _ (charpoly_conj y ν) hr_conj

/-- The bijection of moves in `New.twisted_trace_identity`. Let `m` send a pair `(y, γ)` over `E`
to the pair `((B (j γ))⁻¹ * y, (A (j γ))⁻¹)` over `E'`. For a pair `(x, δ)` over `E'` with
`φ (x⁻¹ * e δ * σ x) ≠ 0` there are a pair `z` over `E` and a map `J` on rational points such that,
for every pair `p` over `E`, `J` takes the moves from `p` to `z` bijectively onto the moves from
`(x, δ)` to `m p` (onto `∅` if `j p.2` is not good). A move over `E'` from `(x₀, γ)` to `(x₁, γ₁)`
is a rational `a` with `x₁⁻¹ * a * x₀ ∈ K` and `a⁻¹ * γ₁ * τ a = γ`; `hK_split` says that every
`s ∈ K` of twisted norm one splits in `K`. -/
private lemma New.IsMatchingRoots.exists_bijOn_of_ne_zero [IsGalois E E']
    (hK_split : ∀ s ∈ K,
      twistedNorm (galoisGf σ) (finrank E E') s = 1 → ∃ t ∈ K, galoisGf σ t = s⁻¹ * t)
    (H : New.IsBaseChangeMaps σ j ω e) (R : New.IsMatchingRoots σ K f φ j ω e Good A B)
    (τ : U (1 : Matrix n n E') ≃* U (1 : Matrix n n E'))
    (hτ : ∀ g : U (1 : Matrix n n E'), τ g = ω g)
    (m : Gf E n × U (1 : Matrix n n E) → Gf E' n × U (1 : Matrix n n E'))
    (hm : ∀ p : Gf E n × U (1 : Matrix n n E),
      m p = ((B (j p.snd))⁻¹ * baseChangeGf p.fst, (A (j p.snd))⁻¹))
    {x : Gf E' n} {δ : U (1 : Matrix n n E')} (hφ : φ (x⁻¹ * e δ * galoisGf σ x) ≠ 0) :
    ∃ (z : Gf E n × U (1 : Matrix n n E)) (J : U (1 : Matrix n n E) → U (1 : Matrix n n E')),
      ∀ p : Gf E n × U (1 : Matrix n n E),
        Set.BijOn J
          {a : U (1 : Matrix n n E) |
            z.fst⁻¹ * (stdSpace E n).embFin a * p.fst ∈ K.comap baseChangeGf ∧
              a⁻¹ * z.snd * a = p.snd}
          {g ∈ {g : U (1 : Matrix n n E') |
            (m p).fst⁻¹ * e g * x ∈ K ∧ g⁻¹ * (m p).snd * τ g = δ} | Good (j p.snd)} := by
  -- The twisted norm `ν` of `δ` is good, and the cocycle `A ν * δ` has twisted norm one.
  set ν : U (1 : Matrix n n E') := twistedNorm ω (finrank E E') δ with hν_def
  have hν : SemiconjBy δ (ω ν) ν := H.semiconjBy_twistedNorm δ
  have hν_good : Good ν := R.good_twistedNorm x δ hφ
  have norm_one : twistedNorm ω (finrank E E') (A ν * δ) = 1 := H.e_injective <| by
    have h1 : (B ν)⁻¹ * e (twistedNorm ω (finrank E E') (A ν * δ)) * B ν = 1 :=
      left_eq_mul.mp (R.map_twistedNorm_eq hν_good hν)
    rw [map_one]
    exact mul_left_cancel ((mul_eq_one_iff_eq_inv.mp h1).trans (mul_one (B ν)⁻¹).symm)
  -- A twisted conjugate of `A ν * δ` lies in `K`, by the matching condition at `x`.
  have mem_K : (B ν * x)⁻¹ * e (A ν * δ) * galoisGf σ (B ν * x) ∈ K := by
    obtain ⟨r, hrδ, h_match⟩ := R.exists_inv_mul_eq hν_good hν
    have h_eq : (x⁻¹ * r * x)⁻¹ * (x⁻¹ * e δ * galoisGf σ x) =
        (B ν * x)⁻¹ * e (A ν * δ) * galoisGf σ (B ν * x) :=
      calc _ = x⁻¹ * (r⁻¹ * e δ) * galoisGf σ x := by group
        _ = _ := by rw [hrδ, map_mul (galoisGf σ) (B ν) x]; group
    simpa only [h_eq] using (h_match x).right _ (H.twistedNorm_conj x δ) hφ
  -- It splits in `K` by `hK_split`, hence adelically, hence rationally by the Hasse principle.
  obtain ⟨k, hk, hk_eq⟩ := hK_split _ mem_K <| by
    rw [H.twistedNorm_conj, norm_one, map_one, mul_one, inv_mul_cancel]
  have h_split_ad : e (A ν * δ) = B ν * x * k * (galoisGf σ (B ν * x * k))⁻¹ := by
    rw [map_mul (galoisGf σ) (B ν * x) k, hk_eq]
    group
  obtain ⟨g, hg⟩ := H.exists_ω_eq_inv_mul (A ν * δ) (B ν * x * k) h_split_ad norm_one
  -- Twisting by `g` gives `σ`-fixed elements, which descend to a pair `(y, γ)` over `E`.
  obtain ⟨y, hy⟩ : ∃ y : Gf E n, baseChangeGf y = e g⁻¹ * B ν * x * k :=
    H.exists_baseChangeGf_eq _ (by
      simp only [map_mul, map_inv, ← H.map_apply_eq_galoisGf, hg, hk_eq]
      group)
  obtain ⟨γ, hγ⟩ : ∃ γ : U (1 : Matrix n n E), j γ = g⁻¹ * ν * g := H.exists_j_eq _ <| by
    rw [map_mul, map_mul, map_inv, hg, eq_inv_mul_of_mul_eq hν]
    calc _ = g⁻¹ * A ν * (ν * (A ν)⁻¹) * g := by group
      _ = g⁻¹ * ν * g := by rw [← (R.commute_inv hν_good).eq]; group
  -- `a ↦ (g * j a)⁻¹` matches the moves from `p` to `(y, γ)` with those from `(x, δ)` to `m p`.
  refine ⟨(y, γ), fun a ↦ (g * j a)⁻¹, fun p ↦
    ⟨fun a ⟨ha_mem, ha_conj⟩ ↦ ?_, ?_, fun a ⟨⟨ha_mem, ha_conj⟩, hp_good⟩ ↦ ?_⟩⟩
  · -- Well defined: `(g * j a)⁻¹` conjugates `ν` to `j p.2`, and `A`, `B` follow the conjugation.
    have h_semi : SemiconjBy (g * j a)⁻¹ ν (j p.2) := by
      simp [SemiconjBy, ← ha_conj, hγ, mul_assoc]
    obtain ⟨hp_good, hA, hB⟩ := R.good_and_conj_of_semiconjBy (g * j a)⁻¹ hν_good h_semi
    refine ⟨⟨?_, ?_⟩, hp_good⟩
    · simpa only [hm, hB, _root_.mul_inv_rev, map_mul, map_inv, H.map_apply_eq_baseChangeGf,
        mul_assoc, inv_inv, mul_inv_cancel_left, mul_inv_cancel, mul_one, hy] using
        inv_mem (mul_mem hk ha_mem)
    · simp [hm, hτ, hA, hg, H.map_apply_eq_self, mul_assoc]
  · simp [H.j_injective.eq_iff]
  · -- Surjective: `a` twists `(A (j p.2))⁻¹`, of twisted norm `j p.2`, to `δ`, so it conjugates
    -- `j p.2` to `ν`; then `(a * g)⁻¹` is `σ`-fixed and descends to a move `a'` over `E`.
    have ha_δ : a⁻¹ * (A (j p.2))⁻¹ * ω a = δ := by simpa only [hm, hτ] using ha_conj
    have h_semi : a⁻¹ * j p.2 = ν * a⁻¹ := H.e_injective <| by
      -- `-map_inv` with `e.map_inv a`: of the inverses under `e`, only that of `a` is pulled out.
      simp [hν_def, ← ha_δ, H.map_apply_eq_galoisGf, H.twistedNorm_conj, -map_inv, e.map_inv a,
        map_twistedNorm e H.map_apply_eq_galoisGf, R.twistedNorm_inv H hp_good]
    obtain ⟨-, hA, hB⟩ := R.good_and_conj_of_semiconjBy _ hp_good h_semi
    obtain ⟨a', ha'_j⟩ : ∃ a' : U (1 : Matrix n n E), j a' = (a * g)⁻¹ :=
      H.exists_j_eq _ (by simp [hg, ← ha_δ, hA, mul_assoc])
    refine ⟨a', ⟨?_, H.j_injective ?_⟩, by simp [ha'_j]⟩
    · simpa only [mul_assoc, Subgroup.mem_comap, map_mul, map_inv, hy, hB, inv_inv,
        _root_.mul_inv_rev, ← H.map_apply_eq_baseChangeGf, ha'_j, mul_inv_cancel_left, hm] using
        inv_mem (mul_mem ha_mem hk)
    · simp [ha'_j, hγ, ← h_semi, mul_assoc]

end MatchingRoots

/-- Twisted trace identity for a step `E'/E` (`IsStep`) and `σ ≠ 1` in its Galois group. Let
`L ≤ K ≤ stdLevel E' n` with `L` open and `σ`-stable, and let every `s ∈ K` of twisted norm one be
`t * (σ t)⁻¹` with `t ∈ K` (`hK_split`). Then for some `c ≠ 0`, an operator `t` on forms of weight
`κ.baseChange` over `E'` (a) turns translation by `g` into that by `σ g`, (b) keeps `L`-fixed forms,
and (c) has `tr (T' * t) = c * tr T` for Hecke operators `T'`, `T` of a matching pair `(φ, f)`. -/
lemma New.twisted_trace_identity {E E' n : Type} [Field E] [CMType E] [Field E'] [Algebra E E']
    [Fintype n] [DecidableEq n] {σ : Gal(E'/E)} (hσ : σ ≠ 1) {μ : (𝔸f E)ˣ →* ℂˣ} [CMTypeOver E E']
    [IsStep (E := E) E' μ] (κ : Weight E) {K L : Subgroup (Gf E' n)} (hK : K ≤ stdLevel E' n)
    (hL : L ≤ K) (hL_open : L.IsOpen) (hL_σ : L.comap (galoisGf σ) = L)
    (hK_split : ∀ s ∈ K,
      twistedNorm (galoisGf σ) (finrank E E') s = 1 → ∃ t ∈ K, galoisGf σ t = s⁻¹ * t) :
    ∃ c ≠ (0 : ℂ), ∃ t : End ℂ ((stdSpace E' n).forms κ.baseChange),
      -- (a) the operator `t` on forms over `E'` turns translation by `g` into translation by `σ g`
      (∀ (g : Gf E' n) (ψ : (stdSpace E' n).forms κ.baseChange),
        t ((stdSpace E' n).formTranslation κ.baseChange g ψ) =
          (stdSpace E' n).formTranslation κ.baseChange (galoisGf σ g) (t ψ)) ∧
      -- (b) `ht`: `t` preserves the `L`-fixed forms
      ∃ ht : ∀ x ∈ levelSpace ((stdSpace E' n).formTranslation κ.baseChange) L,
        t x ∈ levelSpace ((stdSpace E' n).formTranslation κ.baseChange) L,
        -- (c) for a matching pair of functions, the twisted trace is `c` times the trace
        ∀ (f : Gf E n → ℂ) (φ : U (1 : Matrix n n (𝔸f E')) → ℂ),
        IsMatchingPair (adeleMap_star σ) (finrank E E') 1 (kerCompNorm E' μ) baseChangeGf K f φ →
        ∀ (T : End ℂ (levelSpace ((stdSpace E n).formTranslation κ) (L.comap baseChangeGf)))
          (T' : End ℂ (levelSpace ((stdSpace E' n).formTranslation κ.baseChange) L)),
          IsOperatorOf ((stdSpace E n).formTranslation κ) (L.comap baseChangeGf) T f →
          IsOperatorOf ((stdSpace E' n).formTranslation κ.baseChange) L T' φ →
          (T' * t.restrict ht).trace ℂ
              (levelSpace ((stdSpace E' n).formTranslation κ.baseChange) L) =
            c * T.trace ℂ
              (levelSpace ((stdSpace E n).formTranslation κ) (L.comap baseChangeGf)) := by
  -- Both traces are weighted sums of orbital terms (`isSampleTotal_twisted_trace`), over pairs
  -- `(y, γ)` for `E` and `(x, δ)` for `E'`. A rational `A ν` and an adelic `B ν`, built from the
  -- roots in `IsMatchingPair`, send `(y, γ)` to a pair `(B⁻¹ y, A⁻¹)` with the same term, `A⁻¹`
  -- having twisted norm `j γ`. By `hK_split` and the Hasse principle every non-zero term over `E'`
  -- is reached up to a move; `IsSampleTotal.mul_eq_mul_of_bijOn` counts the moves.
  have h_wt := exists_trace_mul_weightRep_eq_of_twistedNorm_eq (n := n) hσ κ
  extract_lets j ω ρ at h_wt
  obtain ⟨s, hs, h_wt⟩ := h_wt
  -- `s` intertwines `ρ δ` with `ρ (ω δ)` (`hs`), and `tr (s * ρ δ)` is the character of weight `κ`
  -- at `γ` when `δ` has twisted norm `j γ` (`h_wt`).
  let e : U (1 : Matrix n n E') →* Gf E' n :=
    U.map (algebraMap E' (𝔸f E')) (fun x : E' ↦ (star_algebraMap_finAdele x).symm)
      (map_one (algebraMap E' (𝔸f E')).mapMatrix)
  have h_emb : (stdSpace E' n).embFin = e :=
    MonoidHom.ext fun γ ↦ Subtype.ext (Units.ext (by
      change (((stdSpace E' n).ratEmbed γ).2 : Matrix n n (𝔸f E')) = _
      dsimp only [Space.ratEmbed, Space.toRatCoords, stdSpace, G.toUnitary,
        MonoidHom.comp_apply, MulEquiv.symm_trans_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_mk, Equiv.coe_fn_symm_mk]
      simp only [U.map, U.conj, inv_one, one_mul, mul_one]
      rfl))
  have h_maps : New.IsBaseChangeMaps σ j ω e := New.isBaseChangeMaps μ hσ
  -- The trace formula over `E` (untwisted) and over `E'` (twisted by `σ`, as an automorphism).
  let τ : U 1 ≃* U 1 := by
    apply ω.toMulEquiv (mapEnd (map_star_CM ↑σ⁻¹)) <;> ext <;> simp [ω, U.map]
  have hσ_l : ((σ⁻¹ : Gal(E'/E)) : E' →+* E').comp (σ : E' →+* E') = RingHom.id E' :=
    RingHom.ext fun x ↦ AlgEquiv.symm_apply_apply σ x
  have hσ_r : (σ : E' →+* E').comp ((σ⁻¹ : Gal(E'/E)) : E' →+* E') = RingHom.id E' :=
    RingHom.ext fun x ↦ AlgEquiv.apply_symm_apply σ x
  let θ : Gf E' n ≃* Gf E' n :=
    (galoisGf σ).toMulEquiv (galoisGf σ⁻¹)
      (MonoidHom.ext fun x ↦ Subtype.ext (Units.ext (Matrix.ext fun a b ↦
        (adeleMap_adeleMap _ _ _).trans (by rw [hσ_l, adeleMap_id]; rfl))))
      (MonoidHom.ext fun x ↦ Subtype.ext (Units.ext (Matrix.ext fun a b ↦
        (adeleMap_adeleMap _ _ _).trans (by rw [hσ_r, adeleMap_id]; rfl))))
  have hK_E : K.comap baseChangeGf ≤ stdLevel E n := fun _ h ↦ baseChangeGf_mem_stdLevel.1 (hK h)
  obtain ⟨c, hc, h_forms, h_level, h_tr⟩ :=
    (stdSpace E n).isSampleTotal_twisted_trace κ 1 continuous_id hK_E (L.comap_mono hL)
      (hL_open.preimage continuous_baseChangeGf) rfl 1 (fun _ ↦ rfl) 1
      (fun _ ↦ (one_mul _).trans (mul_one _).symm)
  have h_tr'_of := (stdSpace E' n).isSampleTotal_twisted_trace κ.baseChange θ
    (continuous_map : Continuous (galoisGf σ⁻¹)) hK hL hL_open hL_σ τ
  rw [h_emb] at h_tr'_of
  obtain ⟨c', hc', ht, ht', h_tr'⟩ := h_tr'_of h_maps.map_apply_eq_galoisGf s hs
  refine ⟨c' / c, div_ne_zero hc' hc,
    (s.compLeft (Gf E' n) ∘ₗ LinearMap.funLeft ℂ (WeylIndex n κ.baseChange.1 → ℂ) θ.symm).restrict
      ht, fun g ψ ↦ ?_, ht', fun f φ h_pair T T' hT hT' ↦ ?_⟩
  · -- The operator precomposes with `σ⁻¹`, which turns translation by `g` into that by `σ g`.
    ext x i
    change s ((ψ : Gf E' n → _) (θ.symm x * g)) i =
      s ((ψ : Gf E' n → _) (θ.symm (x * galoisGf σ g))) i
    rw [map_mul, show θ.symm (galoisGf σ g) = g from θ.symm_apply_apply g]
  rw [div_mul_eq_mul_div, eq_div_iff hc]
  obtain ⟨Good, A, B, h_roots : New.IsMatchingRoots σ K f φ j ω e Good A B⟩ :=
    New.exists_isMatchingRoots hσ h_pair h_maps
  -- `m` sends a pair over `E` to the pair over `E'` with the same term.
  let m (p : Gf E n × U (1 : Matrix n n E)) : Gf E' n × U (1 : Matrix n n E') :=
    ((B (j p.snd))⁻¹ * baseChangeGf p.fst, (A (j p.snd))⁻¹)
  let F (p : Gf E n × U 1) : ℂ := f (p.fst⁻¹ * (stdSpace E n).embFin p.snd * p.fst) *
    ((stdSpace E n).weightRep κ.1 κ.2 p.snd).trace ℂ _
  let F' (p : Gf E' n × U 1) : ℂ :=
    φ (p.fst⁻¹ * e p.snd * galoisGf σ p.fst) * (ρ p.snd * s).trace ℂ _
  refine IsSampleTotal.mul_eq_mul_of_bijOn (B := U 1) (F := F) F' (h_tr hT) (h_tr' hT') m
    {p | Good (j p.snd)} (fun p hp ↦ ?_) (fun p hp y g ⟨hk, hg⟩ ↦ ?_) fun (x, δ) hx ↦ ?_
  · -- A non-zero term over `E` has a good `j γ`.
    exact h_roots.good_of_apply_ne_zero p.fst p.snd (left_ne_zero_of_mul hp)
  · -- A move from `y` to `m p` keeps the value of `φ`, by twisted `K`-invariance, and the trace.
    have h_val : φ (y.fst⁻¹ * e y.snd * galoisGf σ y.fst) =
        f (p.fst⁻¹ * (stdSpace E n).embFin p.snd * p.fst) := by
      rw [h_roots.apply_inv_mul_embFin_mul_eq h_maps p.fst p.snd hp,
        ← h_roots.apply_inv_mul_mul_galoisGf _ hk ((m p).fst⁻¹ * _ * _)]
      simp only [← hg, MonoidHom.toMulEquiv_apply, mul_assoc, map_mul, map_inv,
        h_maps.map_apply_eq_galoisGf, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left,
        inv_mul_cancel_left, τ, m]
    have h_trace :
        (ρ y.snd * s).trace ℂ _ = ((stdSpace E n).weightRep κ.1 κ.2 p.snd).trace ℂ _ := by
      simp [m, τ, ← hg, ← h_wt _ _ (h_roots.twistedNorm_inv h_maps hp), ← hs,
        (ρ g⁻¹).trace_mul_comm, s.trace_mul_comm, ← ρ.map_mul g, mul_assoc]
    simp only [F, F', h_val, h_trace]
  -- A non-zero term `(x, δ)` over `E'` is reached from a pair over `E`.
  exact h_roots.exists_bijOn_of_ne_zero hK_split h_maps τ (fun _ ↦ rfl) m (fun _ ↦ rfl)
    (left_ne_zero_of_mul hx)

end TwistedTraceIdentity
