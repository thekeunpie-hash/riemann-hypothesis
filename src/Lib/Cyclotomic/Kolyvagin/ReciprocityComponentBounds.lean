module

import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.Algebra.Group.AddChar.Basic
public import Lib.GaloisRep.Main.SelmerModules
import Lib.Adelic.Adeles.LocalFactors
import Lib.ClassField.Global.AlbertBrauerHasseNoether
import Lib.General.NumberTheory.FrobeniusOrbits
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.Linter.Style
public import Lib.General.NumberTheory.ImaginaryQuadraticField
import Lib.ClassField.GreenbergWiles.SelmerLevels
import Lib.ClassField.Places.TameInertia
public import Lib.Cyclotomic.Voronoi
import Mathlib.RingTheory.ZMod.Torsion
import Lib.ClassField.Global.ArtinMap
import Lib.ClassField.Global.ArtinReciprocity
import Lib.ClassField.Global.Chebotarev
import Lib.ClassField.Global.ExistenceTheorem
import Lib.PadicComparison.Descent.TestCategory

section
/-!
# A weak form of Stickelberger's theorem for Gauss sums, and a family of Jacobi-type quotients

Gauss sums over `𝔽_p` give a family of elements `J x` of `Ωˣ`, `Ω = ℚ̄`, indexed by torsion points
`x` of `ℚ/ℤ`, with a known Galois action and a distribution relation up to elements of finite order.

* `New.OddPart.floorDiff`, `New.OddPart.sum_floorDiff`: the integer `⌊c ⟨x⟩⌋ - ⌊c ⟨-x⟩⌋` and its
  distribution relation (Hermite's identity).
* `New.OddPart.exists_galUnitsRep_gaussSum_eq`, `New.OddPart.stickelberger`: Galois action on Gauss
  sums, and their orders at a place `B` above `p`.
* `New.OddPart.exists_isJacobiFamily`: the family `J`, built from the quotients
  `j t = g(χ) ^ c / g(χ ^ c)` as `j t / j (-t)`.

Notions from other files:
* `Ω` is `ℚ̄`, and `DiscreteUnits Ω` is `Ωˣ` written additively: a sum is a product, `c • u` is
  `u ^ c`. `galUnitsRep σ` is the action of `σ ∈ Gal(Ω/ℚ)` on it.
* `ClosurePlace`: a valuation subring `B` of `Ω`; it lies above `p` when `B.valuation p < 1`, and
  `centerPrime Ω B` is the prime ideal of `𝓞 Ω` that it defines; `principalUnits B` is the subgroup
  of `DiscreteUnits Ω` of the `u` with `B.valuation (u - 1) < 1`, that is `u ≡ 1` at `B`.
* `ordRat ℚ B u`: the order of `u` at `B`, normalised so that a prime `p` below `B` has order one.
* `cyclotomicCharMod Ω N σ`: the cyclotomic character of `σ` modulo `N`, the unit `a` with
  `σ ζ = ζ ^ a` for every `N`-th root of unity `ζ`.
* `New.QZ`: the group `ℚ/ℤ`; `New.QZ.fracRep x = ⟨x⟩` is the representative in `[0, 1)`, and
  `New.QZ.ofZMod r b = b / r`.

## Relation to the literature

Known result: Stickelberger's factorisation of Gauss sums and the Davenport–Hasse product relation.
Here only prime fields are treated, and characters are named by the valuation of their Gauss sum.
The product relation is proved for Jacobi-type quotients of Gauss sums and only up to a root of
unity. Source: L. Washington, Introduction to Cyclotomic Fields, 2nd ed. 1997, 6.2 and Thm 15.1; for
the product relation, H. Davenport, H. Hasse, J. reine angew. Math. 172 (1935).
-/

@[expose] public section

namespace New.OddPart

open Int Finset NumberField IntermediateField AddChar MulChar AddMonoidHom QZ ZMod QuotientAddGroup
  HasEnoughRootsOfUnity Embeddings ComplexEmbedding ValuationSubring Cohomology NeZero Fact Ideal

variable {r m p : ℕ} [NeZero r] [hp : Fact p.Prime] {B : ClosurePlace}

/-- For `c : ℕ`, the integer `⌊c ⟨x⟩⌋ - ⌊c ⟨-x⟩⌋`, where `⟨x⟩` is the representative of `x ∈ ℚ/ℤ`
in `[0, 1)`. -/
noncomputable def floorDiff (c : ℕ) (x : QZ) : ℤ := ⌊c * x.fracRep⌋ - ⌊c * (-x).fracRep⌋

/-- The distribution relation for `floorDiff m`, with `m` prime to `r`: its sum over the translates
of `x` by the points `v b / r`, for a unit `v` mod `r`, is its value at `r • x`. -/
lemma sum_floorDiff (h_cop : m.Coprime r) (x : QZ) {v : ZMod r} (hv : IsUnit v) :
    ∑ b : ZMod r, floorDiff m (x + ofZMod r (v * b)) = floorDiff m (r • x) := by
  -- Hermite's identity: the representatives of `x + v b / r` in `[0, 1)` are, after the
  -- permutation `b ↦ ⌊r x⌋ + v b` of `ZMod r`, the numbers `(b + fract (r x)) / r`.
  have sum_lift (x : QZ) (v : ZMod r) (hv : IsUnit v) :
      ∑ b : ZMod r, QZ.fracRep (x + ofZMod r (v * b)) =
        ∑ b : ZMod r, (b.val + fract (r * x.fracRep)) / r := by
    refine Fintype.sum_equiv (hv.unit.mulLeft.trans (.addLeft ⌊r * x.fracRep⌋)) _ _ fun b ↦
      .trans ?_ (floor_add_fract _)
    -- Without the `↓` flags, or without `-natCast_val`, `simp` stops with `ZMod.lift` unevaluated.
    simp [← ofZMod_apply, -natCast_val, ofZMod, ← map_zsmul, add_assoc, ← div_eq_mul_inv, sub_div,
      ↓floor_div_natCast, ↓floor_natCast_add, ↓floor_fract, ediv_eq_zero_of_lt, val_lt,
      ← fracRep_mk, add_div, ← self_sub_fract, NeZero.ne]
  -- In `ℚ`, `⌊m ⟨y⟩⌋ = m ⟨y⟩ - ⟨m y⟩`, so `floorDiff m y = m ⟨y⟩ - ⟨m y⟩ - m ⟨-y⟩ + ⟨-(m y)⟩`.
  have hm : IsUnit (m : ZMod r) := (isUnit_iff_coprime m r).mpr h_cop
  qify
  simp [floorDiff, map_nsmul, ← nsmul_eq_mul, ← fracRep_mk, add_div, sum_add_distrib,
    ← self_sub_fract] at sum_lift ⊢
  -- Apply `sum_lift` to the four sums, with the units `v`, `m * v`, `-v`, `-(m * v)`; the constant
  -- `∑ b, b / r` occurs with the coefficients `m - 1 - m + 1 = 0`.
  simp [sum_lift, hm, hv, smul_comm r, ← map_neg, ← neg_mul, add_comm, mul_div_cancel₀, ← mul_sum,
    NeZero.ne, ← map_nsmul, ← mul_assoc]
  ring

/-- Kronecker's theorem in `Ω = ℚ̄`: an element of `Ω` that lies in every valuation ring of `Ω` and
has absolute value one in every complex embedding is a root of unity. -/
lemma isOfFinOrder_of_norm_eq_one {x : Ω} (h_mem : ∀ A : ClosurePlace, x ∈ A)
    (h_norm : ∀ τ : Ω →+* ℂ, ‖τ x‖ = 1) : IsOfFinOrder x := by
  -- Apply Mathlib's Kronecker theorem to the generator of the number field `ℚ⟮x⟯`.
  -- The integral closure of `ℤ` is the intersection of the valuation subrings.
  have h_int : IsIntegral ℤ x :=
    (integralClosure ℤ Ω).toSubring.eq_iInf_of_isIntegrallyClosedIn.ge (by simp [h_mem])
  have : NumberField ℚ⟮x⟯ := { to_finiteDimensional := adjoin.finiteDimensional h_int.tower_top }
  -- Every embedding of `ℚ⟮x⟯` into `ℂ` extends to `Ω`.
  have h_gen (φ : ℚ⟮x⟯ →+* ℂ) : ‖φ (AdjoinSimple.gen ℚ x)‖ = 1 := by
    rw [← lift_algebraMap_apply Ω φ]
    exact h_norm _
  obtain ⟨n, hn_pos, h_pow⟩ := pow_eq_one_of_norm_eq_one ℚ⟮x⟯ ℂ (coe_isIntegral_iff.mp h_int) h_gen
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn_pos, by simpa [Subtype.ext_iff] using h_pow⟩

/-! ### Gauss sums -/

/-- Galois action on Gauss sums. Let `ψ` be an additive character of `𝔽_p`, let `t ↦ χ t` be a
homomorphism from `ZMod r` to the multiplicative characters of `𝔽_p`, and let the unit `g t` of
`Ω` be the Gauss sum of `χ t` and `ψ`. There are homomorphisms `K σ : ZMod r → Ωˣ` with
`σ (g t) = K σ (a t) * g (a t)`, where `a` is the cyclotomic character of `σ` modulo `r`; in the
additive notation of `DiscreteUnits Ω` the right side is `(K σ + g) (a * t)`. -/
lemma exists_galUnitsRep_gaussSum_eq {ψ : AddChar (ZMod p) (𝓞 Ω)}
    {χ : AddChar (ZMod r) (MulChar (ZMod p) (𝓞 Ω))}
    (g : ZMod r → DiscreteUnits Ω) (hg : ∀ t : ZMod r, (g t).toMul.val = gaussSum (χ t) ψ) :
    ∃ K : Gal(Ω/ℚ) → ZMod r →+ DiscreteUnits Ω, ∀ (σ : Gal(Ω/ℚ)) (t : ZMod r),
      galUnitsRep σ (g t) = (K σ + g) (cyclotomicCharMod Ω r σ * t) := by
  -- With `c σ` the cyclotomic character of `σ` modulo `p`, the factor is `K σ t = (χ t)⁻¹ (c σ)`.
  let c : Gal(Ω/ℚ) →* (ZMod p)ˣ := cyclotomicCharMod Ω p
  have hK_ne (σ : Gal(Ω/ℚ)) (t : ZMod r) : (((χ t)⁻¹ (c σ) : 𝓞 Ω) : Ω) ≠ 0 := by
    simp [apply_eq_zero_iff]
  let K (σ : Gal(Ω/ℚ)) (t : ZMod r) : DiscreteUnits Ω := .ofNeZero ((χ t)⁻¹ (c σ) : 𝓞 Ω) (hK_ne σ t)
  have K_add (σ : Gal(Ω/ℚ)) (a b : ZMod r) : K σ (a + b) = K σ a + K σ b := by
    simp [K, DiscreteUnits.ext_iff, field, map_add_eq_mul]
  refine ⟨fun σ ↦ mk' (K σ) (K_add σ), fun σ t ↦ ?_⟩
  -- The values of `χ t` on units are `r`-th, those of `ψ` are `p`-th roots of unity. So `σ` turns
  -- `gaussSum (χ t) ψ` into the Gauss sum of `χ (cyclotomicCharMod Ω r σ * t)` and
  -- `ψ.mulShift (c σ)`.
  have h_shift (s : ZMod r) : ((gaussSum (χ s) (ψ.mulShift (c σ)) : 𝓞 Ω) : Ω) =
      (((χ s)⁻¹ (c σ) * gaussSum (χ s) ψ : 𝓞 Ω) : Ω) := by
    rw [gaussSum_mulShift_eq]
  simpa [K, c, DiscreteUnits.ext_iff, smul_eq_pow_cyclotomicCharMod (N := p),
    smul_eq_pow_cyclotomicCharMod (N := r), hg, gaussSum, sum_eq_add_sum_units, smul_sum,
    NeZero.ne, ← RingHom.map_pow, ← pow_apply_coe, ← map_nsmul_eq_pow, natCast_self]
    using h_shift (cyclotomicCharMod Ω r σ * t)

/-- Let `B` be a place of `Ω` above the prime `p`. An algebraic integer `x` with `x ^ p = 1` is
congruent to `1` modulo the prime ideal `centerPrime Ω B` of `𝓞 Ω` that `B` defines. -/
lemma mk_centrePrime_eq_one_of_pow_eq_one (hB : B.valuation p < 1) {x : 𝓞 Ω} (hx : x ^ p = 1) :
    ↑x = (1 : 𝓞 Ω ⧸ centerPrime Ω B) := by
  -- Otherwise the residue of `x` is a primitive `p`-th root of unity in a domain where `p = 0`.
  by_contra h_ne
  have h_prim : IsPrimitiveRoot (x : 𝓞 Ω ⧸ centerPrime Ω B) p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime (congrArg _ hx) h_ne)
  exact h_prim.neZero'.out (mk_ker.ge (mem_centerPrime.mpr hB))

/-- A weak form of Stickelberger's theorem for `𝔽_p`. Let `B` be a place of `Ω` above `p`, `ψ` a
primitive additive character of `ZMod p`, `r` prime to `p`, `t ↦ χ t` a primitive (so injective)
additive map from `ZMod r` to the multiplicative characters of `ZMod p`, and `g t` the Gauss sum of
`χ t` and `ψ`. Then some injective `S : ZMod r →+ ℚ/ℤ` has, for every `t`, representative
`(S t).fracRep` in `[0, 1)` equal to `ordRat ℚ B (g t)`, the order at `B` normalised so that `p` has
order `1`. Stickelberger's factorisation of Gauss sums computes these orders; here they are only
tied to `S`. -/
lemma stickelberger (hB : B.valuation p < 1) {ψ : AddChar (ZMod p) (𝓞 Ω)}
    {χ : AddChar (ZMod r) (MulChar (ZMod p) (𝓞 Ω))} (g : ZMod r → DiscreteUnits Ω)
    (hg : ∀ t : ZMod r, (g t).toMul.val = gaussSum (χ t) ψ) (hψ : ψ.IsPrimitive)
    (hχ : χ.IsPrimitive) (h_cop : p.Coprime r) :
    ∃ S : ZMod r →+ QZ, (⇑S).Injective ∧ ∀ t : ZMod r, (S t).fracRep = ordRat ℚ B (g t) := by
  -- `v` is the place of `ℚ` below `B`, and `p` has order one at `B`
  obtain ⟨v, hv, -, ord_p⟩ := exists_isPlaceOver_prime hB
  obtain ⟨K, hK⟩ := exists_galUnitsRep_gaussSum_eq g hg
  -- Inertia fixes the `r`-th roots of unity, so it multiplies `g t` by the character `K σ t` and
  -- fixes `g (a + b) / (g a * g b)`, whose order is therefore an integer.
  have ord_add (a b : ZMod r) : ∃ n : ℤ, ordRat ℚ B (g (a + b) - (g a + g b)) = n := by
    refine hv.exists_ordRat_eq_intCast (Γ := Gal(Ω/ℚ)) fun σ hσ ↦ ?_
    have hK_inert (s : ZMod r) : galUnitsRep σ (g s) = K σ s + g s := by
      simp [hK, cyclotomicCharMod_eq_one_of_mem_inertiaGroup hσ, h_cop.valuation_eq_one hB]
    simp only [map_sub, map_add, hK_inert]
    abel
  -- So the class of `ord (g t)` in `ℚ/ℤ` is additive in `t`.
  have S_add (a b : ZMod r) :
      QZ.mk (ordRat ℚ B (g (a + b))) = QZ.mk (ordRat ℚ B (g a)) + QZ.mk (ordRat ℚ B (g b)) := by
    obtain ⟨n, hn⟩ := ord_add a b
    rw [← map_add, ← map_add]
    exact eq_iff_sub_mem.mpr (AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp [← hn]⟩)
  let S : ZMod r →+ QZ := mk' (fun t ↦ QZ.mk (ordRat ℚ B (g t))) S_add
  -- The Gauss sum of `χ' ≠ 1` has positive order: `ψ' ≡ 1` at `B`, so it is `≡ ∑ x, χ' x = 0`.
  have ord_pos (u : DiscreteUnits Ω) {χ' : MulChar (ZMod p) (𝓞 Ω)} {ψ' : AddChar (ZMod p) (𝓞 Ω)}
      (hu : u.toMul.val = gaussSum χ' ψ') (hχ' : χ' ≠ 1) : 0 < ordRat ℚ B u := by
    have h_cen : gaussSum χ' ψ' - gaussSum χ' 1 ∈ centerPrime Ω B := by
      simp [gaussSum, mk_centrePrime_eq_one_of_pow_eq_one hB, ← Submodule.Quotient.mk_eq_zero]
    rw [gaussSum_one_right hχ', sub_zero, mem_centerPrime] at h_cen
    rw [lt_iff_le_and_ne, ne_comm, Ne, hv.ordRat_nonneg_iff, hv.ordRat_eq_zero_iff, hu]
    exact ⟨algebraMap_ringOfIntegers_mem B (gaussSum χ' ψ'), h_cen.ne⟩
  -- The order of `g t` lies in `[0, 1)`, so it is the representative of its class `S t`.
  have lift_S (t : ZMod r) : (S t).fracRep = ordRat ℚ B (g t) := by
    refine (toIcoMod_eq_self _).mpr ?_
    rw [zero_add]
    by_cases ht : χ t = 1
    · -- Here `g t = -1`.
      have hψ_ne : ψ ≠ 1 := by simpa using hψ one_ne_zero
      have ord_zero : ordRat ℚ B (g t) = 0 :=
        hv.ordRat_eq_zero_iff.mpr (by simp [hg, ht, gaussSum_one_left hψ_ne])
      simp [ord_zero]
    · -- `p / g t` is the Gauss sum of `(χ t)⁻¹` and `ψ⁻¹`, of positive order, and `ord p = 1`.
      have h_mul : ((gaussSum (χ t) ψ * gaussSum (χ t)⁻¹ ψ⁻¹ : 𝓞 Ω) : Ω) = p := by
        simp [gaussSum_mul_gaussSum_eq_card ht hψ]
      have h_quot : 0 < ordRat ℚ B (.ofNeZero p out - g t) :=
        ord_pos _ (ψ' := ψ⁻¹) (by simpa [field, ← hg] using h_mul.symm) (inv_ne_one.mpr ht)
      exact ⟨(ord_pos _ (hg t) ht).le, by simpa [ord_p] using h_quot⟩
  -- If `S t = 0` the order of `g t` is `0`, which forces `χ t = 1`, that is `t = 0`.
  refine ⟨S, (injective_iff_map_eq_zero S).mpr fun t ht ↦ ?_, lift_S⟩
  have ord_zero : ordRat ℚ B (g t) = 0 := by
    rw [← lift_S, ht, ← map_zero QZ.mk, fracRep_mk, fract_zero]
  by_contra ht_ne
  exact (ord_pos (g t) (hg t) (mt (hχ.zmod_char_eq_one_iff r t).mp ht_ne)).ne' ord_zero

/-- The distribution relation up to roots of unity. Let `Ω` be the algebraic closure of `ℚ`, let `B`
be a place of `Ω` above `p`, and let `J : ℚ/ℤ → Ωˣ` (written additively) satisfy the following on
the `M`-torsion: it is Galois equivariant (`σ (J x) = J (a • x)` when `σ` raises `M`-th roots of
unity to the power `a`), a unit at every place not above `p`, of order
`floorDiff c x = ⌊c⟨x⟩⌋ − ⌊c⟨−x⟩⌋` at `B` normalised on `ℚ` (where `⟨x⟩` is the representative of
`x` in `[0, 1)`), and of absolute value one in every complex embedding. Then for `M • x = 0`,
`r ∣ M` and `c` prime to `r`, the quotient `(∏ b mod r, J (x + b / r)) / J (r x)` is a root of
unity. -/
lemma isOfFinAddOrder_distribution (hB : B.valuation p < 1) {c M : ℕ} [NeZero M]
    {J : QZ → DiscreteUnits Ω}
    (h_gal : ∀ x : QZ, M • x = 0 → ∀ (σ : Gal(Ω/ℚ)) (a : ℕ),
      (cyclotomicCharMod Ω M σ).val = a → galUnitsRep σ (J x) = J (a • x))
    (h_unit : ∀ x : QZ, M • x = 0 → ∀ A : ClosurePlace, A.valuation p = 1 →
      A.valuation (J x).toMul.val = 1)
    (h_ord : ∀ x : QZ, M • x = 0 → ordRat ℚ B (J x) = floorDiff c x)
    (h_abs : ∀ x : QZ, M • x = 0 → ∀ τ : Ω →+* ℂ, ‖τ (J x).toMul.val‖ = 1) {x : QZ} (hx : M • x = 0)
    (hr : r ∣ M) (hc : c.Coprime r) :
    IsOfFinAddOrder (∑ b : ZMod r, J (x + ofZMod r b) - J (r • x)) := by
  obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = r * M' := hr
  -- `over_p`: all places of `Ω` above `p` lie over one place `v` of `ℚ`.
  obtain ⟨v, -, -, over_p⟩ := exists_rat_place_of_prime hp.out
  set Q : DiscreteUnits Ω := ∑ b : ZMod r, J (x + ofZMod r b) - J (r • x) with hQ
  -- By Kronecker's theorem it suffices to see integrality everywhere and absolute value one.
  refine Units.isOfFinOrder_val.mp (isOfFinOrder_of_norm_eq_one (fun A ↦ ?_) fun τ ↦ ?_)
  · obtain hA | hA : A.valuation p = 1 ∨ A.valuation p < 1 := (valuation_le_one A p).eq_or_lt
    · -- Off `p` every factor is a unit by `h_unit`, so the quotient has valuation one.
      have h_val_one : A.valuation (Q.toMul : Ω) = 1 := by
        simp [hQ, toMul_sub, toMul_sum, h_unit, hA, hx, smul_comm, ← map_nsmul, natCast_self]
      exact (valuation_le_one_iff A _).mp h_val_one.le
    · -- A place `A` above `p` is conjugate to `B`: `σ • A = B`. The conjugate quotient is the sum
      -- of `J (a x + a b / r)` minus `J (r a x)`; its order at `B` vanishes by `sum_floorDiff`.
      obtain ⟨σ, hσ⟩ := (over_p A hA).exists_smul Gal(Ω/ℚ) (over_p B hB)
      obtain ⟨a, ha⟩ : ∃ a : ℕ, (cyclotomicCharMod Ω (r * M') σ : ZMod (r * M')) = a :=
        ⟨_, (natCast_zmod_val _).symm⟩
      have ha_unit : IsUnit (a : ZMod r) := by
        rw [← ZMod.cast_natCast (dvd_mul_right r M'), ← ha]
        exact isUnit_cast_of_dvd (dvd_mul_right r M') _
      have h_ord_conj : ordRat ℚ B (galUnitsRep σ Q) =
          ↑(∑ b : ZMod r, floorDiff c (a • x + ofZMod r (a * b)) - floorDiff c (r • a • x)) := by
        simp [hQ, h_gal _ _ σ a ha, h_ord, hx, smul_comm (r * _), smul_comm r, ← map_nsmul,
          natCast_self, smul_add]
      refine ((over_p A hA).ordRat_nonneg_iff Q).mp (ge_of_eq ?_)
      rw [← (over_p A hA).ordRat_smul σ, hσ, h_ord_conj, sum_floorDiff hc _ ha_unit, sub_self,
        Int.cast_zero]
  · simp [hQ, toMul_sub, toMul_sum, h_abs, hx, smul_comm, ← map_nsmul, natCast_self]

/-- The properties of a family `J : ℚ/ℤ → Ωˣ` (written additively) of Jacobi-type quotients of
Gauss sums over `𝔽_p`, on the points `x` with `M • x = 0`. Here `B` is a place of `Ω` (above `p`
where the family is built), and `c` is the exponent in `g(χ) ^ c / g(χ ^ c)`. -/
structure IsJacobiFamily (p : ℕ) (B : ClosurePlace) (c M : ℕ) [NeZero M]
    (J : QZ → DiscreteUnits Ω) : Prop where
  /-- The distribution relation up to a root of unity: for `r ∣ M` prime to `c`, the quotient
  `(∏ b mod r, J (x + b / r)) / J (r • x)` has finite order. -/
  isOfFinAddOrder_sum_sub {x : QZ} (hx : M • x = 0) (r : ℕ) [NeZero r] (hr : r ∣ M)
    (hc : c.Coprime r) : IsOfFinAddOrder (∑ b : ZMod r, J (x + ofZMod r b) - J (r • x))
  /-- The Galois action: `σ (J x) = J (a • x)` if `σ` raises the `M`-th roots of unity to the
  power `a`. -/
  galUnitsRep_apply {x : QZ} (hx : M • x = 0) (σ : Gal(Ω/ℚ)) (a : ℕ)
    (ha : (cyclotomicCharMod Ω M σ).val = a) : galUnitsRep σ (J x) = J (a • x)
  /-- `J x` is a unit at every place not above `p`. -/
  valuation_eq_one {x : QZ} (hx : M • x = 0) (A : ClosurePlace) (hA : A.valuation p = 1) :
    A.valuation (J x).toMul.val = 1
  /-- The order of `J x` at `B` is `floorDiff c x`. -/
  ordRat_eq {x : QZ} (hx : M • x = 0) : ordRat ℚ B (J x) = floorDiff c x
  /-- For a prime `q ∣ p - 1` and `q • b = 0`, the quotient `J (x + b) / J x` is `≡ 1` at every
  place above `q`. -/
  sub_mem_principalUnits {x : QZ} (hx : M • x = 0) (q : ℕ) [Fact q.Prime] (A : ClosurePlace)
    (b : QZ) (hb : q • b = 0) (hq : q ∣ p - 1) (hA : A.valuation q < 1) :
    J (x + b) - J x ∈ principalUnits A

/-- A Gauss sum over `𝔽_p` of a multiplicative character `χ₀` and a primitive additive character
`ψ` divides `p` in `𝓞 Ω`. -/
lemma gaussSum_dvd_natCast_of_isPrimitive {ψ : AddChar (ZMod p) (𝓞 Ω)} (hψ : ψ.IsPrimitive)
    (χ₀ : MulChar (ZMod p) (𝓞 Ω)) :
    gaussSum χ₀ ψ ∣ p := by
  by_cases hχ₀ : χ₀ = 1
  · simp [hχ₀, gaussSum_one_left (show ψ ≠ 1 by simpa using hψ one_ne_zero)]
  · simpa using Dvd.intro _ (gaussSum_mul_gaussSum_eq_card hχ₀ hψ)

/-- Let `A` be a place of `Ω` not above `p`. A Gauss sum over `𝔽_p` of a multiplicative character
`χ₀` and a primitive additive character `ψ` has valuation one at `A`: it is integral and divides
`p`, which is a unit at `A`. -/
lemma valuation_gaussSum_eq_one_of_valuation_eq_one {A : ClosurePlace} (hA : A.valuation p = 1)
    {ψ : AddChar (ZMod p) (𝓞 Ω)} (hψ : ψ.IsPrimitive) (χ₀ : MulChar (ZMod p) (𝓞 Ω)) :
    A.valuation ((gaussSum χ₀ ψ : 𝓞 Ω) : Ω) = 1 := by
  have h_le : A.valuation ((gaussSum χ₀ ψ : 𝓞 Ω) : Ω) ≤ 1 :=
    A.valuation_le_one ⟨_, algebraMap_ringOfIntegers_mem A (gaussSum χ₀ ψ)⟩
  refine h_le.eq_of_not_lt fun h_lt ↦ hA.not_lt ?_
  exact mem_centerPrime.mp (mem_of_dvd _ (gaussSum_dvd_natCast_of_isPrimitive hψ χ₀)
    (mem_centerPrime.mpr h_lt))

/-- An injective homomorphism `S : ℤ/r → ℚ/ℤ` maps the `m`-torsion onto the `m`-torsion, for
`m ∣ r`. -/
lemma exists_apply_eq_and_nsmul_eq_zero_of_injective {S : ZMod r →+ QZ} (hS : (⇑S).Injective)
    {x : QZ} (hx : m • x = 0) (h_dvd : m ∣ r) : ∃ t : ZMod r, S t = x ∧ m • t = 0 := by
  -- `S = ofZMod r ∘ f` with `f` injective, hence bijective; so `S` hits all the `r`-torsion.
  obtain ⟨f, rfl⟩ : ∃ f : ZMod r →+ ZMod r, (ofZMod r).comp f = S :=
    (bijective_ofZMod_comp (by simp [natCast_self])).surjective S
  obtain ⟨b, rfl⟩ : ∃ b : ZMod r, ofZMod r b = x :=
    exists_ofZMod (Submodule.torsionBy_le_torsionBy_of_dvd m r h_dvd hx)
  obtain ⟨t, rfl⟩ : ∃ t : ZMod r, f t = b :=
    (hS.of_comp (f := ofZMod r)).bijective_of_finite.surjective b
  exact ⟨t, rfl, hS (by rwa [map_nsmul, map_zero])⟩

/-- For a prime `p`, there are a primitive additive character `ψ` of `𝔽_p` and a primitive (so
injective) homomorphism `χ` from `ZMod (p - 1)` to the multiplicative characters of `𝔽_p`, both with
values in `𝓞 Ω`. -/
lemma exists_addChar_isPrimitive_and_mulChar_isPrimitive :
    ∃ (ψ : AddChar (ZMod p) (𝓞 Ω)) (χ : AddChar (ZMod p.pred) (MulChar (ZMod p) (𝓞 Ω))),
      ψ.IsPrimitive ∧ χ.IsPrimitive := by
  have hn_ne : NeZero p.pred := of_pos hp.out.pred_pos
  have root (m : ℕ) [NeZero m] : ∃ ζ : 𝓞 Ω, IsPrimitiveRoot ζ m :=
    ⟨_, (exists_isPrimitiveRoot Ω m).choose_spec.toInteger_isPrimitiveRoot⟩
  obtain ⟨ζp, hζp⟩ := root p
  obtain ⟨ζn, hζn⟩ := root p.pred
  -- `χ` sends `1` to a character `χ₀` of order `p - 1`, a generator of the dual of `𝔽_pˣ`.
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : MulChar (ZMod p) (𝓞 Ω), orderOf χ₀ = p.pred :=
    exists_mulChar_orderOf (ZMod p) (by simp) hζn
  exact ⟨_, _, zmodChar_primitive_of_primitive_root p hζp,
    zmodChar_primitive_of_primitive_root p.pred (IsPrimitiveRoot.iff_orderOf.mpr hχ₀)⟩

/-- Let `A` be a place of `Ω` above a prime `q`, let `ψ` be an additive character of `𝔽_p` and
`t ↦ χ t` a homomorphism from `ZMod n` to the multiplicative characters of `𝔽_p`. If `q • u = 0`,
the Gauss sums of `χ (w + u)` and of `χ w` with `ψ` are congruent modulo the prime ideal
`centerPrime Ω A`: the values of `χ u` on units are `q`-th roots of unity, so `≡ 1` at `A`. -/
lemma gaussSum_add_sub_gaussSum_mem_centrePrime_of_nsmul_eq_zero {n q : ℕ} [Fact q.Prime]
    {A : ClosurePlace} (hA : A.valuation q < 1) (ψ : AddChar (ZMod p) (𝓞 Ω))
    (χ : AddChar (ZMod n) (MulChar (ZMod p) (𝓞 Ω))) (w u : ZMod n) (hu : q • u = 0) :
    gaussSum (χ (w + u)) ψ - gaussSum (χ w) ψ ∈ centerPrime Ω A := by
  simp [gaussSum, mk_centrePrime_eq_one_of_pow_eq_one hA, hu, sum_eq_add_sum_units,
    map_add_eq_mul, ← Submodule.Quotient.mk_eq_zero, ← pow_apply_coe, ← map_nsmul_eq_pow]

/-- Let `B` be a place of `Ω` above the prime `p` and let `c : ℕ`. There is a family `J : ℚ/ℤ → Ωˣ`
(written additively) such that, for every `M` with `p ≡ 1` mod `M`, its values at the points `x`
with `M • x = 0` have the properties `New.OddPart.IsJacobiFamily`. It is built from the Jacobi-type
quotients `j t = g(χ) ^ c / g(χ ^ c)` of Gauss sums over `𝔽_p` (`χ` the character of index `t`): at
the point `x` of index `t` it is `j t / j (-t)`.

Such quotients of Gauss sums are used to prove Stickelberger's theorem on annihilators of class
groups of cyclotomic fields; no class group appears in the statement. -/
lemma exists_isJacobiFamily (hB : B.valuation p < 1) (c : ℕ) :
    ∃ J : QZ → DiscreteUnits Ω,
      ∀ (M : ℕ) [NeZero M], p ≡ 1 [MOD M] → IsJacobiFamily p B c M J := by
  -- Let `G t` be the Gauss sum of `χ t = χ₀ ^ t`, for a generator `χ₀` of the dual of `𝔽_pˣ`. By
  -- `stickelberger`, `S t = ord (G t)` identifies `ZMod (p - 1)` with the `(p - 1)`-torsion of
  -- `ℚ/ℤ`. Put `j t = G t ^ c / G (c t)` and `J (S t) = j t / j (-t)`.
  let n : ℕ := p.pred
  have hn_ne : NeZero n := of_pos hp.out.pred_pos
  have h_cop : p.Coprime n := by simp [n, hp.out.one_le]
  obtain ⟨ψ, χ, hψ, hχ⟩ := exists_addChar_isPrimitive_and_mulChar_isPrimitive (p := p)
  -- Gauss sums divide `p`, so they are non-zero.
  have gauss_ne (t : ZMod n) : ((gaussSum (χ t) ψ : 𝓞 Ω) : Ω) ≠ 0 :=
    RingOfIntegers.ext.mt (ne_zero_of_dvd_ne_zero out
      (gaussSum_dvd_natCast_of_isPrimitive hψ (χ t)))
  let G (t : ZMod n) : DiscreteUnits Ω := .ofNeZero (gaussSum (χ t) ψ : 𝓞 Ω) (gauss_ne t)
  have hG (t : ZMod n) : (G t).toMul.val = gaussSum (χ t) ψ := rfl
  obtain ⟨K, hK⟩ := exists_galUnitsRep_gaussSum_eq G hG
  obtain ⟨S, hS, lift_S⟩ := stickelberger hB G hG hψ hχ h_cop
  let j : ZMod n → DiscreteUnits Ω := c • G - G ∘ fun t : ZMod n ↦ c • t
  let J : QZ → DiscreteUnits Ω := (⇑S).extend (j - j ∘ fun t : ZMod n ↦ -t) 0
  have J_S (t : ZMod n) : J (S t) = j t - j (-t) := hS.extend_apply _ 0 t
  refine ⟨J, fun M _ hM ↦ ?_⟩
  have S_surj {x : QZ} (hx : M • x = 0) : ∃ t : ZMod n, S t = x ∧ M • t = 0 :=
    exists_apply_eq_and_nsmul_eq_zero_of_injective hS hx hM.symm.dvd'
  have h_gal (x : QZ) (hx : M • x = 0) (σ : Gal(Ω/ℚ)) (a : ℕ)
      (ha : (cyclotomicCharMod Ω M σ).val = a) : galUnitsRep σ (J x) = J (a • x) := by
    obtain ⟨t, rfl, ht⟩ := S_surj hx
    -- The factors `K σ` cancel in `j`, and `σ` acts on the index by `t ↦ a • t`. Test this on an
    -- injective `μ : ZMod n →+ DiscreteUnits Ω`, where `M • μ t = 0` as `M • t = 0`.
    let μ : ZMod n →+ DiscreteUnits Ω := (rootPowHom Ω n).val
    have hμ : Function.Injective μ := (rootPowHom Ω n).property.left
    have hμ_tors : M • μ t = 0 := by rw [← map_nsmul, ht, map_zero]
    have cyc_mul : (cyclotomicCharMod Ω n σ).val * t = a • t := hμ <| by
      rw [map_cyclotomicCharMod_mul, cyclotomicCharMod_eq_iff_unitsRep.mp ha hμ_tors, map_nsmul]
    -- Without `-nsmul_eq_mul`, `a • t` becomes `↑a * t` and `cyc_mul` no longer applies.
    simp [J_S, j, hK, cyc_mul, -nsmul_eq_mul, ← map_nsmul]
  have h_unit (x : QZ) (hx : M • x = 0) (A : ClosurePlace) (hA : A.valuation p = 1) :
      A.valuation (J x).toMul.val = 1 := by
    obtain ⟨t, rfl, -⟩ := S_surj hx
    simp [J_S, j, hG, valuation_gaussSum_eq_one_of_valuation_eq_one hA hψ]
  have h_ord (x : QZ) (hx : M • x = 0) : ordRat ℚ B (J x) = floorDiff c x := by
    obtain ⟨t, rfl, -⟩ := S_surj hx
    -- With `x = S t`, the order of `j t` is `c ⟨x⟩ - ⟨c x⟩ = ⌊c ⟨x⟩⌋`.
    simp [J_S, floorDiff, map_nsmul, ← nsmul_eq_mul, ← lift_S, j, ← self_sub_fract, ← fracRep_mk]
  have h_abs (x : QZ) (hx : M • x = 0) (τ : Ω →+* ℂ) : ‖τ (J x).toMul.val‖ = 1 := by
    obtain ⟨t, rfl, -⟩ := S_surj hx
    -- A complex conjugation `σ` for `τ` sends `j t` to `j (-t)`, so `τ (J x)` is `z / conj z`.
    obtain ⟨σ, hσ⟩ : ∃ σ : Gal(Ω/ℚ), ∀ z : Ω, τ (σ • z) = star τ z :=
      exists_apply_smul_eq_of_comp_algebraMap_eq Gal(Ω/ℚ) τ (star τ) (RingHom.ext_rat _ _)
    have j_neg : j (-t) = galUnitsRep σ (j t) := by
      simp [j, hK, IsComplexConj.cyclotomicCharMod_eq_neg_one ⟨τ, hσ⟩, ← map_nsmul]
    -- `AlgEquiv.smul_def` would hide the action `σ • z` that `hσ` rewrites.
    simp [J_S, j_neg, hσ, -AlgEquiv.smul_def]
  -- The distribution relation follows from these four properties; the congruence remains.
  refine
    { isOfFinAddOrder_sum_sub hx r := isOfFinAddOrder_distribution hB h_gal h_unit h_ord h_abs hx
      galUnitsRep_apply := h_gal _
      valuation_eq_one := h_unit _
      ordRat_eq := h_ord _
      sub_mem_principalUnits := fun hx q _ A b hb hq hA ↦ ?_ }
  obtain ⟨t, rfl, -⟩ := S_surj hx
  obtain ⟨s, rfl, hs⟩ := exists_apply_eq_and_nsmul_eq_zero_of_injective hS hb hq
  -- If `q • u = 0` the values of `χ u` on units are `q`-th roots of unity, `≡ 1` at `A`.
  -- So `G (w + u) ≡ G w`, and both are units at `A` as `q ≠ p`.
  have hA_p : A.valuation p = 1 := (h_cop.symm.of_dvd_left hq).valuation_eq_one hA
  have G_congr (w u : ZMod n) (hu : q • u = 0) :
      (G (w + u) : DiscreteUnits Ω ⧸ principalUnits A) = G w := by
    have h_val : valuationVia Ω A (gaussSum (χ (w + u)) ψ - gaussSum (χ w) ψ) < 1 :=
      mem_centerPrime.mp (gaussSum_add_sub_gaussSum_mem_centrePrime_of_nsmul_eq_zero hA ψ χ w u hu)
    refine eq_iff_sub_mem.mpr (show A.valuation (((G (w + u) - G w).toMul : Ω) - 1) < 1 from ?_)
    simpa [toMul_sub, valuationVia, div_sub_one, gauss_ne, map_div₀, hG,
      valuation_gaussSum_eq_one_of_valuation_eq_one hA_p hψ] using h_val
  have j_congr (w u : ZMod n) (hu : q • u = 0) :
      (j (w + u) : DiscreteUnits Ω ⧸ principalUnits A) = j w := by
    have hcu : q • c • u = 0 := by rw [smul_comm, hu, smul_zero]
    simp [-nsmul_eq_mul, j, G_congr w u hu, G_congr _ _ hcu]
  rw [← map_add, J_S, J_S, ← eq_iff_sub_mem, neg_add, QuotientAddGroup.mk_sub,
    QuotientAddGroup.mk_sub, j_congr t s hs, j_congr (-t) (-s) (by rw [smul_neg, hs, neg_zero])]

end New.OddPart
end
end

section
/-!
# Kolyvagin's derivative cocycles from Gauss sums, for one set of primes

The main result, `New.OddPart.exists_isKolyvaginSystem`, constructs Kolyvagin's cocycles `κ S` with
values in `O/lⁿ` from the Jacobi-type quotients `J` of `New.OddPart.exists_isJacobiFamily`. One
takes `lⁿ`-th roots `y` of `J`, forms the roots of unity `γ y / (g γ g⁻¹) y`, applies the derivative
operators at the primes of `S` and sums against `aᵉ ψ(a)`. The local properties are read modulo a
place, where roots of unity of order prime to it stay distinct.

* `New.OddPart.IsKolyvaginSystem`: the properties of the cocycles `κ S`.
* `New.OddPart.exists_isKolyvaginSystem`: a Kolyvagin system exists.
* `New.OddPart.derivativeSum`: the derivative operators followed by the character sum.

Conventions: `Ω = ℚ̄` is an algebraic closure of `ℚ`, and its places are valuation subrings
(`ClosurePlace`); `DiscreteUnits Ω` is `Ω^×` written additively, so `n • u` is `uⁿ`, and
`galUnitsRep g` is the action of `g` on it; `New.QZ.ofZMod M a` is `a/M` in `ℚ/ℤ`;
`QuotSpan (l ^ n : O)` is `O/lⁿ`; `floorDiff c x` is `⌊c ⟨x⟩⌋ - ⌊c ⟨-x⟩⌋`, where `⟨x⟩` is the
representative of `x` in `[0, 1)`.

Notions from other files:
* `New.OddPart.principalUnits B`: the units of `Ω` congruent to `1` modulo the maximal ideal of `B`,
  as an additive subgroup of `DiscreteUnits Ω`.
* `New.IsFrob B q σ`: `σ` stabilises `B`, and `σ x ≡ x ^ q` modulo the maximal ideal of `B` for
  every `x` in `B`; for `q = 1` this says that `σ` lies in the inertia group of `B`.
* `New.rootPowHom Ω m`: the map `ℤ/m → Ω^×`, `t ↦ ζᵗ`, for a fixed primitive `m`-th root of unity
  `ζ`; it is injective, and its image is the set of `m`-th roots of unity.
* `New.cyclotomicPowDirichlet l e ψ`: the character `cycᵉ ψ` of `Gal(ℚ̄/ℚ)` with values in `Oˣ`,
  where `cyc` is the `l`-adic cyclotomic character.

## Relation to the literature

Known result: Kolyvagin's derivative classes of the Euler system of Gauss sums. Here the classes
carry a Tate twist and a Dirichlet character and are cocycles over the rationals that vanish at one
fixed element. Their ramification, the relation between Frobenius and inertia, and the link between
the bottom class and the Stickelberger element are also covered. Source: K. Rubin, Kolyvagin's
system of Gauss sums, Arithmetic Algebraic Geometry (Texel 1989), Progr. Math. 89, 1991, 309-324;
with a Tate twist: G. Banaszak, W. Gajda, Euler systems for higher K-theory of number fields, J.
Number Theory 58 (1996).
-/

@[expose] public section

namespace New.OddPart

open QZ Finset MulAut Function ZMod NeZero DiscreteUnits Cohomology Representation Multiplicative
  Selmer

section

variable {O : Type} [CommRing O] {B : ClosurePlace} {g : Gal(Ω/ℚ)} {u : DiscreteUnits Ω}
  {m a M N l n e : ℕ} [NeZero m] [NeZero N] [Fact l.Prime] [Algebra ℤ_[l] O]
  {ψ : DirichletCharacter O N} [Algebra (ZMod (l ^ n)) (QuotSpan (l ^ n : O))]
  {L : ∀ q : Nat.Primes, (ZMod q)ˣ →* Multiplicative (ZMod (l ^ n))}
  {S : Finset Nat.Primes} {d f : Nat.Primes → ZMod (l ^ n)} {G G' : QZ → ZMod (l ^ n)}
  {γ : Gal(Ω/ℚ)} {q : Nat.Primes} {τ φ : Gal(Ω/ℚ)} {Y : ZMod q → DiscreteUnits Ω}
  {y : DiscreteUnits Ω} {v : (ZMod q)ˣ} {lg : (ZMod q)ˣ → ℤ}

private lemma mem_principalUnits_iff {x : DiscreteUnits Ω} :
    x ∈ principalUnits B ↔ B.valuation ((x.toMul : Ω) - 1) < 1 :=
  Iff.rfl

/-- Let `g` act as the `a`-th power modulo the maximal ideal of `B` (`IsFrob B a g`), and let
the `m`-th power of `u` be a unit at `B`, where `m ≠ 0`. Then `g u / uᵃ` is a principal unit at
`B`. -/
lemma _root_.New.IsFrob.sub_nsmul_mem_principalUnits (hg : IsFrob B a g)
    (hu : B.valuation ((m • u).toMul : Ω) = 1) :
    galUnitsRep g u - a • u ∈ principalUnits B := by
  -- `u` is a unit at `B`, so `g u / u ^ a - 1` has the valuation of `g u - u ^ a`.
  obtain ⟨-, hg_cong⟩ : g ∈ decompGroup Gal(Ω/ℚ) B ∧
      ∀ x : Ω, B.valuation x ≤ 1 → B.valuation (g • x - x ^ a) < 1 := hg
  have h_unit : B.valuation (u.toMul : Ω) = 1 := by simpa [NeZero.ne] using hu
  have h_cong : B.valuation (g • (u.toMul : Ω) - (u.toMul : Ω) ^ a) < 1 := hg_cong _ h_unit.le
  rw [mem_principalUnits_iff]
  simpa [div_sub_one, h_unit] using h_cong

/-- Roots of unity of order prime to the residue characteristic stay distinct modulo `B`. Let
`μ = New.rootPowHom Ω m` be the fixed map `t ↦ ζᵗ` from `ℤ/m` to `Ω^×`. If `m` is a unit at `B`
and `μ (a - b)` is a principal unit at `B`, then `a = b`. -/
lemma eq_of_mem_principalUnits {a b : ZMod m} (hm : B m = 1)
    (h_mem : (rootPowHom Ω m).val (a - b) ∈ principalUnits B) :
    a = b := by
  -- The image of `a - b` is an `m`-th root of unity congruent to one, and `m` is a unit at `B`.
  obtain ⟨μ_inj, μ_range⟩ : Injective (rootPowHom Ω m).val ∧
      ∀ y : DiscreteUnits Ω, y ∈ (rootPowHom Ω m).val.range ↔ m • y = 0 := (rootPowHom Ω m).prop
  have h_root : m • (rootPowHom Ω m).val (a - b) = 0 := (μ_range _).mp ⟨a - b, rfl⟩
  have h_pow : (((rootPowHom Ω m).val (a - b)).toMul : Ω) ^ m = 1 := by
    simpa using congr_arg (fun z : DiscreteUnits Ω ↦ (z.toMul : Ω)) h_root
  have h_eq_one : (((rootPowHom Ω m).val (a - b)).toMul : Ω) = 1 :=
    eq_of_val_sub_lt_one hm h_pow (one_pow m) (mem_principalUnits_iff.mp h_mem)
  exact sub_eq_zero.mp (μ_inj ((DiscreteUnits.ext h_eq_one).trans (map_zero _).symm))

/-- Let `M = m a` with `a` a unit at `B`. An element `g` of the inertia group of `B` that fixes
the `m`-th roots of unity fixes the `M`-th roots of unity. -/
lemma mem_cycloGalGroup_of_mem_inertiaGroup [NeZero M] (hg : g ∈ inertiaGroup Gal(Ω/ℚ) B)
    (ha : B a = 1) (hM : m * a = M) (hgm : g ∈ cycloGalGroup m) :
    g ∈ cycloGalGroup M := by
  -- `a • z` is an `m`-th root of unity, so it is a unit at `B` and `g` fixes it; as `a` is a unit
  -- at `B`, inertia then fixes its `a`-th root `z`.
  refine cyclotomicCharMod_eq_one_iff.mpr fun z hz ↦ DiscreteUnits.ext ?_
  have h_fix : galUnitsRep g (a • z) = a • z :=
    cyclotomicCharMod_eq_one_iff.mp hgm (a • z) (by rwa [smul_smul, hM])
  have h_fix_val : g • ((a • z).toMul : Ω) = (a • z).toMul := by rw [← val_unitsRep, h_fix]
  have h_unit : B.valuation ((a • z).toMul : Ω) = 1 := by
    simpa [NeZero.ne, ← hM] using congr_arg (fun w : DiscreteUnits Ω ↦ B w.toMul) hz
  rw [val_unitsRep]
  exact inertia_fixes_root_of_unit hg ha rfl h_unit h_fix_val

/-- If `B` lies above the prime `l` and `a` is prime to `l`, some element of the inertia group of
`B` in `Gal(Ω/ℚ)` has `l`-adic cyclotomic character `a`. -/
lemma exists_inertia_cyclotomicChar_eq (hB : B l < 1) (ha : l.Coprime a) :
    ∃ γ ∈ inertiaGroup Gal(Ω/ℚ) B, (cyclotomicChar Ω l γ).val = a := by
  -- `B` is pulled back from the integers of `ℚ̄_l` along an embedding `e`, and `res` restricts the
  -- local Galois group along `e`. It carries local inertia into inertia and keeps `cyclotomicChar`.
  obtain ⟨e, rfl⟩ := exists_comap_intQpBar_eq hB
  obtain ⟨res, h_res⟩ : ∃ res : Gp l →ₜ* Gal(Ω/ℚ), ∀ (g : Gp l) (x : Ω), e (res g • x) = g • e x :=
    exists_galois_restrict _ _ e fun g x ↦ by simp
  -- the local statement: `ℚ_l(μ_{l^∞})` is totally ramified
  have h_prime : ThePrime l := ThePrime.mk
  obtain ⟨g, hg_ine, hg_val⟩ := exists_inertia_cyclotomicGp_eq a ha
  exact ⟨res g, .map h_res hg_ine, by rwa [cyclotomicChar_eq_of_equivariant l (h_res g)]⟩

/-- If `g` raises the `(N m)`-th roots of unity to the power `a`, then on an element `x` of an
`O`-module with `m x = 0` the value `cyclotomicPowDirichlet l e ψ g` acts as the scalar
`aᵉ ψ(a)`. -/
lemma cyclotomicPowDirichlet_smul (hg : (cyclotomicCharMod Ω (N * m) g).val = a) {V : Type*}
    [AddCommGroup V] [Module O V] {x : V} (hx : m • x = 0) :
    (cyclotomicPowDirichlet l e ψ g).val • x = (a ^ e * ψ a) • x := by
  -- Up to a unit, `m` is a power of `l` in `ℤ_[l]`, and modulo that power the `l`-adic cyclotomic
  -- character of `g` is `a`.
  have hm_ne : (m : ℤ_[l]) ≠ 0 := NeZero.ne _
  have h_pow_dvd : (l : ℤ_[l]) ^ multiplicity l m ∣ (cyclotomicChar Ω l g).val - a :=
    (pow_dvd_cyclotomicChar_sub_iff _).mpr
      (cyclotomicCharMod_eq_of_dvd (.mul_left (pow_multiplicity_dvd l m) N) hg)
  have h_adic : (m : ℤ_[l]) ∣ (cyclotomicChar Ω l g).val - a :=
    (PadicInt.unitCoeff_spec hm_ne).dvd.trans (by simpa [PadicInt.valuation] using h_pow_dvd)
  obtain ⟨b, hb⟩ : (m : O) ∣ algebraMap ℤ_[l] O (cyclotomicChar Ω l g).val ^ e - a ^ e := by
    simpa using map_dvd (algebraMap ℤ_[l] O) (h_adic.trans (sub_dvd_pow_sub_pow _ _ e))
  have h_scalar : ((cyclotomicPowDirichlet l e ψ g : Oˣ) : O) =
      algebraMap ℤ_[l] O (cyclotomicChar Ω l g).val ^ e * ψ a := by
    simp [cyclotomicPowDirichlet, cyclotomicCharMod_eq_of_dvd (dvd_mul_right N m) hg]
  -- The two scalars differ by `ψ a * b * m`, and `m` kills `x`.
  rw [h_scalar]
  linear_combination (norm := module) ψ a • (hb • x + b • hx)

private lemma cyclotomicPowDirichlet_succ_smul
    (hg : (cyclotomicCharMod Ω (N * m) g).val = a) {V : Type*} [AddCommGroup V] [Module O V]
    {x : V} (hx : m • x = 0) :
    (cyclotomicPowDirichlet l (e + 1) ψ g).val • x =
      (cyclotomicPowDirichlet l e ψ g).val • a • x := by
  have hax : m • a • x = 0 := by rw [smul_comm m a, hx, smul_zero]
  rw [cyclotomicPowDirichlet_smul hg hx, cyclotomicPowDirichlet_smul hg hax]
  module

/-- Discrete logarithm: for a prime `q ≡ 1 mod k` there is a homomorphism `L` from `(ℤ/q)ˣ` to
`ℤ/k` (written multiplicatively) that sends some unit `g` to `1`, so `L` is onto. -/
lemma exists_monoidHom_units_zmod_eq_ofAdd_one {q : Nat.Primes} {k : ℕ} (hq : q ≡ 1 [MOD k]) :
    ∃ L : (ZMod q)ˣ →* Multiplicative (ZMod k), ∃ g : (ZMod q)ˣ, L g = ofAdd 1 := by
  obtain ⟨g, gen⟩ := (isCyclic_units_prime q.prop).exists_zpow_surjective
  have h_gen (x : (ZMod q)ˣ) : x ∈ Subgroup.zpowers g := Subgroup.mem_zpowers_iff.mpr (gen x)
  -- `1` has order `k` in `ℤ/k`, and `k` divides `q - 1`, the order of `g`.
  have h_order : orderOf (ofAdd (1 : ZMod k)) ∣ orderOf g := by
    simp [orderOf_eq_card_of_forall_mem_zpowers h_gen, Nat.totient_prime q.prop, hq.symm.dvd']
  exact ⟨monoidHomOfForallMemZpowers h_gen h_order, g,
    monoidHomOfForallMemZpowers_apply_gen h_gen h_order⟩

/-- An `m`-th root of unity `u` of `Ω` is moved alike by `γ` and by its conjugate `g γ g⁻¹`. -/
lemma galUnitsRep_conj_of_nsmul_eq_zero (γ g : Gal(Ω/ℚ)) {u : DiscreteUnits Ω} (hu : m • u = 0) :
    galUnitsRep γ u = galUnitsRep (g * γ * g⁻¹) u := by
  have h_ker : γ⁻¹ * conj g γ ∈ cycloGalGroup m := by simp [mul_comm]
  have h_fix : galUnitsRep (γ⁻¹ * conj g γ) u = u := cyclotomicCharMod_eq_one_iff.mp h_ker u hu
  calc galUnitsRep γ u = galUnitsRep γ (galUnitsRep (γ⁻¹ * conj g γ) u) := by rw [h_fix]
    _ = galUnitsRep (g * γ * g⁻¹) u := by simp

section Derivative

variable (ψ e L S d) in
/-- Kolyvagin's derivative followed by the character sum, with values in `O/lⁿ`
(`QuotSpan (l ^ n : O)`). For each `q ∈ S`, a function on `ℚ/ℤ` is translated by `u/q` with weight
`L q u - d q` and summed over the units `u` mod `q`; the values of the result at `a / N lⁿ` are
then summed against `aᵉ ψ(a)` over the units `a` mod `N lⁿ`. -/
noncomputable def derivativeSum : (QZ → ZMod (l ^ n)) →ₗ[ZMod (l ^ n)] QuotSpan (l ^ n : O) :=
  (∑ a : (ZMod (N * l ^ n))ˣ,
      LinearMap.smulRight
        ((a : ZMod (N * l ^ n)).val ^ e • LinearMap.proj (ofZMod (N * l ^ n) a))
        (ψ (a : ZMod (N * l ^ n)).val : QuotSpan (l ^ n : O))) ∘ₗ
    asAlgebraHom (ofDistribMulAction (ZMod (l ^ n)) (Multiplicative QZ)ᵈᵐᵃ (QZ → ZMod (l ^ n)))
      (∏ q ∈ S, ∑ u : (ZMod q)ˣ,
        MonoidAlgebra.single (DomMulAct.mk (ofAdd (ofZMod q u))) ((L q u).toAdd - d q))

omit [Algebra ℤ_[l] O] in
/-- With no primes, `derivativeSum` is the character sum: the value of `G` at `a / N lⁿ` is summed
against `aᵉ ψ(a)` over the units `a` mod `N lⁿ`. -/
lemma derivativeSum_empty :
    derivativeSum e ψ L ∅ d G = ∑ a : (ZMod (N * l ^ n))ˣ,
      (((a : ZMod (N * l ^ n)).val ^ e : ℕ) * G (ofZMod (N * l ^ n) a)) •
        (ψ (a : ZMod (N * l ^ n)).val : QuotSpan (l ^ n : O)) := by
  simp [derivativeSum]

omit [Algebra ℤ_[l] O] in
/-- Adding a prime `q` to `S` applies the derivative at `q` first. -/
lemma derivativeSum_insert {q : Nat.Primes} (hq : q ∉ S) :
    derivativeSum e ψ L (insert q S) d G =
      derivativeSum e ψ L S d fun x : QZ ↦
        ∑ u : (ZMod q)ˣ, ((L q u).toAdd - d q) * G (x + ofZMod q u) := by
  -- `MonoidAlgebra.single_sub` would split the weights before the sums are matched.
  simp [derivativeSum, hq, mul_comm _ (S.prod _), sum_fn, DomMulAct.smul_apply, add_comm,
    -MonoidAlgebra.single_sub]

/-- Substituting `a u` for `u` in all the sums. Here `derivativeSum e ψ L S d G ∈ O/lⁿ` applies
Kolyvagin's derivative to `G : ℚ/ℤ → ZMod (lⁿ)`: for each `q ∈ S`, `G` is translated by `u/q` with
weight `L q u - d q` and summed over the units `u` mod `q`, and the values of the result at
`b / N lⁿ` are then summed against `bᵉ ψ(b)` over the units `b` mod `N lⁿ`. Let `M` be a multiple of
`N lⁿ` and of the primes of `S`, and let `a` be the cyclotomic character of `g` mod `N lⁿ`; if
`G x = G' (a x)` on the `M`-torsion of `ℚ/ℤ`, and `f q = L q v + d q` with `v ≡ a` mod `q` for each
`q ∈ S`, then `cycᵉ ψ (g)` (`cyclotomicPowDirichlet l e ψ g`) times `derivativeSum … d G` is
`derivativeSum … f G'`. -/
lemma cyclotomicPowDirichlet_smul_derivativeSum (hM : N * l ^ n ∣ M) (hS : ∀ q ∈ S, (q : ℕ) ∣ M)
    (hg : (cyclotomicCharMod Ω (N * l ^ n) g : ZMod (N * l ^ n)) = a)
    (hf : ∀ q ∈ S, ∃ v : (ZMod q)ˣ, f q = (L q v).toAdd + d q ∧ (v : ZMod q) = a)
    (hG : ∀ {x : QZ}, M • x = 0 → G x = G' (a • x)) :
    (cyclotomicPowDirichlet l e ψ g : O) • derivativeSum e ψ L S d G =
      derivativeSum e ψ L S f G' := by
  have killed {x : QuotSpan (l ^ n : O)} : l ^ n • x = 0 := nsmul_quot_eq_zero dvd_rfl x
  induction S using Finset.induction generalizing G G' with
  | empty =>
    -- Substitute `χ u` for `u` in the character sum, where `χ` is the character of `g` mod `N lⁿ`.
    have base_zero : (M : ZMod (N * l ^ n)) = 0 := (natCast_eq_zero_iff M (N * l ^ n)).mpr hM
    rw [derivativeSum_empty, derivativeSum_empty, smul_sum]
    refine Fintype.sum_equiv (.mulLeft (cyclotomicCharMod Ω (N * l ^ n) g)) _ _ fun u ↦ ?_
    -- Both terms become products in `O/lⁿ`, equal by `ring`.
    simp [cyclotomicPowDirichlet_smul hg killed, base_zero, Algebra.smul_def, ← map_nsmul, hG, hg]
    ring
  | insert q S hq ih =>
    obtain ⟨hqM, hS⟩ := (forall_mem_insert q S _).mp hS
    obtain ⟨⟨v, hv_shift, hv⟩, hf⟩ := (forall_mem_insert q S _).mp hf
    have q_zero : (M : ZMod q) = 0 := (natCast_eq_zero_iff M q).mpr hqM
    rw [derivativeSum_insert hq, derivativeSum_insert hq]
    -- Substitute `v u` for `u` in the sum at `q`.
    refine ih hS hf fun {x} hx ↦ sum_equiv (.mulLeft v) (fun u ↦ by simp) fun u _ ↦ ?_
    have h_tors : M • (x + ofZMod q u) = 0 := by simp [q_zero, ← map_nsmul, hx]
    have h_shift : (L q (v * u)).toAdd - f q = (L q u).toAdd - d q := by simp [hv_shift]
    have h_arg : a • (x + ofZMod q u) = a • x + ofZMod q (v * u : (ZMod q)ˣ) := by
      simp [← map_nsmul, hv]
    change ((L q u).toAdd - d q) * G (x + ofZMod q u) =
      ((L q (v * u)).toAdd - f q) * G' (a • x + ofZMod q (v * u : (ZMod q)ˣ))
    rw [hG h_tors, h_arg, h_shift]

/-- The case of a prime `r ≡ 1 mod N lⁿ` outside `S`, where `rᵉ ψ(r) = 1` in `O/lⁿ`. Let `M` be
a multiple of `N lⁿ` and of the primes of `S`. If `G x = G' (r x)` on the `M`-torsion of `ℚ/ℤ`,
then `derivativeSum` takes the same value on `d, G` as on `f, G'`, where `f q = L q r' + d q` for
the unit `r'` of `ℤ/q` that `r` gives. -/
lemma derivativeSum_eq_of_prime (hM : N * l ^ n ∣ M) (hS : ∀ q ∈ S, (q : ℕ) ∣ M) {r : Nat.Primes}
    (hr : r ≡ 1 [MOD N * l ^ n]) (hrS : r ∉ S)
    (hG : ∀ {x : QZ}, M • x = 0 → G x = G' ((r : ℕ) • x)) :
    derivativeSum e ψ L S d G =
      derivativeSum e ψ L S
        (fun q : Nat.Primes ↦ (L q (invFun Units.val ((r : ℕ) : ZMod q))).toAdd + d q) G' := by
  have h_cyc_one : (cyclotomicCharMod Ω (N * l ^ n) (1 : Gal(Ω/ℚ)) : ZMod (N * l ^ n)) =
      (r : ℕ) := by
    simpa using (natCast_eq_natCast_iff 1 r (N * l ^ n)).mpr hr.symm
  have r_unit {q : Nat.Primes} (hq : q ∈ S) : IsUnit ((r : ℕ) : ZMod q) :=
    (CharP.cast_ne_zero_of_ne_of_prime (ZMod q) r.prop
      fun h_eq ↦ ne_of_mem_of_not_mem hq hrS (Subtype.ext h_eq)).isUnit
  -- `cyclotomicPowDirichlet l e ψ` is a homomorphism, so its value at `1` acts trivially.
  simpa using cyclotomicPowDirichlet_smul_derivativeSum (e := e) (ψ := ψ) (L := L) (d := d)
    (f := fun q : Nat.Primes ↦ (L q (invFun Units.val ((r : ℕ) : ZMod q))).toAdd + d q) hM hS
    h_cyc_one (fun q hq ↦ ⟨invFun Units.val _, rfl, invFun_eq (r_unit hq)⟩) hG

/-- `derivativeSum` reads only the shifts at the primes of `S` and the values on the
`M`-torsion of `ℚ/ℤ`, where `M` is a multiple of `N lⁿ` and of the primes of `S`. -/
lemma derivativeSum_congr (hM : N * l ^ n ∣ M) (hS : ∀ q ∈ S, (q : ℕ) ∣ M)
    (hf : ∀ q ∈ S, f q = d q) (hG : ∀ {x : QZ}, M • x = 0 → G x = G' x) :
    derivativeSum e ψ L S d G = derivativeSum e ψ L S f G' := by
  -- Take `g = 1` in `cyclotomicPowDirichlet_smul_derivativeSum`.
  have h_shift : ∀ q ∈ S, ∃ v : (ZMod q)ˣ, f q = (L q v).toAdd + d q ∧ (v : ZMod q) = (1 : ℕ) :=
    fun q hq ↦ ⟨1, by simp [hf q hq], by simp⟩
  simpa using cyclotomicPowDirichlet_smul_derivativeSum (g := 1) (a := 1) (e := e) (ψ := ψ) hM hS
    (by simp) h_shift (fun {x} hx ↦ by simpa using hG hx)

/-- Let `M` be a multiple of `N lⁿ`, let the natural number `a` represent the cyclotomic character
of `g ∈ Gal(ℚ̄/ℚ)` mod `N lⁿ`, and let `s : ℚ/ℤ → ℤ` and `G : ℚ/ℤ → ℤ/lⁿ` satisfy
`G x = a s(x) - s(a x)` on the `M`-torsion. Suppose that the character sum
`∑_u G(u / N lⁿ) uᵉ ψ(u)` of `G` (`derivativeSum` for no primes) vanishes in `O/lⁿ`
(`QuotSpan (l ^ n : O)`), where `u` runs over the units mod `N lⁿ`. Then `cycᵉ⁺¹ ψ (g) - 1`
(`cyclotomicPowDirichlet l (e + 1) ψ g - 1`) kills the character sum `∑_u s(u / N lⁿ) uᵉ ψ(u)` of
`s` in `O/lⁿ`. -/
lemma sub_one_smul_sum_eq_zero (hM : N * l ^ n ∣ M)
    (hg : (cyclotomicCharMod Ω (N * l ^ n) g : ZMod (N * l ^ n)) = a) {s : QZ → ℤ}
    (hG : ∀ {x : QZ}, M • x = 0 → a • (s x : ZMod (l ^ n)) - G x = s (a • x))
    (h_zero : derivativeSum e ψ L ∅ d G = 0) :
    (cyclotomicPowDirichlet l (e + 1) ψ g - 1 : O) •
        ((∑ u : (ZMod (N * l ^ n))ˣ, s (ofZMod (N * l ^ n) u) *
            ((u : ZMod (N * l ^ n)).val ^ e * ψ (u : ZMod (N * l ^ n)).val) : O) :
          QuotSpan (l ^ n : O)) =
      (0 : QuotSpan (l ^ n : O)) := by
  -- Let `Λ` be the character sum and `F` be `s` mod `lⁿ`. Equivariance gives
  -- `cycᵉ ψ (g) Λ (a F - G) = Λ F`, and the left side is `cycᵉ⁺¹ ψ (g) Λ F` since `Λ G = 0`.
  let F : QZ → ZMod (l ^ n) := fun x : QZ ↦ s x
  have killed {x : QuotSpan (l ^ n : O)} : l ^ n • x = 0 := nsmul_quot_eq_zero dvd_rfl x
  have h_sum : ((∑ u : (ZMod (N * l ^ n))ˣ, s (ofZMod (N * l ^ n) u) *
        ((u : ZMod (N * l ^ n)).val ^ e * ψ (u : ZMod (N * l ^ n)).val) : O) :
      QuotSpan (l ^ n : O)) = derivativeSum e ψ L ∅ d F := by
    rw [derivativeSum_empty, map_sum]
    refine sum_congr rfl fun u _ ↦ ?_
    simp only [F, Algebra.smul_def, map_mul, map_pow, map_natCast, map_intCast, Nat.cast_pow]
    ring
  have h_equiv : (cyclotomicPowDirichlet l e ψ g : O) • derivativeSum e ψ L ∅ d (a • F - G) =
      derivativeSum e ψ L ∅ d F :=
    cyclotomicPowDirichlet_smul_derivativeSum hM (by simp) hg (by simp) hG
  have h_sub : derivativeSum e ψ L ∅ d (a • F - G) = a • derivativeSum e ψ L ∅ d F := by
    rw [map_sub, map_nsmul, h_zero, sub_zero]
  rw [h_sum, sub_smul, one_smul, cyclotomicPowDirichlet_succ_smul hg killed,
    ← h_sub, h_equiv, sub_self]

end Derivative

section CommutatorLog

/-- The exponent `t` with `γ y / (g γ g⁻¹) y = ζᵗ`, for the fixed primitive `m`-th root of unity
`ζ` of `New.rootPowHom`, when this quotient is an `m`-th root of unity (otherwise some value that
is of no use). -/
noncomputable def commutatorLog (m : ℕ) [NeZero m] (γ : Gal(Ω/ℚ)) (y : DiscreteUnits Ω)
    (g : Gal(Ω/ℚ)) : ZMod m :=
  invFun (rootPowHom Ω m).val (galUnitsRep γ y - galUnitsRep (g * γ * g⁻¹) y)

/-- `commutatorLog m γ y g` is locally constant in `g`, since the orbit map `g ↦ (g γ g⁻¹) y` is. -/
lemma isLocallyConstant_commutatorLog : IsLocallyConstant (commutatorLog m γ y) := by
  -- The orbit map of `y` under the conjugates of `γ` is locally constant, read in `Ω`.
  have h_orbit_val : IsLocallyConstant fun g : Gal(Ω/ℚ) ↦ (g * γ * g⁻¹) • (y.toMul : Ω) :=
    (isLocallyConstant_smul (y.toMul : Ω)).comp_continuous (by fun_prop)
  have orbit : IsLocallyConstant fun g : Gal(Ω/ℚ) ↦ galUnitsRep (g * γ * g⁻¹) y :=
    .desc _ (fun z : DiscreteUnits Ω ↦ (z.toMul : Ω)) h_orbit_val fun _ _ ↦ DiscreteUnits.ext
  exact orbit.comp fun z : DiscreteUnits Ω ↦ invFun (rootPowHom Ω m).val (galUnitsRep γ y - z)

/-- The cocycle rule. Let `g` act on the `m`-th roots of unity by `a`, and let `g y / y'` be an
`m`-th root of unity. If `ζᵗ = γ y / (g' γ g'⁻¹) y`, `ζˢ = γ y' / (g g' γ (g g')⁻¹) y'` and
`ζ ^ s' = γ y' / (g γ g⁻¹) y'`, where `ζ ^ t` is `rootPowHom Ω m t`, then `a t = s - s'`. -/
lemma nsmul_exponent_eq_sub {g' : Gal(Ω/ℚ)} {y' : DiscreteUnits Ω} {t s s' : ZMod m}
    (hg : (cyclotomicCharMod Ω m g : ZMod m) = a) (hgy : m • (galUnitsRep g y - y') = 0)
    (ht : (rootPowHom Ω m).val t = galUnitsRep γ y - galUnitsRep (g' * γ * g'⁻¹) y)
    (hs : (rootPowHom Ω m).val s = galUnitsRep γ y' - galUnitsRep (g * g' * γ * (g * g')⁻¹) y')
    (hs' : (rootPowHom Ω m).val s' = galUnitsRep γ y' - galUnitsRep (g * γ * g⁻¹) y') :
    a • t = s - s' := by
  obtain ⟨μ_inj, μ_range⟩ : Injective (rootPowHom Ω m).val ∧
      ∀ z : DiscreteUnits Ω, z ∈ (rootPowHom Ω m).val.range ↔ m • z = 0 := (rootPowHom Ω m).prop
  -- `g` raises the `m`-th root of unity `ζᵗ` to the power `a`.
  have g_pow : galUnitsRep g ((rootPowHom Ω m).val t) = a • (rootPowHom Ω m).val t :=
    cyclotomicCharMod_eq_iff_unitsRep.mp hg ((μ_range _).mp ⟨t, rfl⟩)
  -- Apply `g` to `ζᵗ`; conjugates of `γ` act alike on the root of unity `g y / y'`.
  apply μ_inj
  show (rootPowHom Ω m).val (a • t) = (rootPowHom Ω m).val (s - s')
  linear_combination (norm := skip) galUnitsRep_conj_of_nsmul_eq_zero γ (g * g') hgy -
    galUnitsRep_conj_of_nsmul_eq_zero γ g hgy - g_pow
  -- `-nsmul_eq_mul` keeps `a •` outside `rootPowHom`, where `abel` can match it.
  simp [ht, hs, hs', -nsmul_eq_mul]
  abel

/-- Let `B` lie above the prime `q` and let `M` be a unit at `B`. For a unit `v` mod `q` there is
an element `τ` of the inertia group of `B` whose cyclotomic character mod `q M`, acting on `ℚ/ℤ`,
sends `x + v u / q` to `x + u / q` for every `x` in the `M`-torsion and every `u` mod `q`. -/
lemma exists_inertia_smul_add_ofZMod [NeZero M] {q : Nat.Primes} (hq : B.valuation (q : Ω) < 1)
    (hM : B.valuation M = 1) (v : (ZMod q)ˣ) :
    ∃ τ ∈ inertiaGroup Gal(Ω/ℚ) B, ∀ x : QZ, M • x = 0 → ∀ u : ZMod q,
      (cyclotomicCharMod Ω (q * M) τ : ZMod (q * M)).val • (x + ofZMod q (v * u)) =
        x + ofZMod q u := by
  -- Take `τ` with `cyc_q τ = v⁻¹`; it fixes the `M`-th roots of unity, as `M` is a unit at `B`.
  obtain ⟨τ, hτ, cyc_τ⟩ := exists_inertia_cyclotomicChar_eq hq (val_coe_unit_coprime v⁻¹).symm
  refine ⟨τ, hτ, fun x hx u ↦ ?_⟩
  obtain ⟨b, rfl⟩ := exists_ofZMod hx
  -- The character of `τ` is `1` mod `M` and `v⁻¹` mod `q`.
  have cyc_M : (cyclotomicCharMod Ω M τ : ZMod M) = (1 : ℕ) := hτ.cyclotomicCharMod_eq hM
  have cyc_mod_q : (cyclotomicCharMod Ω q τ : ZMod q) = ((v⁻¹ : (ZMod q)ˣ) : ZMod q).val :=
    cyclotomicCharMod_eq_of_dvd (dvd_pow_self (q : ℕ) one_ne_zero)
      ((pow_dvd_cyclotomicChar_sub_iff 1).mp (by simp only [cyc_τ, sub_self, dvd_zero]))
  -- Without `-inv_coe_unit` this `simp` call loops.
  simp [← map_nsmul, ← cyclotomicCharMod_eq_of_dvd _ (ZMod.natCast_zmod_val _).symm, cyc_M,
    cyc_mod_q, -inv_coe_unit]

end CommutatorLog

section Telescoping

/-- Let `τ` lie in the inertia group of `B` and let `φ` be a `q`-Frobenius at `B`. Let the `Y b`,
for `b` mod `q`, have `m`-th powers that are units at `B` and congruent to each other modulo `B`,
and let `lg (v u) ≡ lg u + 1 mod m` for the units `u` mod `q`. Then
`∏_b Y b / φ (Y 0) · ∏_u (τ Y(v u) / Y u) ^ lg u` is a principal unit at `B`. -/
lemma telescoping_mem_principalUnits (hτ : IsFrob B 1 τ) (hφ : IsFrob B q φ)
    (h_unit : ∀ b : ZMod q, B.valuation ((m • Y b).toMul : Ω) = 1)
    (h_cong : ∀ b : ZMod q, m • (Y b - Y 0) ∈ principalUnits B)
    (hlg : ∀ u : (ZMod q)ˣ, (m : ℤ) ∣ lg (v * u) - lg u - 1) :
    ∑ b : ZMod q, Y b - galUnitsRep φ (Y 0) +
        ∑ u : (ZMod q)ˣ, lg u • (galUnitsRep τ (Y (v * u)) - Y u) ∈
      principalUnits B := by
  -- Modulo `B`, `τ` acts trivially on units and `φ` as the `q`-th power; the sum over `u`
  -- telescopes.
  have h_quot : ∀ u : (ZMod q)ˣ, ∃ k : ℤ, lg (v * u) - lg u - 1 = m * k := hlg
  choose k hk using h_quot
  have inertia (b : ZMod q) : galUnitsRep τ (Y b) - 1 • Y b ∈ principalUnits B :=
    hτ.sub_nsmul_mem_principalUnits (h_unit b)
  have frobenius : galUnitsRep φ (Y 0) - (q : ℕ) • Y 0 ∈ principalUnits B :=
    hφ.sub_nsmul_mem_principalUnits (h_unit 0)
  have h_mem : ∑ u : (ZMod q)ˣ, (lg u • (galUnitsRep τ (Y (v * u)) - 1 • Y (v * u)) -
      k u • m • (Y (v * u) - Y 0)) - (galUnitsRep φ (Y 0) - (q : ℕ) • Y 0) ∈ principalUnits B :=
    sub_mem (sum_mem fun u _ ↦
      sub_mem (zsmul_mem (inertia (v * u)) (lg u)) (zsmul_mem (h_cong (v * u)) (k u))) frobenius
  -- Reindex the sum by `u ↦ v u`; the exponents telescope by `hk`.
  have h_eq : ∑ b : ZMod q, Y b - galUnitsRep φ (Y 0) +
        ∑ u : (ZMod q)ˣ, lg u • (galUnitsRep τ (Y (v * u)) - Y u) =
      ∑ u : (ZMod q)ˣ, (lg u • (galUnitsRep τ (Y (v * u)) - 1 • Y (v * u)) -
        k u • m • (Y (v * u) - Y 0)) - (galUnitsRep φ (Y 0) - (q : ℕ) • Y 0) := by
    simp_rw [← natCast_zsmul, ← mul_zsmul', ← hk]
    linear_combination (norm := skip) Equiv.sum_comp (.mulLeft v) fun u ↦ lg u • (Y u - Y 0) - Y u
    simp [sub_smul, smul_sub, sub_nsmul, q.prop.one_le, Nat.totient_prime q.prop,
      sum_eq_add_sum_units]
    abel
  rw [h_eq]
  exact h_mem

open Pointwise in
/-- The congruence behind the relation between Frobenius and inertia. Let `B` lie above `q`, let `τ`
lie in its inertia group, let `φ` be a `q`-Frobenius at `B`, and let `γ ∈ Gal(Ω/ℚ)` and `y ∈ Ωˣ`.
Let `Y : ℤ/q → Ωˣ` be such that at every place above `q`, `Y bᵐ` is a unit and `(Y b / Y 0)ᵐ` is a
principal unit. Let `v` be a unit mod `q` and `lg` satisfy `lg (v u) ≡ lg u + 1 mod m`. Suppose
`φ (Y 0) / y` and `τ Y(v u) / Y u` are `m`-th roots of unity, and `(∏_b Y b / y)ᵐ` is a root of
unity. Then `∏_u (γ Y u / τγτ⁻¹ Y u) ^ lg u ≡ γ y / φγφ⁻¹ y` modulo `B`, i.e. their quotient is a
principal unit at `B`. -/
lemma derivative_sub_frob_mem_principalUnits (γ : Gal(Ω/ℚ)) (hq : B.valuation (q : Ω) < 1)
    (hτ : IsFrob B 1 τ) (hφ : IsFrob B q φ)
    (h_unit : ∀ A : ClosurePlace, A.valuation (q : Ω) < 1 →
      ∀ b : ZMod q, A.valuation ((m • Y b).toMul : Ω) = 1)
    (h_cong : ∀ A : ClosurePlace, A.valuation (q : Ω) < 1 →
      ∀ b : ZMod q, m • (Y b - Y 0) ∈ principalUnits A)
    (hlg : ∀ u : (ZMod q)ˣ, (m : ℤ) ∣ lg (v * u) - lg u - 1)
    (hφY : m • (galUnitsRep φ (Y 0) - y) = 0)
    (hτY : ∀ u : ZMod q, m • (galUnitsRep τ (Y (v * u)) - Y u) = 0)
    (h_dist : IsOfFinAddOrder (m • (∑ b : ZMod q, Y b - y))) :
    ∑ u : (ZMod q)ˣ, lg u • (galUnitsRep γ (Y u) - galUnitsRep (τ * γ * τ⁻¹) (Y u)) -
      (galUnitsRep γ y - galUnitsRep (φ * γ * φ⁻¹) y) ∈ principalUnits B := by
  -- `W δ` is the telescoping product for `τ` and `φ` conjugated by `δ`; it is a principal unit at
  -- `δ B`. The wanted quotient is `γ (W 1) / γ (W γ⁻¹)`.
  let W (δ : Gal(Ω/ℚ)) : DiscreteUnits Ω :=
    ∑ b : ZMod q, Y b - galUnitsRep (δ * φ * δ⁻¹) (Y 0) +
      ∑ u : (ZMod q)ˣ, lg u • (galUnitsRep (δ * τ * δ⁻¹) (Y (v * u)) - Y u)
  have W_mem (δ : Gal(Ω/ℚ)) : galUnitsRep δ⁻¹ (W δ) ∈ principalUnits B := by
    have hqδ : (δ • B).valuation (q : Ω) < 1 := by simpa using (smul_apply_smul_lt_one_iff δ).mpr hq
    have W_conj : W δ ∈ principalUnits (δ • B) :=
      telescoping_mem_principalUnits (hτ.conj δ) (hφ.conj δ) (h_unit _ hqδ) (h_cong _ hqδ) hlg
    -- `δ` carries `B` to `δ B` and `δ⁻¹ (W δ)` to `W δ`.
    rw [mem_principalUnits_iff, ← smul_apply_smul_lt_one_iff δ]
    simpa [val_unitsRep, smul_sub] using mem_principalUnits_iff.mp W_conj
  -- `W 1` is a root of unity by the distribution relation, so `γ` acts on it by a power.
  obtain ⟨k, k_pos, hk⟩ := h_dist.exists_nsmul_eq_zero
  have hk_ne : NeZero k := NeZero.of_pos k_pos
  have h_diff : k • m • (∑ b : ZMod q, Y b - y) - k • m • (galUnitsRep φ (Y 0) - y) = 0 := by
    rw [hk, hφY, smul_zero, sub_zero]
  have root : (k * m) • W 1 = 0 := by
    simpa [W, ← smul_sub, smul_sum, smul_comm _ (lg _), hτY, mul_smul] using h_diff
  have γ_mem : galUnitsRep γ (W 1) ∈ principalUnits B := by
    rw [cyclotomicCharMod_eq_iff_unitsRep.mp (ZMod.natCast_zmod_val _).symm root]
    exact nsmul_mem (by simpa using W_mem 1) _
  -- Conjugating by `φ` and `τ` does not change how `γ` acts on these roots of unity.
  have h_conj_τ : ∑ u : (ZMod q)ˣ, lg u • galUnitsRep γ (galUnitsRep τ (Y (v * u)) - Y u) =
      ∑ u : (ZMod q)ˣ, lg u • galUnitsRep (τ * γ * τ⁻¹) (galUnitsRep τ (Y (v * u)) - Y u) :=
    sum_congr rfl fun u _ ↦ by rw [galUnitsRep_conj_of_nsmul_eq_zero γ τ (hτY u)]
  have h_eq : ∑ u : (ZMod q)ˣ, lg u • (galUnitsRep γ (Y u) - galUnitsRep (τ * γ * τ⁻¹) (Y u)) -
        (galUnitsRep γ y - galUnitsRep (φ * γ * φ⁻¹) y) =
      galUnitsRep γ (W 1) - galUnitsRep γ⁻¹⁻¹ (W γ⁻¹) := by
    linear_combination (norm := skip) galUnitsRep_conj_of_nsmul_eq_zero γ φ hφY - h_conj_τ
    simp [W, smul_sub]
    abel
  rw [h_eq]
  exact sub_mem γ_mem (W_mem γ⁻¹)

end Telescoping

end

section Cocycles

variable {O : Type} [CommRing O] {B : ClosurePlace} {M N l n e : ℕ} [NeZero N] [Fact l.Prime]
  [Algebra ℤ_[l] O] {ψ : DirichletCharacter O N} [Algebra (ZMod (l ^ n)) (QuotSpan (l ^ n : O))]
  {L : ∀ q : Nat.Primes, (ZMod q)ˣ →* Multiplicative (ZMod (l ^ n))}
  {p : Nat.Primes} {c : ℕ} {γ : Gal(Ω/ℚ)} {y : QZ → DiscreteUnits Ω} [NeZero M]

/-- A Kolyvagin system for the character `χ`, the element `γ`, the prime `p` and the set of primes
`P`: cocycles `κ S`, one for each `S ⊆ P`, that are unramified over `ℚ(ζ_N)` away from `l`, `p` and
`S`, vanish at `γ`, and are linked by the relation between Frobenius and inertia at the primes of
`P`. -/
structure IsKolyvaginSystem {V : Type} [AddCommGroup V] [Module O V] (χ : Gal(Ω/ℚ) →* Oˣ)
    (γ : Gal(Ω/ℚ)) (N l : ℕ) [NeZero N] (p : Nat.Primes) (P : Finset Nat.Primes)
    (κ : Finset Nat.Primes → Gal(Ω/ℚ) → V) : Prop where
  /-- `κ S` is a locally constant `χ`-cocycle that vanishes on inertia over `ℚ(ζ_N)` at the places
  above neither `l`, `p` nor a prime of `S`. -/
  mem_vanishingCocycles : ∀ S ⊆ P, κ S ∈ vanishingCocycles χ V (inertiaOff N l (insert p S))
  /-- `κ S` vanishes at `γ`. -/
  apply_eq_zero : ∀ S ⊆ P, κ S γ = 0
  /-- For `q ∈ P ∖ S` and a Frobenius `φ` at a place `A` above `q`, `κ S φ` is a value of
  `κ (S ∪ {q})` on inertia at `A`. -/
  exists_mem_inertiaGroup_eq : ∀ S ⊆ P, ∀ q ∈ P, q ∉ S →
    ∀ (A : ClosurePlace) (φ : Gal(Ω/ℚ)), IsFrob A q φ → A.valuation (q : Ω) < 1 →
    ∃ τ ∈ inertiaGroup Gal(Ω/ℚ) A, κ (insert q S) τ = κ S φ

/-!
## The cocycles at one level

In this section `y : ℚ/ℤ → Ω^×` is a family whose `lⁿ`-th powers `lⁿ • y` form a Jacobi family
(`New.OddPart.IsJacobiFamily`) at a level `M` (for `x` killed by `M`: `σ J(x) = J(a x)` if `σ` acts
on `μ_M` by `a`; `J x` is a unit at places prime to `p` and has order `floorDiff c x` at `B`), and
`commutatorLog (l ^ n) γ (y x) g` is the exponent `t` with `γ y(x) / (g γ g⁻¹) y(x) = ζᵗ`, for the
fixed primitive `lⁿ`-th root of unity `ζ`.
-/

omit [Fact l.Prime] in
/-- Let `lⁿ • y` be a Jacobi family at level `M`. If `σ` raises the `M`-th roots of unity to the
power `a`, then `σ (y x) / y (a x)` is an `lⁿ`-th root of unity, for every `x` killed by `M`. -/
private lemma nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) {x : QZ} (hx : M • x = 0) (σ : Gal(Ω/ℚ)) (a : ℕ)
    (ha : (cyclotomicCharMod Ω M σ).val = a) :
    l ^ n • (galUnitsRep σ (y x) - y (a • x)) = 0 := by
  rw [smul_sub, ← map_nsmul, sub_eq_zero]
  exact hJ.galUnitsRep_apply hx σ a ha

/-- Let `lⁿ • y` be a Jacobi family at level `M` and let `x` be killed by `M`. Then `commutatorLog`
names the root of unity `γ y(x) / (g γ g⁻¹) y(x)`: its image under `rootPowHom Ω (l ^ n)` is this
quotient. -/
private lemma rootPowHom_commutatorLog_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) {x : QZ} (hx : M • x = 0) (g : Gal(Ω/ℚ)) :
    (rootPowHom Ω (l ^ n)).val (commutatorLog (l ^ n) γ (y x) g) =
      galUnitsRep γ (y x) - galUnitsRep (g * γ * g⁻¹) (y x) := by
  -- The commutator `γ⁻¹ g γ g⁻¹` fixes the `M`-th roots of unity.
  have h_comm : (cyclotomicCharMod Ω M (γ⁻¹ * conj g γ)).val = (1 : ℕ) := by simp [mul_comm]
  have h_fixed : l ^ n • (galUnitsRep (γ⁻¹ * conj g γ) (y x) - y x) = 0 := by
    simpa using nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily hJ hx (γ⁻¹ * conj g γ) 1 h_comm
  have h_root : l ^ n • (galUnitsRep γ (y x) - galUnitsRep (g * γ * g⁻¹) (y x)) = 0 := by
    simpa [smul_sub] using congr_arg (fun z : DiscreteUnits Ω ↦ -galUnitsRep γ z) h_fixed
  exact invFun_eq (((rootPowHom Ω (l ^ n)).prop.2 _).mpr h_root)

/-- Let `lⁿ • y` be a Jacobi family at level `M`, with `N lⁿ ∣ M`, and let every prime of `I` divide
`M` and be `≡ 1 mod c N lⁿ`. For `S ⊆ I`, the derivative sum `derivativeSum e ψ L S d` of the
exponents `x ↦ commutatorLog (l ^ n) γ (y x) g` does not depend on the shifts `d` (the sum at
`q ∈ S` carries the weights `L q u - d q`). -/
private lemma derivativeSum_commutatorLog_eq_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) (hM : N * l ^ n ∣ M) {I : Finset Nat.Primes}
    (hI_dvd : ∀ q ∈ I, (q : ℕ) ∣ M) (hI_one : ∀ q ∈ I, (q : ℕ) ≡ 1 [MOD c * (N * l ^ n)])
    (g : Gal(Ω/ℚ)) {S : Finset Nat.Primes} (hS : S ⊆ I) (d f : Nat.Primes → ZMod (l ^ n)) :
    derivativeSum e ψ L S d (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) g) =
      derivativeSum e ψ L S f (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) g) := by
  let F (x : QZ) : ZMod (l ^ n) := commutatorLog (l ^ n) γ (y x) g
  have h_dist {r : Nat.Primes} (hr : r ∈ I) {x : QZ} (hx : M • x = 0) :
      ∑ b : ZMod r, F (x + ofZMod r b) = F ((r : ℕ) • x) := by
    let D : DiscreteUnits Ω := ∑ b : ZMod r, y (x + ofZMod r b) - y ((r : ℕ) • x)
    have h_order : IsOfFinAddOrder (l ^ n • D) := by
      simpa [D, smul_sub, smul_sum] using hJ.isOfFinAddOrder_sum_sub hx r (hI_dvd r hr)
        (hI_one r hr).of_mul_right.coprime_of_modEq_one.symm
    obtain ⟨k, k_pos, hk⟩ := (h_order.of_nsmul (NeZero.ne _)).exists_nsmul_eq_zero
    have : NeZero k := .of_pos k_pos
    have h_level (b : ZMod r) : M • (x + ofZMod r b) = 0 := by
      simp [← map_nsmul, (natCast_eq_zero_iff M r).mpr (hI_dvd r hr), hx]
    have h_level_r : M • ((r : ℕ) • x) = 0 := by simp [smul_comm M, hx]
    apply (rootPowHom Ω (l ^ n)).property.left
    simp only [F, map_sum, rootPowHom_commutatorLog_of_isJacobiFamily hJ (h_level _),
      rootPowHom_commutatorLog_of_isJacobiFamily hJ h_level_r]
    simpa only [D, map_sub, map_sum, sum_sub_distrib, sub_sub_sub_comm,
      sub_eq_sub_iff_sub_eq_sub] using galUnitsRep_conj_of_nsmul_eq_zero γ g hk
  revert hS d f
  refine S.strongInductionOn fun S ih hS d f ↦ ?_
  have step (T : Finset Nat.Primes) (hT : T ⊆ S) :
      derivativeSum e ψ L S (T.piecewise d f) F = derivativeSum e ψ L S f F := by
    induction T using Finset.induction with
    | empty => rfl
    | insert r T hrT ihT =>
      obtain ⟨hr, hT⟩ := insert_subset_iff.mp hT
      refine .trans ?_ (ihT hT)
      have erase_le : S.erase r ⊆ I := (erase_subset r S).trans hS
      have hr_not : r ∉ S.erase r := notMem_erase r S
      have h_dvd : ∀ q ∈ S.erase r, (q : ℕ) ∣ M := fun q hq ↦ hI_dvd q (erase_le hq)
      let G₁ (x : QZ) : ZMod (l ^ n) :=
        ∑ u : (ZMod r)ˣ, ((L r u).toAdd - (insert r T).piecewise d f r) * F (x + ofZMod r u)
      let H (x : QZ) : ZMod (l ^ n) := ∑ b : ZMod r, F (x + ofZMod r b)
      have h_vanish : derivativeSum e ψ L (S.erase r) ((insert r T).piecewise d f) H =
          derivativeSum e ψ L (S.erase r) ((insert r T).piecewise d f) F :=
        (derivativeSum_eq_of_prime hM h_dvd (hI_one r (hS hr)).of_mul_left hr_not
          (h_dist (hS hr))).trans (ih _ (erase_ssubset hr) erase_le _ _)
      rw [← insert_erase hr, derivativeSum_insert hr_not, derivativeSum_insert hr_not]
      calc derivativeSum e ψ L (S.erase r) ((insert r T).piecewise d f) G₁
          = derivativeSum e ψ L (S.erase r) ((insert r T).piecewise d f)
              (G₁ + (d r - f r) • (H - F)) := by simp [h_vanish]
        _ = derivativeSum e ψ L (S.erase r) (T.piecewise d f) _ :=
            derivativeSum_congr hM h_dvd (fun q hq ↦ by simp [ne_of_mem_erase hq]) fun _ ↦ by
              simp [G₁, H, hrT, mul_sum, sum_eq_add_sum_units, ← add_mul, ← sum_add_distrib]
  exact (derivativeSum_congr hM (fun q hq ↦ hI_dvd q (hS hq)) (fun q hq ↦ by simp [hq])
    fun _ ↦ rfl).trans (step S le_rfl)

/-- Let `lⁿ • y` be a Jacobi family at level `M` with `lⁿ ∣ M`, and let `g` lie in the inertia group
(`IsFrob A 1 g`) of a place `A` prime to `l`, fix the `M`-th roots of unity and have `g r / r = ζᵇ`.
If `y x ^ lⁿ` is a unit at `A` times `r ^ (lⁿ floorDiff c x)` for every `x` killed by `M`, then
`commutatorLog (l ^ n) γ (y x) g = (a floorDiff c x - floorDiff c (a x)) b` for such `x`, where `γ`
raises the `M`-th roots of unity to the power `a`. -/
private lemma nsmul_floorDiff_mul_sub_commutatorLog_eq_of_isFrob
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) (hM : l ^ n ∣ M) {a : ℕ}
    (ha : (cyclotomicCharMod Ω M γ).val = a) {g : Gal(Ω/ℚ)} {A : ClosurePlace}
    (hg_cyc : cyclotomicCharMod Ω M g = 1) (hg_inertia : IsFrob A 1 g)
    (hl : A.valuation (l ^ n : ℕ) = 1) {b : ZMod (l ^ n)} {r : DiscreteUnits Ω}
    (hr : galUnitsRep g r - r = (rootPowHom Ω (l ^ n)).val b)
    (h_unit : ∀ {x : QZ}, M • x = 0 → A.valuation (l ^ n • (y x - floorDiff c x • r)).toMul.val = 1)
    {x : QZ} (hx : M • x = 0) :
    a • (floorDiff c x * b) - commutatorLog (l ^ n) γ (y x) g = floorDiff c (a • x) * b := by
  have h_gy : l ^ n • (galUnitsRep g (y x) - y x) = 0 := by
    simpa using nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily hJ hx g 1 (by simp [hg_cyc])
  have h_γy : l ^ n • (galUnitsRep γ (y x) - y (a • x)) = 0 :=
    nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily hJ hx γ a ha
  have hax : M • a • x = 0 := by simp [smul_comm M, hx]
  have g_fix : galUnitsRep g (galUnitsRep γ (y x) - y (a • x)) =
      1 • (galUnitsRep γ (y x) - y (a • x)) :=
    cyclotomicCharMod_eq_iff_unitsRep.mp (hg_inertia.cyclotomicCharMod_eq hl) h_γy
  have γ_pow : galUnitsRep γ (galUnitsRep g (y x) - y x) = a • (galUnitsRep g (y x) - y x) :=
    cyclotomicCharMod_eq_iff_unitsRep.mp (cyclotomicCharMod_eq_of_dvd hM ha) h_gy
  have h_mem : galUnitsRep g (y (a • x) - floorDiff c (a • x) • r) -
      1 • (y (a • x) - floorDiff c (a • x) • r) -
      a • (galUnitsRep g (y x - floorDiff c x • r) - 1 • (y x - floorDiff c x • r)) ∈
      principalUnits A :=
    sub_mem (hg_inertia.sub_nsmul_mem_principalUnits (h_unit hax))
      (nsmul_mem (hg_inertia.sub_nsmul_mem_principalUnits (h_unit hx)) a)
  have h_eq : (rootPowHom Ω (l ^ n)).val
      (a • (floorDiff c x * b) - commutatorLog (l ^ n) γ (y x) g - floorDiff c (a • x) * b) =
      galUnitsRep g (y (a • x) - floorDiff c (a • x) • r) -
        1 • (y (a • x) - floorDiff c (a • x) • r) -
        a • (galUnitsRep g (y x - floorDiff c x • r) - 1 • (y x - floorDiff c x • r)) := by
    linear_combination (norm := skip) g_fix - γ_pow + galUnitsRep_conj_of_nsmul_eq_zero γ g h_gy
    simp [rootPowHom_commutatorLog_of_isJacobiFamily hJ hx g, ← hr, ← zsmul_eq_mul, smul_sub,
      -nsmul_eq_mul]
    abel
  exact eq_of_mem_principalUnits hl (by rwa [h_eq])

/-- The relation for the character sum. Let `B` lie above `p ≡ 1 mod N lⁿ`, and let `lⁿ • y` be a
Jacobi family at level `N lⁿ` for `p`, `B` and `c`. If the derivative sum over no primes of the
exponents `x ↦ commutatorLog (l ^ n) γ (y x) τ` vanishes for every `τ` in the inertia group of `B`,
then `(Υ γ - 1) ∑ floorDiff c (a / N lⁿ) aᵉ ψ(a) = 0` in `O/lⁿ`, where `Υ = cyc^(e+1) ψ` and `a`
runs over the units mod `N lⁿ`. -/
private lemma cyclotomicPowDirichlet_sub_one_smul_sum_eq_zero_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c (N * l ^ n) (l ^ n • y)) (hpB : B.valuation p < 1)
    (hp_one : (p : ℕ) ≡ 1 [MOD N * l ^ n])
    (h_vanish : ∀ τ ∈ inertiaGroup Gal(Ω/ℚ) B,
      derivativeSum e ψ L ∅ 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) τ) = 0) :
    (cyclotomicPowDirichlet l (e + 1) ψ γ - 1 : O) •
        ((∑ a : (ZMod (N * l ^ n))ˣ, floorDiff c (ofZMod (N * l ^ n) a) *
            ((a : ZMod (N * l ^ n)).val ^ e * ψ (a : ZMod (N * l ^ n)).val) : O) :
          QuotSpan (l ^ n : O)) =
      (0 : QuotSpan (l ^ n : O)) := by
  -- Take `τ` in the inertia group at `B` moving an `lⁿ`-th root `r` of a uniformiser by `ζ`. As
  -- `y x ^ lⁿ` is a unit times `r ^ (lⁿ floorDiff c x)`, the exponent of `y x` at `τ` is
  -- `a floorDiff c x - floorDiff c (a x)`, where `a` is the cyclotomic character of `γ`.
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (cyclotomicCharMod Ω (N * l ^ n) γ).val = a :=
    ⟨_, (ZMod.natCast_zmod_val _).symm⟩
  obtain ⟨v, hv, -⟩ := exists_isPlaceOver_prime hpB
  obtain ⟨τ, hτ, π, r, unif, hr, τ_r⟩ := exists_isTameGeneratorFor Gal(Ω/ℚ) (l ^ n) hv
  have h_unit {x : QZ} (hx : (N * l ^ n) • x = 0) :
      B.valuation (l ^ n • (y x - floorDiff c x • r)).toMul.val = 1 := by
    have h_ord : l ^ n • ordRat ℚ B (y x) = floorDiff c x := by simpa using hJ.ordRat_eq hx
    apply hv.ordRat_eq_zero_iff.mp
    simp [smul_sub, smul_comm, h_ord, hv.ordRat_ofBase, hv.isUniformizer_iff.mp unif, hr]
  have hτ_cyc : τ ∈ cycloGalGroup (N * l ^ n) := decompGroup_le_cycloGalGroup hpB hp_one hτ.left
  have hl : B.valuation (l ^ n : ℕ) = 1 :=
    (hp_one.of_dvd (dvd_mul_left _ _)).coprime_of_modEq_one.valuation_eq_one hpB
  have hτ_r : galUnitsRep τ r - r = (rootPowHom Ω (l ^ n)).val 1 := by simpa using τ_r
  have h_exponent {x : QZ} (hx : (N * l ^ n) • x = 0) :
      a • (floorDiff c x : ZMod (l ^ n)) - commutatorLog (l ^ n) γ (y x) τ =
        floorDiff c (a • x) := by
    simpa only [mul_one] using nsmul_floorDiff_mul_sub_commutatorLog_eq_of_isFrob hJ
      (dvd_mul_left _ _) ha hτ_cyc hτ hl hτ_r h_unit hx
  exact sub_one_smul_sum_eq_zero dvd_rfl ha h_exponent (h_vanish τ hτ)

/-- The cocycle rule. Let `lⁿ • y` be a Jacobi family at level `M`, with `N lⁿ ∣ M`, and let every
prime of `I` divide `M` and be `≡ 1 mod c N lⁿ`. Write `Λ h` for `derivativeSum e ψ L I 0` of the
exponents `x ↦ commutatorLog (l ^ n) γ (y x) h`. Then `Λ (g g') = Λ g + Υ(g) Λ g'` for
`Υ = cyc^(e+1) ψ`. -/
private lemma derivativeSum_commutatorLog_mul_eq_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) (hM : N * l ^ n ∣ M) {I : Finset Nat.Primes}
    (hI_dvd : ∀ q ∈ I, (q : ℕ) ∣ M) (hI_one : ∀ q ∈ I, (q : ℕ) ≡ 1 [MOD c * (N * l ^ n)])
    (g g' : Gal(Ω/ℚ)) :
    derivativeSum e ψ L I 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) (g * g')) =
      derivativeSum e ψ L I 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) g) +
        (cyclotomicPowDirichlet l (e + 1) ψ g).val •
          derivativeSum e ψ L I 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) g') := by
  -- With `a` the cyclotomic character of `g` mod `M` and `F h x` the exponent of `y x` at `h`:
  -- `F (g g') (a x) = F g (a x) + a F g' x` (`nsmul_exponent_eq_sub`). Equivariance of the
  -- derivative sum carries this to `Λ`; it changes only the shifts, which do not matter.
  let F (h : Gal(Ω/ℚ)) (x : QZ) : ZMod (l ^ n) := commutatorLog (l ^ n) γ (y x) h
  change derivativeSum e ψ L I 0 (F (g * g')) = derivativeSum e ψ L I 0 (F g) +
    (cyclotomicPowDirichlet l (e + 1) ψ g).val • derivativeSum e ψ L I 0 (F g')
  have killed {v : QuotSpan (l ^ n : O)} : l ^ n • v = 0 := nsmul_quot_eq_zero dvd_rfl v
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (cyclotomicCharMod Ω M g).val = a := ⟨_, (ZMod.natCast_zmod_val _).symm⟩
  have ha_N : (cyclotomicCharMod Ω (N * l ^ n) g).val = a := cyclotomicCharMod_eq_of_dvd hM ha
  have h_exponent {x : QZ} (hx : M • x = 0) : (a • F g') x = (F (g * g') - F g) (a • x) := by
    have hax : M • a • x = 0 := by simp [smul_comm M, hx]
    exact nsmul_exponent_eq_sub (cyclotomicCharMod_eq_of_dvd (dvd_of_mul_left_dvd hM) ha)
      (nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily hJ hx g a ha)
      (rootPowHom_commutatorLog_of_isJacobiFamily hJ hx g')
      (rootPowHom_commutatorLog_of_isJacobiFamily hJ hax (g * g'))
      (rootPowHom_commutatorLog_of_isJacobiFamily hJ hax g)
  have a_unit {q : Nat.Primes} (hq : q ∈ I) : IsUnit (a : ZMod q) :=
    ⟨unitsMap (hI_dvd q hq) (cyclotomicCharMod Ω M g),
      by rw [unitsMap_val, ha, cast_natCast (hI_dvd q hq) a]⟩
  let v (q : Nat.Primes) : (ZMod q)ˣ := invFun Units.val (a : ZMod q)
  let f (q : Nat.Primes) : ZMod (l ^ n) := (L q (v q)).toAdd
  have h_equiv : (cyclotomicPowDirichlet l e ψ g : O) • derivativeSum e ψ L I 0 (a • F g') =
      derivativeSum e ψ L I f (F (g * g') - F g) :=
    cyclotomicPowDirichlet_smul_derivativeSum hM hI_dvd ha_N
      (fun q hq ↦ ⟨v q, by simp [f], invFun_eq (a_unit hq)⟩) h_exponent
  have h_shift (h : Gal(Ω/ℚ)) : derivativeSum e ψ L I f (F h) = derivativeSum e ψ L I 0 (F h) :=
    derivativeSum_commutatorLog_eq_of_isJacobiFamily hJ hM hI_dvd hI_one h le_rfl f 0
  rw [cyclotomicPowDirichlet_succ_smul ha_N killed, ← map_nsmul, h_equiv, map_sub, h_shift,
    h_shift]
  abel

/-- The cocycles at the level `M = N lⁿ ∏_{r ∈ I} r`, when `lⁿ • y` is a Jacobi family at level `M`
and the primes of `I` are `≡ 1 mod c N lⁿ`: `g ↦ derivativeSum e ψ L I 0 F_g`, where `F_g x` is the
exponent `commutatorLog (l ^ n) γ (y x) g`, is a locally constant cocycle for `Υ = cyc^(e+1) ψ` that
vanishes on inertia over `ℚ(ζ_N)` at the places above neither `l`, `p` nor a prime of `I`. -/
private lemma derivativeSum_commutatorLog_mem_vanishingCocycles_of_isJacobiFamily
    (hJ : IsJacobiFamily p B c M (l ^ n • y)) {I : Finset Nat.Primes}
    (hM_eq : N * l ^ n * ∏ q ∈ I, (q : ℕ) = M) (hM : N * l ^ n ∣ M)
    (hI_dvd : ∀ q ∈ I, (q : ℕ) ∣ M) (hI_one : ∀ q ∈ I, (q : ℕ) ≡ 1 [MOD c * (N * l ^ n)]) :
    (fun g : Gal(Ω/ℚ) ↦ derivativeSum e ψ L I 0 fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) g) ∈
      vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ n : O))
        (inertiaOff N l (insert p I)) := by
  -- The derivative sum reads only the values on `M`-torsion.
  have h_congr {G G' : QZ → ZMod (l ^ n)} (hG : ∀ {x : QZ}, M • x = 0 → G x = G' x) :
      derivativeSum e ψ L I 0 G = derivativeSum e ψ L I 0 G' :=
    derivativeSum_congr hM hI_dvd (fun _ _ ↦ rfl) hG
  refine ⟨?_, fun g g' ↦
    derivativeSum_commutatorLog_mul_eq_of_isJacobiFamily hJ hM hI_dvd hI_one g g', ?_⟩
  · -- Locally constant: only the finitely many exponents at the points `b / M` are read.
    have h_orbit (b : ZMod M) :
        IsLocallyConstant fun g : Gal(Ω/ℚ) ↦ commutatorLog (l ^ n) γ (y (ofZMod M b)) g :=
      isLocallyConstant_commutatorLog
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g ↦ ?_
    filter_upwards [Filter.eventually_all.mpr fun b ↦ (h_orbit b).eventually_eq g] with g' hg'
    refine h_congr fun hx ↦ ?_
    obtain ⟨b, rfl⟩ := exists_ofZMod hx
    exact hg' b
  · -- Away from `l`, `p` and `I` the `y x` are units, and inertia fixing `μ_N` fixes `μ_M`; so
    -- every exponent is zero (`nsmul_floorDiff_mul_sub_commutatorLog_eq_of_isFrob` with `b = 0` and
    -- `r = 0`, the unit `1` of `Ω^×` written additively).
    rintro g ⟨A, ⟨hgN, hlA, hg⟩, hA⟩
    obtain ⟨hpA, hIA⟩ : A.valuation p = 1 ∧ ∀ q ∈ I, A.valuation (q : Ω) = 1 := by
      simpa [LE.le.ge_iff_eq] using hA
    have h_cofactor : A.valuation ((l ^ n * ∏ q ∈ I, (q : ℕ) : ℕ) : Ω) = 1 := by
      simp +contextual [hlA, hIA]
    have hgM : g ∈ cycloGalGroup M :=
      mem_cycloGalGroup_of_mem_inertiaGroup hg h_cofactor (by rw [← hM_eq, mul_assoc]) hgN
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (cyclotomicCharMod Ω M γ).val = a :=
      ⟨_, (ZMod.natCast_zmod_val _).symm⟩
    have h_unit {x : QZ} (hx : M • x = 0) :
        A.valuation (l ^ n • (y x - floorDiff c x • (0 : DiscreteUnits Ω))).toMul.val = 1 := by
      simpa using hJ.valuation_eq_one hx A hpA
    have h_exponent_zero {x : QZ} (hx : M • x = 0) : commutatorLog (l ^ n) γ (y x) g = 0 := by
      simpa using nsmul_floorDiff_mul_sub_commutatorLog_eq_of_isFrob hJ (dvd_of_mul_left_dvd hM) ha
        hgM hg (by simp [hlA]) (b := 0) (by simp) h_unit hx
    exact (h_congr (G' := 0) h_exponent_zero).trans (map_zero _)

/-- Frobenius and inertia for the exponents at one `x` killed by `M`: for a Frobenius `φ` at a place
`A` above `q` and `τ` in the inertia group of `A` whose cyclotomic character mod `q M` fixes the
`M`-torsion and sends `v u / q` to `u / q` (where `L q v = 1`), the exponents of `y (x + u/q)`
at `τ`, weighted by `L q u`, sum to the exponent of `y (q x)` at `φ`. Here `lⁿ ∣ M`, `q` is prime
to `M`, `q ≡ 1 mod c`, `p ≡ 1 mod q`, and `lⁿ • y` is a Jacobi family at levels `M` and `q M`. -/
private lemma sum_mul_commutatorLog_eq_of_isJacobiFamily {q : Nat.Primes}
    (hJ : IsJacobiFamily p B c M (l ^ n • y))
    (hJ_q : IsJacobiFamily p B c ((q : ℕ) * M) (l ^ n • y)) (hM : l ^ n ∣ M)
    (hq_cop : (q : ℕ).Coprime M) (hq_one : (q : ℕ) ≡ 1 [MOD c]) (hpq : (p : ℕ) ≡ 1 [MOD q])
    {v : (ZMod q)ˣ} (hv : L q v = ofAdd 1) {A : ClosurePlace} (hqA : A.valuation (q : Ω) < 1)
    {τ φ : Gal(Ω/ℚ)} (hτ : τ ∈ inertiaGroup Gal(Ω/ℚ) A)
    (hτ_cyc : ∀ x : QZ, M • x = 0 → ∀ u : ZMod q,
      (cyclotomicCharMod Ω ((q : ℕ) * M) τ : ZMod ((q : ℕ) * M)).val • (x + ofZMod q (v * u)) =
        x + ofZMod q u)
    (hφ : IsFrob A q φ) {x : QZ} (hx : M • x = 0) :
    ∑ u : (ZMod q)ˣ, (L q u).toAdd * commutatorLog (l ^ n) γ (y (x + ofZMod q u)) τ =
      commutatorLog (l ^ n) γ (y ((q : ℕ) • x)) φ := by
  -- Put `Y b = y (x + b/q)` and lift `L q` to `lg` with values in `ℤ`. The congruence
  -- `derivative_sub_frob_mem_principalUnits` says that the image of the difference of the two sides
  -- under `rootPowHom` is a principal unit at `A`; so the two sides are equal.
  choose lg hlg using fun u : (ZMod q)ˣ ↦
    (intCast_surjective (L q u).toAdd : ∃ z : ℤ, (z : ZMod (l ^ n)) = (L q u).toAdd)
  let Y (b : ZMod q) : DiscreteUnits Ω := y (x + ofZMod q b)
  have h_level (b : ZMod q) : ((q : ℕ) * M) • (x + ofZMod q b) = 0 := by
    simp [← map_nsmul, mul_smul, hx, natCast_self]
  have hx_q : M • ((q : ℕ) • x) = 0 := by simp [smul_comm M, hx]
  have h_unit (A' : ClosurePlace) (hqA' : A'.valuation (q : Ω) < 1) (b : ZMod q) :
      A'.valuation (l ^ n • Y b).toMul.val = 1 :=
    hJ_q.valuation_eq_one (h_level b) A'
      (hpq.coprime_of_modEq_one.symm.valuation_eq_one hqA')
  have h_cong (A' : ClosurePlace) (hqA' : A'.valuation (q : Ω) < 1) (b : ZMod q) :
      l ^ n • (Y b - Y 0) ∈ principalUnits A' := by
    simpa [Y, smul_sub] using hJ.sub_mem_principalUnits hx q A' (ofZMod q b)
      (by simp [← map_nsmul, natCast_self]) hpq.symm.dvd' hqA'
  have h_lg_step (u : (ZMod q)ˣ) : ((l ^ n : ℕ) : ℤ) ∣ lg (v * u) - lg u - 1 := by
    rw [← intCast_zmod_eq_zero_iff_dvd]
    simp [hlg, hv]
  -- Up to `lⁿ`-th roots of unity, `φ` sends `Y 0 = y x` to `y (q x)`, and `τ` sends `Y (v u)` to
  -- `Y u`.
  have hφ_Y : l ^ n • (galUnitsRep φ (Y 0) - y ((q : ℕ) • x)) = 0 := by
    simpa [Y] using nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily hJ hx φ q
      (hφ.cyclotomicCharMod_eq (hq_cop.valuation_eq_one hqA))
  have hτ_Y (u : ZMod q) : l ^ n • (galUnitsRep τ (Y (v * u)) - Y u) = 0 := by
    simpa only [hτ_cyc x hx u] using
      nsmul_galUnitsRep_sub_eq_zero_of_isJacobiFamily hJ_q (h_level (v * u)) τ _
        (ZMod.natCast_zmod_val _).symm
  have h_dist : IsOfFinAddOrder (l ^ n • (∑ b : ZMod q, Y b - y ((q : ℕ) • x))) := by
    simpa [Y, smul_sub, smul_sum] using
      hJ_q.isOfFinAddOrder_sum_sub (h_level 0) q (dvd_mul_right _ _)
        hq_one.coprime_of_modEq_one.symm
  have h_image : (rootPowHom Ω (l ^ n)).val
      (∑ u : (ZMod q)ˣ, (L q u).toAdd * commutatorLog (l ^ n) γ (y (x + ofZMod q u)) τ -
        commutatorLog (l ^ n) γ (y ((q : ℕ) • x)) φ) =
      ∑ u : (ZMod q)ˣ, lg u • (galUnitsRep γ (Y u) - galUnitsRep (τ * γ * τ⁻¹) (Y u)) -
        (galUnitsRep γ (y ((q : ℕ) • x)) - galUnitsRep (φ * γ * φ⁻¹) (y ((q : ℕ) • x))) := by
    simp [← hlg, ← zsmul_eq_mul, rootPowHom_commutatorLog_of_isJacobiFamily hJ_q (h_level _),
      rootPowHom_commutatorLog_of_isJacobiFamily hJ hx_q, Y]
  apply eq_of_mem_principalUnits ((hq_cop.of_dvd_right hM).valuation_eq_one hqA)
  rw [h_image]
  exact derivative_sub_frob_mem_principalUnits γ hqA hτ hφ h_unit h_cong h_lg_step hφ_Y hτ_Y h_dist

/-- Frobenius and inertia for the derivative sums, at the level `M = N lⁿ ∏_{r ∈ I} r`: for a prime
`q ∉ I`, a place `A` above `q` and a Frobenius `φ` at `A`, some `τ` in the inertia group of `A` has
`Λ (I ∪ {q}) τ = Λ I φ`, with `Λ S h = derivativeSum e ψ L S 0 (commutatorLog (l ^ n) γ (y ·) h)`.
Here `p ≡ 1` mod `M` and mod `q`, `lⁿ • y` is a Jacobi family at every level `M' ∣ p - 1`, `q` and
the primes of `I` are `≡ 1 mod c N lⁿ`, and `L q v = 1` for some `v`. -/
private lemma exists_mem_inertiaGroup_derivativeSum_insert_eq_of_isJacobiFamily
    (hJ : ∀ (M' : ℕ) [NeZero M'], (p : ℕ) ≡ 1 [MOD M'] → IsJacobiFamily p B c M' (l ^ n • y))
    {I : Finset Nat.Primes} (hM_eq : N * l ^ n * ∏ r ∈ I, (r : ℕ) = M) (hM : N * l ^ n ∣ M)
    (hI_dvd : ∀ r ∈ I, (r : ℕ) ∣ M) (hpM : (p : ℕ) ≡ 1 [MOD M])
    (hI_one : ∀ r ∈ I, (r : ℕ) ≡ 1 [MOD c * (N * l ^ n)])
    {q : Nat.Primes} (hq_one : (q : ℕ) ≡ 1 [MOD c * (N * l ^ n)]) (hqI : q ∉ I)
    (hpq : (p : ℕ) ≡ 1 [MOD q]) (hL : ∃ v : (ZMod q)ˣ, L q v = ofAdd 1) {A : ClosurePlace}
    {φ : Gal(Ω/ℚ)} (hφ : IsFrob A q φ) (hqA : A.valuation (q : Ω) < 1) :
    ∃ τ ∈ inertiaGroup Gal(Ω/ℚ) A,
      derivativeSum e ψ L (insert q I) 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) τ) =
        derivativeSum e ψ L I 0 (fun x : QZ ↦ commutatorLog (l ^ n) γ (y x) φ) := by
  -- Take `v` with `L q v = 1` and `τ` in the inertia group at `A` with `cyc_q τ = v⁻¹`. By
  -- `derivativeSum_eq_of_prime` it suffices to compare the exponents at each `x` killed by `M`.
  obtain ⟨v, hv⟩ := hL
  have hq_cop : (q : ℕ).Coprime M := by
    rw [← hM_eq]
    refine hq_one.of_mul_left.coprime_of_modEq_one.mul_right (Nat.Coprime.prod_right fun r hr ↦
      (Nat.coprime_primes q.prop r.prop).mpr fun h_eq ↦ hqI ?_)
    rwa [Subtype.ext h_eq]
  have hpqM : (p : ℕ) ≡ 1 [MOD q * M] := (Nat.modEq_and_modEq_iff_modEq_mul hq_cop).mp ⟨hpq, hpM⟩
  obtain ⟨τ, hτ, hτ_cyc⟩ := exists_inertia_smul_add_ofZMod hqA (hq_cop.valuation_eq_one hqA) v
  have h_relation {x : QZ} (hx : M • x = 0) :
      ∑ u : (ZMod q)ˣ, (L q u).toAdd * commutatorLog (l ^ n) γ (y (x + ofZMod q u)) τ =
        commutatorLog (l ^ n) γ (y ((q : ℕ) • x)) φ :=
    sum_mul_commutatorLog_eq_of_isJacobiFamily (hJ M hpM) (hJ (q * M) hpqM)
      (dvd_of_mul_left_dvd hM) hq_cop hq_one.of_mul_right hpq hv hqA hτ hτ_cyc hφ hx
  refine ⟨τ, hτ, ?_⟩
  calc derivativeSum e ψ L (insert q I) 0 (fun x ↦ commutatorLog (l ^ n) γ (y x) τ)
      = derivativeSum e ψ L I 0 fun x ↦
          ∑ u : (ZMod q)ˣ, (L q u).toAdd * commutatorLog (l ^ n) γ (y (x + ofZMod q u)) τ := by
        simp only [derivativeSum_insert hqI, Pi.zero_apply, sub_zero]
    _ = derivativeSum e ψ L I _ (fun x ↦ commutatorLog (l ^ n) γ (y x) φ) :=
        derivativeSum_eq_of_prime hM hI_dvd hq_one.of_mul_left hqI h_relation
    _ = derivativeSum e ψ L I 0 (fun x ↦ commutatorLog (l ^ n) γ (y x) φ) :=
        derivativeSum_commutatorLog_eq_of_isJacobiFamily (hJ M hpM) hM hI_dvd hI_one φ le_rfl _ 0

end Cocycles

/-- Kolyvagin's cocycles. Let `l` be a prime, `O` a `ℤ_l`-algebra, `ψ` a Dirichlet character mod
`N ≠ 0` with values in `O`, and `Υ = cyc^(e+1) ψ` (`New.cyclotomicPowDirichlet`) the character of
`Gal(ℚ̄/ℚ)` with `cyc` the `l`-adic cyclotomic character. Let `γ ∈ Gal(ℚ̄/ℚ)`, let `P` be a finite
set of primes `≡ 1 mod c N lⁿ`, and let `B` be a place of `ℚ̄` above a prime `p ≡ 1 mod N lⁿ ∏ P`.
Then there are maps `κ S` from `Gal(ℚ̄/ℚ)` to `O/lⁿ` (`QuotSpan (l ^ n : O)`), one for each finite
set `S` of primes, with two properties.
* They form a Kolyvagin system (`New.OddPart.IsKolyvaginSystem`). For `S ⊆ P`, `κ S` is a locally
  constant `Υ`-cocycle, is unramified over `ℚ(ζ_N)` away from `l`, `p` and `S`, and vanishes at
  `γ`. For `q ∈ P ∖ S`, the value of `κ S` at a Frobenius at a place `A` above `q` is a value of
  `κ (S ∪ {q})` on the inertia group of `A`.
* If `κ ∅` vanishes on the inertia group of `B`, then `Υ γ - 1` kills the twisted Stickelberger
  sum `∑ₐ m(a / N lⁿ) aᵉ ψ(a)` in `O/lⁿ`. Here `a` runs over the units mod `N lⁿ`, read as integers
  in `[0, N lⁿ)`; `ofZMod M a` is `a / M` in `ℚ/ℤ`; and `m(x) = ⌊c ⟨x⟩⌋ - ⌊c ⟨-x⟩⌋`
  (`New.OddPart.floorDiff c x`), where `⟨x⟩` is the representative of `x` in `[0, 1)`. -/
lemma exists_isKolyvaginSystem {O : Type} [CommRing O] {B : ClosurePlace} {N l n : ℕ} [NeZero N]
    [Fact l.Prime] [Algebra ℤ_[l] O] {ψ : DirichletCharacter O N} (e c : ℕ) (γ : Gal(Ω/ℚ))
    {P : Finset Nat.Primes} (hP_one : ∀ q ∈ P, (q : ℕ) ≡ 1 [MOD c * (N * l ^ n)])
    {p : Nat.Primes} (hp_one : (p : ℕ) ≡ 1 [MOD N * l ^ n * ∏ q ∈ P, (q : ℕ)])
    (hpB : B.valuation (p : Ω) < 1) :
    ∃ κ : Finset Nat.Primes → Gal(Ω/ℚ) → QuotSpan (l ^ n : O),
      IsKolyvaginSystem (cyclotomicPowDirichlet l (e + 1) ψ) γ N l p P κ ∧
      ((∀ τ ∈ inertiaGroup Gal(Ω/ℚ) B, κ ∅ τ = 0) →
        (cyclotomicPowDirichlet l (e + 1) ψ γ - 1 : O) •
            ((∑ a : (ZMod (N * l ^ n))ˣ, floorDiff c (ofZMod (N * l ^ n) a) *
                ((a : ZMod (N * l ^ n)).val ^ e * ψ (a : ZMod (N * l ^ n)).val) : O) :
              QuotSpan (l ^ n : O)) =
          (0 : QuotSpan (l ^ n : O))) := by
  -- Let `y x` be an `lⁿ`-th root of the Jacobi-type quotient `J x` (`exists_isJacobiFamily`). Then
  -- `κ S g` is the derivative sum over `S` of the exponents of the `lⁿ`-th roots of unity
  -- `γ y(x) / (g γ g⁻¹) y(x)`; its properties are proved at the level `N lⁿ ∏ S` above.
  have killed (x : QuotSpan (l ^ n : O)) : l ^ n • x = 0 := nsmul_quot_eq_zero dvd_rfl x
  let _ : Module (ZMod (l ^ n)) (QuotSpan (l ^ n : O)) := AddCommGroup.zmodModule killed
  let _ : Algebra (ZMod (l ^ n)) (QuotSpan (l ^ n : O)) :=
    algebraOfModule (l ^ n) (QuotSpan (l ^ n : O))
  obtain ⟨J, hJ⟩ : ∃ J : QZ → DiscreteUnits Ω,
      ∀ (M : ℕ) [NeZero M], (p : ℕ) ≡ 1 [MOD M] → IsJacobiFamily p B c M J :=
    exists_isJacobiFamily hpB c
  obtain ⟨y, hy⟩ : ∃ y : QZ → DiscreteUnits Ω, ∀ x : QZ, l ^ n • y x = J x :=
    Classical.skolem.mp fun x ↦ (J x).exists_nsmul (ne _)
  obtain rfl : J = l ^ n • y := funext fun x ↦ (hy x).symm
  -- Discrete logarithms `L q` onto `ℤ/lⁿ`, for `q ∈ P`.
  have exists_log : ∀ q ∈ P, ∃ L : (ZMod q)ˣ →* Multiplicative (ZMod (l ^ n)),
      ∃ v : (ZMod q)ˣ, L v = ofAdd 1 :=
    fun q hq ↦ exists_monoidHom_units_zmod_eq_ofAdd_one (hP_one q hq).of_mul_left.of_mul_left
  choose! L hL using exists_log
  let κ (S : Finset Nat.Primes) (g : Gal(Ω/ℚ)) : QuotSpan (l ^ n : O) :=
    derivativeSum e ψ L S 0 fun x ↦ commutatorLog (l ^ n) γ (y x) g
  -- The level `M S = N lⁿ ∏ S` divides `p - 1` for `S ⊆ P`.
  let M (S : Finset Nat.Primes) : ℕ := N * l ^ n * ∏ q ∈ S, (q : ℕ)
  have M_neZero (S : Finset Nat.Primes) : NeZero (M S) := ⟨by simp [M, ne, prod_eq_zero_iff]⟩
  have base_dvd (S : Finset Nat.Primes) : N * l ^ n ∣ M S := dvd_mul_right _ _
  have prime_dvd (S : Finset Nat.Primes) (q : Nat.Primes) (hq : q ∈ S) : (q : ℕ) ∣ M S :=
    (dvd_prod_of_mem _ hq).mul_left _
  have hp_level {S : Finset Nat.Primes} (hS : S ⊆ P) : (p : ℕ) ≡ 1 [MOD M S] :=
    hp_one.of_dvd (mul_dvd_mul_left (N * l ^ n) (prod_dvd_prod_of_subset S P _ hS))
  have hJ_level {S : Finset Nat.Primes} (hS : S ⊆ P) : IsJacobiFamily p B c (M S) (l ^ n • y) :=
    hJ (M S) (hp_level hS)
  have system : IsKolyvaginSystem (cyclotomicPowDirichlet l (e + 1) ψ) γ N l p P κ :=
    { mem_vanishingCocycles := fun S hS ↦
        derivativeSum_commutatorLog_mem_vanishingCocycles_of_isJacobiFamily (hJ_level hS) rfl
          (base_dvd S) (prime_dvd S) fun q hq ↦ hP_one q (hS hq)
      apply_eq_zero := fun S hS ↦ by
        dsimp only [κ]
        rw [derivativeSum_congr (base_dvd S) (prime_dvd S) (fun _ _ ↦ rfl) (G' := 0), map_zero]
        intro x hx
        apply (rootPowHom Ω (l ^ n)).property.left
        rw [rootPowHom_commutatorLog_of_isJacobiFamily (hJ_level hS) hx γ, mul_inv_cancel_right,
          sub_self]
        simp
      exists_mem_inertiaGroup_eq := fun S hS q hqP hqS A φ hφ hqA ↦
        exists_mem_inertiaGroup_derivativeSum_insert_eq_of_isJacobiFamily hJ rfl (base_dvd S)
          (prime_dvd S) (hp_level hS) (fun r hr ↦ hP_one r (hS hr)) (hP_one q hqP) hqS
          (hp_one.of_dvd (prime_dvd P q hqP)) (hL q hqP) hφ hqA }
  -- The relation for `κ ∅` is proved at the level `N lⁿ`.
  have hp_base : (p : ℕ) ≡ 1 [MOD N * l ^ n] := hp_one.of_dvd (base_dvd P)
  exact ⟨κ, system,
    cyclotomicPowDirichlet_sub_one_smul_sum_eq_zero_of_isJacobiFamily (hJ (N * l ^ n) hp_base) hpB
      hp_base⟩

end New.OddPart
end
end

/-!
# Reciprocity laws and Stickelberger and Kolyvagin bounds for odd-part cocycles

The file studies cocycles on `Gal(Ω/ℚ)`, with `Ω` an algebraic closure of ℚ. Here
`New.cyclotomicPowDirichlet l e ψ` is `cyc^e ψ` with `cyc` the `l`-adic cyclotomic character. The
module `New.OddPart.component l e ψ ν` consists of the cocycles for `(cyc^e ψ)⁻¹` with values in
`O / l^ν`, where `O` (`PadicIntegerRing O l`) is the integer ring of a finite extension of ℚ_l, that
satisfy three conditions. They are unramified off `l` over ℚ(μ_N), split at `l` over ℚ(μ_{N l^∞})
and zero at `New.cmConj`, a complex conjugation. Reciprocity laws at primes `q ≡ 1` relate the value
of one cocycle at a Frobenius element to the ramification of another. Using these laws and
Chebotarev's theorem, the file bounds these components in two ways. One bound is an annihilation
result analogous to Stickelberger's theorem. The other uses Kolyvagin's descent with the Euler
system of Gauss sums.

## Main definitions and results

* `New.OddPart.artin_reciprocity_of_mem_component`: Artin reciprocity over ℚ(μ_{N m}), where the
  prime q ≡ 1 splits completely, pairs a cocycle `x` with a number `y`; only the places above q
  contribute.
* `New.OddPart.reciprocity_mod_ell`: the same law modulo `l` for a cocycle κ for cyc^(e+1) ψ; if
  `2 (a ^ e - 1) x φ ≠ 0`, then κ vanishes on the inertia group of `B`.
* `New.OddPart.nsmul_component_eq_zero`: if `X` has the Stickelberger property
  (`New.OddPart.IsStickelbergerBound N e X`), `cyc^e ψ` is odd and `e ≠ 0`, then `4 X²` kills
  `New.OddPart.component l e ψ ν` (an analogue of Stickelberger's theorem).
* `New.OddPart.exists_detecting_points_component`: for large `l`, a cocycle in
  `New.OddPart.component l e ψ ν` is determined by its values at `v_l(X) + 1` elements (Kolyvagin's
  descent with the Euler system of Gauss sums).

Notions from other files:
* `New.cyclotomicPowDirichlet l e ψ`: the character `cyc^e ψ` of `Gal(Ω/ℚ)` with values in `Oˣ`; the
  Dirichlet character `ψ` is read through the action on the `N`-th roots of unity.
* `New.OddPart.vanishingCocycles χ M s`: the `O`-module of locally constant maps `x : Gal(Ω/ℚ) → M`
  with `x (g h) = x g + χ(g) x h` (cocycles for `χ`) that vanish on `s`.
* `New.IsFrob A q σ`: `σ` stabilises the place `A` and `σ • x ≡ x ^ q` modulo its maximal ideal for
  all `x ∈ A`.
* `New.ordRat K A`: the order `Ωˣ → ℚ` at the place `A`, normalised to be `1` on uniformisers of
  `K`. `New.cyclotomicCharMod Ω n` gives the action on the `n`-th roots of unity, in `(ℤ/n)ˣ`.

## Relation to the literature

Known result: Stickelberger annihilation and the Kolyvagin–Rubin bound for odd twisted components.
Here the value is taken at a negative integer instead of at zero, and for an integer X whose
multiples (a^(e+1) − 1) X, for a ≡ 1 mod N, are congruent modulo each m prime to a to 2w times the
Stickelberger sum at level N m, and which for each prime ℓ is divisible by (a^e − 1)(a^(e+1) − 1)
for some such a prime to ℓ, 4X² kills the odd component at every prime. For large primes ℓ, at most
v_ℓ(X)+1 Galois elements detect its classes. Source: J. Coates, W. Sinnott, An analogue of
Stickelberger's theorem for the higher K-groups, Invent. Math. 24 (1974); K. Rubin, Euler Systems,
2000, III.4, Thm 4.6.
-/

@[expose] public section

namespace New.OddPart

/-!
## Reciprocity laws for Galois cocycles and finiteness

Places are valuation subrings of `Ω`, and the group Ω^× is written additively. `New.cycloGalGroup N`
is the Galois group over ℚ(μ_N). The cocycles in `New.OddPart.component l e ψ ν` vanish at
`New.cmConj`. Over ℚ(μ_N) they also vanish on inertia at places prime to `l` and on
`New.Selmer.shaLocalSet` above `l`.
-/

section ReciprocityLaw

open DiscreteUnits Finset Subgroup QZ MonoidHom NeZero Fact Pointwise Submodule IsLocalRing
  IsPlaceOver

variable {O M : Type} [CommRing O]
  {N l m e q ν : ℕ} [NeZero N] [NeZero m] [Fact l.Prime] [Fact q.Prime] [PadicIntegerRing O l]
  {ψ : DirichletCharacter O N} {g τ φ : Gal(Ω/ℚ)}
  {B : ClosurePlace} [AddCommGroup M] [Module O M]
  {χ : Gal(Ω/ℚ) →* Oˣ} {s : Set Gal(Ω/ℚ)} {z : Gal(Ω/ℚ) → M} (hz : z ∈ vanishingCocycles χ M s)

/-- A map `z` in `vanishingCocycles χ M s` satisfies the cocycle rule
`z (g h) = z g + χ(g) z h`. -/
private lemma apply_mul_of_mem_vanishingCocycles (hz : z ∈ vanishingCocycles χ M s)
    (g h : Gal(Ω/ℚ)) : z (g * h) = z g + (χ g).val • z h :=
  hz.2.1 g h

/-- A map `z` in `vanishingCocycles χ M s` is locally constant. -/
private lemma isLocallyConstant_of_mem_vanishingCocycles (hz : z ∈ vanishingCocycles χ M s) :
    IsLocallyConstant z :=
  hz.1

/-- A map `z` in `vanishingCocycles χ M s` vanishes on `s`. -/
private lemma apply_eq_zero_of_mem_vanishingCocycles (hz : z ∈ vanishingCocycles χ M s)
    {g : Gal(Ω/ℚ)} (hg : g ∈ s) : z g = 0 :=
  hz.2.2 g hg

/-- Let `g` fix the `N m`-th roots of unity (`g ∈ cycloGalGroup (N * m)`) and let `m • y = 0`.
Then `cyc^e ψ (g)` and its inverse fix `y`. -/
lemma cyclotomicPowDirichlet_smul_eq_self (hg : g ∈ cycloGalGroup (N * m)) {y : M}
    (hy : m • y = 0) :
    (cyclotomicPowDirichlet l e ψ g).val • y = y ∧
      (cyclotomicPowDirichlet l e ψ g)⁻¹.val • y = y := by
  have h_fix {σ : Gal(Ω/ℚ)} (hσ : σ ∈ cycloGalGroup (N * m)) :
      (cyclotomicPowDirichlet l e ψ σ).val • y = y := by
    simpa using cyclotomicPowDirichlet_smul (a := 1) (by simp [mem_ker.1 hσ]) hy
  exact ⟨h_fix hg, by simpa using h_fix (inv_mem hg)⟩

/-- The open subgroup `{g | z g = 0}` of zeros of a map `z` in `vanishingCocycles χ M s` (given by
`hz`): it is a subgroup by the cocycle rule, and open since `z` is locally constant. -/
noncomputable def openCocycleKer : OpenSubgroup Gal(Ω/ℚ) :=
  OpenSubgroup.mk (cocycleKer χ hz.2.1) (hz.1 {0})

/-- Let `z` be in `vanishingCocycles χ M s`, with `z γ = 0` and `(χ γ - 1) • z ≠ 0`. Then `z` does
not vanish on the Galois group over ℚ(μ_f), for any `f ≠ 0`. -/
lemma not_cycloGalGroup_le_openCocycleKer (γ : Gal(Ω/ℚ)) (hγ : z γ = 0)
    (h_ne : ((χ γ).val - 1) • z ≠ 0) (f : ℕ) [NeZero f] :
    ¬cycloGalGroup f ≤ openCocycleKer hz := by
  -- If `z` vanishes on `cycloGalGroup f`, it kills all commutators, so Sah's lemma gives
  -- `(χ γ - 1) • z g = (χ g - 1) • z γ`; and `z γ = 0`.
  refine fun h_le ↦ h_ne (funext fun g ↦ ?_)
  have h_comm_mem : (γ * g)⁻¹ * (g * γ) ∈ cycloGalGroup f := by simp [mul_right_comm]
  simpa [hγ] using sah (apply_mul_of_mem_vanishingCocycles hz) γ g (h_le h_comm_mem)

omit [PadicIntegerRing O l] in
/-- Let `M` be finite, let ℚ(μ_{N l^n}) trivialise the action through `χ`, and let `s` contain
the inertia over ℚ(μ_N) at all non-trivial places prime to `l`. Then there are finitely many
locally constant cocycles for `χ` that vanish on `s`. -/
lemma finite_vanishingCocycles [Finite M] {n : ℕ}
    (h_triv : ∀ g : cycloGalGroup (N * l ^ n), ∀ {y : M}, (χ g).val • y = y)
    (hs : ↑(cycloGalGroup N) ∩ inertiaAbove (placesDividing ℚ l)ᶜ ⊆ s) :
    Finite (vanishingCocycles χ M s) := by
  -- These cocycles are continuous for the discrete topology and unramified outside `N l`, and
  -- there are finitely many such (`selmerZ1.finite_unramified_cocycles`).
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := discreteTopology_bot M
  let : MulAction Gal(Ω/ℚ) M := .compHom M χ
  have cont : ContinuousSMul Gal(Ω/ℚ) M :=
    continuousSMul_iff_stabilizer_isOpen.2 fun y ↦ isOpen_mono (fun g hg ↦ h_triv ⟨g, hg⟩) out
  refine (selmerZ1.finite_unramified_cocycles (.of (charRep M χ) cont.continuous_smul)
    ((finite_natCast_mem N).union (placesDividing ℚ l).toFinite)).subset
    fun z ⟨z_lc, z_cocycle, z_zero⟩ ↦
      ⟨⟨z_lc.continuous, z_cocycle⟩, Submodule.mem_pi.2 fun g hg ↦ z_zero g ?_⟩
  -- Inertia at a place prime to `N l` fixes the `N`-th roots of unity, so `g ∈ s`.
  change g ∈ s
  simp_all [inertiaAbove, Set.subset_def]
  grind [valuation_natCast_eq_one_iff, cyclotomicCharMod_eq_one_of_mem_inertiaGroup]

/-- Let `B` be a place of `Ω` above `l`, and let `a ≡ 1 mod N` be prime to `l`. Then some element
`i` of the inertia group of `B` has `cyc^e ψ (i) = a ^ e`. -/
lemma exists_inertia_cyclotomicPowDirichlet_eq {a : ℕ} (ha : l.Coprime a) (ha_one : a ≡ 1 [MOD N])
    (hB : B.valuation (l : Ω) < 1) (e : ℕ) :
    ∃ i ∈ inertiaGroup Gal(Ω/ℚ) B, (cyclotomicPowDirichlet l e ψ i).val = a ^ e := by
  -- Take `i` in inertia with `l`-adic cyclotomic character `a`.
  obtain ⟨i, hi, cyc_i⟩ := exists_inertia_cyclotomicChar_eq hB ha
  -- It fixes the roots of unity of order the `l`-part of `N`, since `a ≡ 1` modulo that number.
  have fix_l_part : i ∈ cycloGalGroup (ordProj[l] N) := Units.ext <| by
    simp [cyclotomicCharMod_prime_pow_eq, cyc_i,
      (ZMod.natCast_eq_natCast_iff a 1 _).2 (ha_one.of_dvd (N.ordProj_dvd l))]
  -- By rigidity it fixes all `N`-th roots of unity, so `ψ` contributes nothing.
  have hB_compl : B.valuation (ordCompl[l] N : ℕ) = 1 :=
    (N.coprime_ordCompl out (NeZero.ne N)).valuation_eq_one hB
  have fix_N : i ∈ cycloGalGroup N :=
    mem_cycloGalGroup_of_mem_inertiaGroup hi hB_compl (N.ordProj_mul_ordCompl_eq_self l) fix_l_part
  exact ⟨i, hi, by simp [cyclotomicPowDirichlet, cyc_i, mem_ker.1 fix_N]⟩

/-- A cocycle `x ∈ component l e ψ ν` vanishes at every `g` that fixes the `N m`-th roots of unity
and lies in the inertia group of a place `A` of `Ω` prime to `l`, above the place `t` of `ℚ`. -/
private lemma apply_eq_zero_of_mem_inertiaGroup_of_valuation_eq_one
    {x : Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)} (hx : x ∈ component l e ψ ν) {A : ClosurePlace}
    {t : FinPlace ℚ} (hA : IsPlaceOver A t) (hA_l : A.valuation l = 1) {g : Gal(Ω/ℚ)}
    (hg : g ∈ cycloGalGroup (N * m)) (hg_inertia : g ∈ inertiaGroup Gal(Ω/ℚ) A) : x g = 0 := by
  have hg_N : g ∈ cycloGalGroup N := cyclotomicCharMod_eq_one_of_dvd ⟨_, rfl⟩ hg
  have hg_off : g ∈ inertiaAbove (placesDividing ℚ l)ᶜ :=
    ⟨t, hA.valuation_natCast_eq_one_iff.1 hA_l, A, hA, hg_inertia⟩
  exact apply_eq_zero_of_mem_vanishingCocycles hx (.inr ⟨hg_N, .inl hg_off⟩)

/-- Let `x ∈ component l e ψ ν` be killed by `m`, let `A` be a place of `Ω` above `l`, and let
`a ≡ 1 mod N` be prime to `l`. Then `(a ^ e - 1) • x g = 0` for every `g` that fixes the `N m`-th
roots of unity and lies in the decomposition group of `A`. -/
private lemma pow_sub_one_smul_apply_eq_zero_of_mem_decompGroup {a : ℕ} (ha : l.Coprime a)
    (ha_one : a ≡ 1 [MOD N]) {x : Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)} (hx : x ∈ component l e ψ ν)
    (hx_tors : ∀ g : Gal(Ω/ℚ), m • x g = 0) {A : ClosurePlace} (hA : A.valuation l < 1)
    {g : Gal(Ω/ℚ)} (hg : g ∈ cycloGalGroup (N * m)) (hg_dec : g ∈ decompGroup Gal(Ω/ℚ) A) :
    (a ^ e - 1 : O) • x g = 0 := by
  -- Take `δ` in the inertia group of `A` with `cyc^e ψ (δ) = a ^ e`. The cocycle `x` vanishes on
  -- the commutator of `δ⁻¹` and `g`, so Sah's lemma gives `(Υ δ - 1) • x g = ((Υ g)⁻¹ - 1) • x δ⁻¹`
  -- for `Υ = cyc^e ψ`, and the right side is `0` because `g` acts trivially.
  obtain ⟨δ, hδ_inertia, hδ⟩ := exists_inertia_cyclotomicPowDirichlet_eq (ψ := ψ) ha ha_one hA e
  have hδ_dec : δ ∈ decompGroup Gal(Ω/ℚ) A := IsFrob.mem_decompGroup hδ_inertia
  have h_comm_mem : (δ⁻¹ * g)⁻¹ * (g * δ⁻¹) ∈
      ↑(cycloGalGroup N) ∩ (inertiaAbove (placesDividing ℚ l)ᶜ ∪ Selmer.shaLocalSet l ℚ 1) :=
    ⟨by simp [mul_comm], .inr ⟨A, by simp_all [mul_comm, mul_mem]⟩⟩
  have h_sah : (((cyclotomicPowDirichlet l e ψ)⁻¹ δ⁻¹).val - 1) • x g =
      (((cyclotomicPowDirichlet l e ψ)⁻¹ g).val - 1) • x δ⁻¹ :=
    sah (apply_mul_of_mem_vanishingCocycles hx) δ⁻¹ g
      (apply_eq_zero_of_mem_vanishingCocycles hx (.inr h_comm_mem))
  simpa [hδ, hx_tors, sub_smul, cyclotomicPowDirichlet_smul_eq_self hg] using h_sah

/-- Let `x ∈ component l e ψ ν` be killed by `m`, let `φ` fix the `N m`-th roots of unity, and let
`σ` act on them by `u ∈ (ℤ/N m)ˣ`. Then `x (σ⁻¹ φ σ) = (u ^ e ψ(u)) • x φ`. -/
private lemma apply_conj_eq_smul_of_cyclotomicCharMod_eq {x : Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)}
    (hx : x ∈ component l e ψ ν) (hx_tors : ∀ g : Gal(Ω/ℚ), m • x g = 0) {φ σ : Gal(Ω/ℚ)}
    (hφ : φ ∈ cycloGalGroup (N * m)) {u : (ZMod (N * m))ˣ}
    (hσ : cyclotomicCharMod Ω (N * m) σ = u) :
    x (σ⁻¹ * φ * σ⁻¹⁻¹) = (u.val.val ^ e * ψ u.val.val : O) • x φ := by
  -- The cocycle rule gives `x (σ⁻¹ φ σ) = Υ⁻¹ (σ⁻¹) • x φ = Υ σ • x φ` for `Υ = cyc^e ψ`, as `φ`
  -- acts trivially.
  have h_fix : ((cyclotomicPowDirichlet l e ψ)⁻¹ φ).val • x σ⁻¹⁻¹ = x σ⁻¹⁻¹ := by
    simp [cyclotomicPowDirichlet_smul_eq_self hφ (hx_tors _)]
  have h_cyc : (cyclotomicCharMod Ω (N * m) σ).val = (u.val.val : ℕ) := by simp [hσ]
  rw [cocycle_conj_eq_smul (apply_mul_of_mem_vanishingCocycles hx) h_fix]
  simpa using cyclotomicPowDirichlet_smul h_cyc (hx_tors φ)

/-- Let `s u ∈ Gal(Ω/ℚ)` act on the `N m`-th roots of unity by `u ∈ (ℤ/N m)ˣ`, and let the
decomposition group of the place `B` fix them. If `w u` is a place of `ℚ(μ_{N m})` below
`(s u)⁻¹ • B` for each `u`, then the places `w u` are pairwise distinct. -/
private lemma injective_of_forall_isPlaceOver_inv_smul {s : (ZMod (N * m))ˣ → Gal(Ω/ℚ)}
    (hs : ∀ u : (ZMod (N * m))ˣ, cyclotomicCharMod Ω (N * m) (s u) = u)
    (dec_B : decompGroup Gal(Ω/ℚ) B ≤ cycloGalGroup (N * m))
    {w : (ZMod (N * m))ˣ → FinPlace (fixedFieldOf (cycloGalGroup (N * m)))}
    (hw : ∀ u : (ZMod (N * m))ˣ, IsPlaceOver ((s u)⁻¹ • B) (w u)) :
    Function.Injective w := by
  -- If `w u = w t`, some `g` over ℚ(μ_{N m}) carries `(s t)⁻¹ • B` to `(s u)⁻¹ • B`. Then
  -- `s u * g * (s t)⁻¹` fixes `B`, so it fixes the roots of unity, and `u = t`.
  intro u t hut
  obtain ⟨g, hg⟩ : ∃ g : cycloGalGroup (N * m), (g : Gal(Ω/ℚ)) • (s t)⁻¹ • B = (s u)⁻¹ • B :=
    (hw t).exists_smul (cycloGalGroup (N * m)) (by simpa only [hut] using hw u)
  have h_dec : s u * g * (s t)⁻¹ ∈ decompGroup Gal(Ω/ℚ) B :=
    MulAction.mem_stabilizer_iff.2 (by simp [mul_smul, hg])
  simpa [mem_ker.1, mul_inv_eq_one, hs] using dec_B h_dec

/-- Let `v` be a place of `ℚ` such that every place of `Ω` at which `v.q` is not a unit lies over
`v`, and let `B` be such a place. Let `s u ∈ Gal(Ω/ℚ)` act on the `N m`-th roots of unity by `u`,
and let `w u` be a place of `ℚ(μ_{N m})` below `(s u)⁻¹ • B`. Then every place `t` of `ℚ(μ_{N m})`
at which `v.q` is not a unit is one of the `w u`. -/
private lemma mem_range_of_valuation_lt_one {v : FinPlace ℚ}
    (over_v : ∀ A : ClosurePlace, A.valuation (v.q : Ω) < 1 → IsPlaceOver A v)
    (hB : B.valuation (v.q : Ω) < 1) {s : (ZMod (N * m))ˣ → Gal(Ω/ℚ)}
    (hs : ∀ u : (ZMod (N * m))ˣ, cyclotomicCharMod Ω (N * m) (s u) = u)
    {w : (ZMod (N * m))ˣ → FinPlace (fixedFieldOf (cycloGalGroup (N * m)))}
    (hw : ∀ u : (ZMod (N * m))ˣ, IsPlaceOver ((s u)⁻¹ • B) (w u))
    {t : FinPlace (fixedFieldOf (cycloGalGroup (N * m)))}
    (ht : (placeOver t).valuation (v.q : Ω) < 1) :
    t ∈ Set.range w := by
  -- Some `σ` carries a place above `t` to `B`. With `u` the action of `σ` on the roots of unity,
  -- `(s u)⁻¹ * σ` fixes them, so `(s u)⁻¹ • B` also lies above `t`, and `t = w u`.
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(Ω/ℚ), σ • placeOver t = B :=
    (over_v _ ht).exists_smul Gal(Ω/ℚ) (over_v B hB)
  let u : (ZMod (N * m))ˣ := cyclotomicCharMod Ω (N * m) σ
  let g : cycloGalGroup (N * m) := ⟨(s u)⁻¹ * σ, (eq_iff _).1 (hs u).symm⟩
  have h_over_g : IsPlaceOver (((s u)⁻¹ * σ : Gal(Ω/ℚ)) • placeOver t) t :=
    t.isPlaceOver_placeOver.smul g
  have h_over : IsPlaceOver ((s u)⁻¹ • B) t := by simpa [← hσ, smul_smul] using h_over_g
  exact ⟨u, (hw u).unique h_over⟩

/-- Artin reciprocity over `K = ℚ(μ_{N m})` at a prime `q ≡ 1 mod N m`, with `φ` a Frobenius at `B`
above `q`. The space `component l e ψ ν` consists of cocycles `Gal(Ω/ℚ) → O/l^ν` for `(cyc^e ψ)⁻¹`
under local conditions, including vanishing at `cmConj` and on inertia over `ℚ(μ_N)` away from `l`.
Let `x` in it be killed by `m`, and let `a ≡ 1 mod N` be prime to `l`. Let `y ∈ Kˣ` be, at each
place prime to `l q`, a unit times the `m`-th power of an element fixed by inertia, unless `x` kills
the decomposition group there. With `s u` acting on `μ_{N m}` by `u`, the orders `k u` of `s u • y`
at `B`, weighted by `u ^ e ψ(u)`, sum to a scalar killing `2 (a ^ e - 1) x φ`. -/
lemma artin_reciprocity_of_mem_component {a : ℕ} (ha : l.Coprime a) (ha_one : a ≡ 1 [MOD N])
    (hB : B.valuation q < 1) (hφ : IsFrob B q φ) {x : Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)}
    (hx : x ∈ component l e ψ ν) (hq_one : q ≡ 1 [MOD N * m])
    (hx_tors : ∀ g : Gal(Ω/ℚ), m • x g = 0) {y : DiscreteUnits Ω}
    (hy : ∀ g : cycloGalGroup (N * m), galUnitsRep g y = y)
    (h_away : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) = 1 → A.valuation q = 1 →
      (∃ r : DiscreteUnits Ω,
        A.valuation (y - m • r).toMul = 1 ∧
        ∀ i ∈ inertiaGroup (cycloGalGroup (N * m)) A, galUnitsRep i r = r) ∨
        ∀ g ∈ decompGroup Gal(Ω/ℚ) A, x g = 0)
    {s : (ZMod (N * m))ˣ → Gal(Ω/ℚ)}
    (hs : ∀ u : (ZMod (N * m))ˣ, cyclotomicCharMod Ω (N * m) (s u) = u) :
    ∃ k : (ZMod (N * m))ˣ → ℤ,
      -- (a) `k u` is the order at `B` of the conjugate of `y` by `s u`
      (∀ u : (ZMod (N * m))ˣ, ordRat ℚ B (galUnitsRep (s u) y) = k u) ∧
      -- (b) the weighted sum of these orders kills `2 (a ^ e - 1) • x φ`
      (∑ u : (ZMod (N * m))ˣ, k u * (u.val.val ^ e * ψ u.val.val)) • (2 * (a ^ e - 1) : O) • x φ =
        0 := by
  -- Over `F = ℚ(μ_{N m})`, with group `G`, the map `g ↦ lam (d • x g)` is a character `χ` for each
  -- `lam` with values in `ℚ/ℤ`. Apply Artin's law `sum_ord_smul_frob_eq_zero` to `χ` and `y`: only
  -- the places above `q`, which lie below the conjugates `(s u)⁻¹ • B`, contribute.
  set d : O := 2 * (a ^ e - 1)
  let G : Subgroup Gal(Ω/ℚ) := cycloGalGroup (N * m)
  let F : IntermediateField ℚ Ω := fixedFieldOf G
  -- `v` is the place of `ℚ` at `q`; from here on `q` is `v.q`.
  obtain ⟨v, ⟨rfl, -⟩, -, over_v⟩ := exists_rat_place_of_prime (p := q) (Fact.out : q.Prime)
  -- `y` is fixed by `G`, so it comes from `Fˣ`; from here on `y` is that element of `Fˣ`.
  obtain ⟨y, rfl⟩ : ∃ y₀ : Fˣ, (ofBase G Ω (Additive.ofMul y₀) : DiscreteUnits Ω) = y :=
    ((ofBase_bijective G).surjective ⟨y, hy⟩).imp fun _ ↦ congrArg Subtype.val
  -- `q` splits completely in `F`; let `w u` be the place of `F` below `(s u)⁻¹ • B`.
  have dec_B : decompGroup Gal(Ω/ℚ) B ≤ G := decompGroup_le_cycloGalGroup hB hq_one
  have conj_over (u : (ZMod (N * m))ˣ) : IsPlaceOver ((s u)⁻¹ • B) v := (over_v B hB).smul (s u)⁻¹
  choose w hw _ using fun u ↦ (conj_over u).exists_above (L := F)
  have split (u : (ZMod (N * m))ˣ) :
      FinPlace.q (w u) = v.q ∧ ordRat F ((s u)⁻¹ • B) = ordRat ℚ ((s u)⁻¹ • B) :=
    ((conj_over u).ramification_in_tower G (hw u)).1
      (decompGroup_le_cycloGalGroup (conj_over u).valuation_q_lt_one hq_one)
  refine ⟨fun u ↦ -((w u).valuation F y).log, fun u ↦ ?_,
    eq_zero_of_forall_hom_eq_zero fun lam ↦ ?_⟩
  · change ordRat ℚ B (unitsRep (s u) (ofBase G Ω (Additive.ofMul y) : DiscreteUnits Ω)) =
      -((w u).valuation F y).log
    simpa [split, ← (conj_over u).ordRat_smul (s u)] using (hw u).ordRat_ofBase (Γ := G) y
  have h_lc : IsLocallyConstant fun g : Gal(Ω/ℚ) ↦ lam (d • x g) :=
    (isLocallyConstant_of_mem_vanishingCocycles hx).comp fun z ↦ lam (d • z)
  let χ : QZChar G := ⟨fun g ↦ lam (d • x g), h_lc.continuous.comp continuous_subtypeVal,
    fun g h ↦ by simp [apply_mul_of_mem_vanishingCocycles hx,
      cyclotomicPowDirichlet_smul_eq_self g.prop, hx_tors]⟩
  have torsion : m • χ = 0 := by
    ext
    simp [χ, ← map_nsmul, smul_comm, hx_tors]
  -- `χ` kills complex conjugations `σ`, since `2 • x σ = 0` and `2 ∣ d`.
  have conj_zero (σ : G) (hσ : IsComplexConj σ) : χ.val σ = 0 := by
    have hσ_sq : (σ : Gal(Ω/ℚ)) * σ = 1 := by simp [← Subgroup.coe_mul, hσ.mul_self]
    -- The cocycle rule evaluates `x (σ * (σ * σ)) = x σ` as `3 • x σ = x σ`.
    have h_val : x (σ * (σ * σ) : Gal(Ω/ℚ)) = x σ := by rw [hσ_sq, mul_one]
    have h_two : (2 : O) • x σ = 0 := by
      simpa [apply_mul_of_mem_vanishingCocycles hx, hx_tors, two_smul,
        cyclotomicPowDirichlet_smul_eq_self σ.prop] using h_val
    simp [χ, d, mul_comm (2 : O), mul_smul, h_two]
  -- Above `l`, `χ` kills the decomposition group, since `(a ^ e - 1) • x g = 0` there.
  have dec_zero (A : ClosurePlace) (hA : A.valuation l < 1) (g : G)
      (hg : (g : Gal(Ω/ℚ)) ∈ decompGroup Gal(Ω/ℚ) A) : χ.val g = 0 := by
    simp [χ, d, mul_smul,
      pow_sub_one_smul_apply_eq_zero_of_mem_decompGroup ha ha_one hx hx_tors hA g.prop hg]
  -- `χ` is unramified: off `l`, `x` vanishes on inertia over `ℚ(μ_N)`.
  have unramified {A : ClosurePlace} {t : FinPlace ℚ} (hA : IsPlaceOver A t) (g : G)
      (hg : g ∈ inertiaGroup G A) : χ.val g = 0 := by
    rcases (A.valuation_le_one l).eq_or_lt with h | h
    · simp [χ, apply_eq_zero_of_mem_inertiaGroup_of_valuation_eq_one hx hA h g.prop hg]
    · exact dec_zero A h g (IsFrob.mem_decompGroup hg)
  -- The places `w u` are all the places of `F` above `q`.
  have unit_q (t : FinPlace F) (ht : t ∉ Set.range w) : (placeOver t).valuation v.q = 1 :=
    eq_of_le_of_not_lt (by simp) fun h ↦ ht (mem_range_of_valuation_lt_one over_v hB hs hw h)
  have hφ_G : φ ∈ G := dec_B hφ.mem_decompGroup
  let frob u : G := ⟨(s u)⁻¹ * φ * (s u)⁻¹⁻¹, (normal_ker _).conj_mem _ hφ_G _⟩
  -- The conjugate `frob u` of `φ` is a Frobenius element at `(s u)⁻¹ • B`, above `w u`.
  have frob_isFrob (u : (ZMod (N * m))ˣ) : IsFrob ((s u)⁻¹ • B) (w u).q (frob u) := by
    rw [(split u).left]
    exact hφ.conj (s u)⁻¹
  have reciprocity : ∑ u, -((w u).valuation F y).log • χ.val (frob u) = 0 := by
    -- `χ` kills complex conjugations, hence the Artin symbol of `y`.
    refine sum_ord_smul_frob_eq_zero torsion
      (abelianLift_artinMap_principalIdele_eq_one χ y conj_zero)
      (injective_of_forall_isPlaceOver_inv_smul hs dec_B hw) hw frob_isFrob
      (fun u ↦ unramified (conj_over u)) fun t ht ↦ ?_
    -- At another place either `χ` kills the decomposition group, or `y` is a unit times an
    -- `m`-th power of an element fixed by inertia.
    have h_over : IsPlaceOver (placeOver t) t := t.isPlaceOver_placeOver
    rcases ((placeOver t).valuation_le_one l).eq_or_lt with h | h
    · rcases h_away _ h (unit_q t ht) with h_unit | h_dec
      · exact .inr ⟨h_unit, unramified h_over.isPlaceOver_below⟩
      · exact .inl ((h_over.artinAt_trivial_iff_decompGroup_le χ).2
          (fun g hg ↦ show χ.val g = 0 by simp [χ, h_dec g hg]) _)
    · exact .inl ((h_over.artinAt_trivial_iff_decompGroup_le χ).2 (dec_zero _ h) _)
  -- Each `x (frob u)` is `(u ^ e * ψ u) • x φ`, so `reciprocity` is the claim.
  have frob_val (u : (ZMod (N * m))ˣ) : x (frob u) = (u.val.val ^ e * ψ u.val.val : O) • x φ :=
    apply_conj_eq_smul_of_cyclotomicCharMod_eq hx hx_tors hφ_G (hs u)
  rw [← reciprocity]
  simp [sum_smul, χ, frob_val, smul_comm d, mul_smul, ← zsmul_eq_mul]

/-- Hilbert 90 for a cocycle read through `L : M →+ Ωˣ`. Let `κ` be a cocycle for `cyc^(e+1) ψ` with
values in `M`, killed by `l`. Then on the Galois group over ℚ(μ_{N l}) the map `g ↦ L (κ g)` is a
coboundary: `L (κ g) = g • r - r` for some `r ∈ Ωˣ` (the group `Ωˣ` is written additively). -/
private lemma exists_apply_eq_galUnitsRep_sub {κ : Gal(Ω/ℚ) → M} {s : Set Gal(Ω/ℚ)}
    (hκ : κ ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) M s)
    (hκ_tors : ∀ g : Gal(Ω/ℚ), l • κ g = 0) (L : M →+ DiscreteUnits Ω) :
    ∃ r : DiscreteUnits Ω, ∀ g : cycloGalGroup (N * l), L (κ g) = galUnitsRep g r - r := by
  have h_lc : IsLocallyConstant (L ∘ κ) := (isLocallyConstant_of_mem_vanishingCocycles hκ).comp L
  refine hilbert90_unitsRep ⟨_, h_lc.continuous.comp continuous_subtypeVal, fun g h ↦ ?_⟩
  -- `g` fixes the root of unity `L (κ h)` and acts trivially on `κ h`.
  change L (κ (g * h)) = L (κ g) + unitsRep (g : Gal(Ω/ℚ)) (L (κ h))
  rw [cyclotomicCharMod_eq_one_iff.1 g.property]
  · simp [hκ_tors, apply_mul_of_mem_vanishingCocycles hκ,
    cyclotomicPowDirichlet_smul_eq_self g.property]
  · simp [mul_smul, ← map_nsmul, hκ_tors]

/-- Let `z` be an element of `M`, let `b` be a basis of `O ∙ z` over `ZMod l`, and let `j ∈ ZMod l`.
Suppose that for every unit `u` modulo `N l` the vector with coordinates `m i u * j` in the basis
`b`, scaled by `u ^ e ψ(u)`, is `z`. Suppose also that each weighted sum `∑_u m i u u ^ e ψ(u)`
kills a nonzero `c`, and that the totient of `N l` is a unit of `O`. Then `z = 0`. -/
private lemma eq_zero_of_forall_smul_equivFun_symm_eq {z : M} [Module (ZMod l) (O ∙ z)]
    (b : Module.Basis (Fin (Module.finrank (ZMod l) (O ∙ z))) (ZMod l) (O ∙ z))
    (m : Fin (Module.finrank (ZMod l) (O ∙ z)) → (ZMod (N * l))ˣ → ℤ) (j : ZMod l)
    (h_coords : ∀ u : (ZMod (N * l))ˣ,
      (u.val.val ^ e * ψ u.val.val) • b.equivFun.symm (m · u * j) = z)
    {Y : Type} [AddCommGroup Y] [Module O Y] {c : Y} (hc : c ≠ 0)
    (h_kill : ∀ i : Fin (Module.finrank (ZMod l) (O ∙ z)),
      (∑ u : (ZMod (N * l))ˣ, m i u * (u.val.val ^ e * ψ u.val.val : O)) • c = 0)
    (h_totient : IsUnit ((N * l).totient : O)) :
    z = 0 := by
  -- The weighted sums kill `c ≠ 0`, so they lie in the maximal ideal. Summing `h_coords` over the
  -- units `u` gives `t • z = φ(N l) • z` for some `t` in the maximal ideal.
  obtain ⟨t, t_mem, ht⟩ : ∃ t ∈ maximalIdeal O,
      t • z = ∑ i, (∑ u, m i u * (u.val.val ^ e * ψ u.val.val)) • ((j • b i : O ∙ z) : M) :=
    mem_smul_span_singleton.1 <| sum_mem fun i _ ↦
      (maximalIdeal O).smul_mem_smul (fun h ↦ hc (h.smul_eq_zero.1 (h_kill i))) (j • b i).prop
  have unit : IsUnit (t - (N * l).totient) :=
    by_contra fun h ↦ (sub_mem_iff_right _ t_mem).1 h h_totient
  have sum_coords : ∑ u : (ZMod (N * l))ˣ,
      (((u.val.val ^ e * ψ u.val.val) • b.equivFun.symm (m · u * j) : O ∙ z) : M) =
        ∑ u : (ZMod (N * l))ˣ, z :=
    sum_congr rfl fun u _ ↦ h_coords u
  rw [← unit.smul_eq_zero, sub_smul, sub_eq_zero, ht]
  simpa [smul_sum, sum_smul, sum_comm (γ := _ˣ), ← zsmul_eq_mul, Nat.cast_smul_eq_nsmul,
    smul_comm (_ : O)] using sum_coords

/-- Reciprocity modulo `l`, when the totient of `N l` is a unit of `O`. The space
`component l e ψ ν` consists of cocycles `Gal(Ω/ℚ) → O/l^ν` for `(cyc^e ψ)⁻¹` under local
conditions, including vanishing at `cmConj` and on inertia over `ℚ(μ_N)` away from `l`. Let `φ` be a
Frobenius at `B` above a prime `q ≡ 1 mod N l`. Let `l` kill `x ∈ component l e ψ ν` and a cocycle
`κ` for `cyc ^ (e + 1) ψ` zero on `inertiaOff N l T`: the elements over `ℚ(μ_N)` in the inertia
group of a place above neither `l` nor a prime of `T`. Let each place prime to `q` lie above no
prime of `T`, or have its decomposition group killed by `x`. If `2 (a ^ e - 1) x φ ≠ 0` for some
`a ≡ 1 mod N` prime to `l`, then `κ` vanishes on the inertia group of `B`. -/
lemma reciprocity_mod_ell {a : ℕ} (ha : l.Coprime a) (ha_one : a ≡ 1 [MOD N])
    (hB : B.valuation q < 1) (hφ : IsFrob B q φ) {x : Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)}
    (hx : x ∈ component l e ψ ν) [Finite M] (h_totient : IsUnit ((N * l).totient : O))
    (hq_one : q ≡ 1 [MOD N * l]) (hx_tors : l • x = 0) {κ : Gal(Ω/ℚ) → M} {T : Finset Nat.Primes}
    (hκ : κ ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) M (inertiaOff N l T))
    (hκ_tors : ∀ g : Gal(Ω/ℚ), l • κ g = 0) (hτ : τ ∈ inertiaGroup Gal(Ω/ℚ) B)
    (h_away : ∀ A : ValuationSubring Ω, A.valuation (q : Ω) = 1 →
      (∀ r ∈ T, ¬A.valuation r < 1) ∨ ∀ g ∈ decompGroup Gal(Ω/ℚ) A, x g = 0)
    (h_ne : (2 * (a ^ e - 1) : O) • x φ ≠ 0) :
    κ τ = 0 := by
  -- Kummer theory turns each coordinate of `κ` in the `𝔽_l`-space `O ∙ κ τ` into an element
  -- `l • r i` of `ℚ(μ_{N l})`; the orders `m i u` at `B` of its conjugates give the coordinates of
  -- `κ τ`. By `artin_reciprocity_of_mem_component` their weighted sums lie in the maximal ideal, so
  -- `κ τ` is killed by a unit.
  have h_zmodModule : Module (ZMod l) (O ∙ κ τ) :=
    AddCommGroup.zmodModule (by simp [mem_span_singleton, smul_comm, hκ_tors])
  let b := Module.finBasis (ZMod l) (O ∙ κ τ)
  have τ_fix : cyclotomicCharMod Ω (N * l) τ = 1 :=
    mem_ker.1 (decompGroup_le_cycloGalGroup hB hq_one (IsFrob.mem_decompGroup hτ))
  obtain ⟨v, hv, -, ord_q⟩ := exists_isPlaceOver_prime hB
  choose σ hσ using cyclotomicCharMod_surjective (N * l)
  -- `μ` identifies `ℤ/l` with the `l`-th roots of unity; `τ` moves an `l`-th root `π` of `q`
  -- by `μ j`.
  set μ : ZMod l →+ DiscreteUnits Ω := (rootPowHom Ω l).val with hμ
  obtain ⟨-, μ_range⟩ := (rootPowHom Ω l).property
  obtain ⟨π, hπ⟩ := (ofNeZero (q : Ω) (NeZero.ne _)).exists_nsmul (NeZero.ne l)
  obtain ⟨j, hj⟩ : galUnitsRep τ π - π ∈ μ.range :=
    (μ_range _).2 (DiscreteUnits.ext (by simp [smul_sub, ← map_nsmul, hπ]))
  -- Extend the coordinates, read in `μ_l`, to `M`; by Hilbert 90 `L i ∘ κ` is a coboundary.
  have extend i : ∃ L : M →+ DiscreteUnits Ω, ∀ y hy, L y = μ (b.repr ⟨y, hy⟩ i) := by
    simpa [DFunLike.ext_iff] using
      exists_extend (O ∙ κ τ).subtype.toAddMonoidHom (μ.comp (b.coord i)) (by aesop_cat)
  choose L hL using extend
  have kummer i :
      ∃ r : DiscreteUnits Ω, ∀ g : cycloGalGroup (N * l), L i (κ g) = galUnitsRep g r - r :=
    exists_apply_eq_galUnitsRep_sub hκ hκ_tors (L i)
  choose r hr using kummer
  have reciprocity i : ∃ m : (ZMod (N * l))ˣ → ℤ,
      (∀ u, ordRat ℚ B (galUnitsRep (σ u) (l • r i)) = m u) ∧
      (∑ u, m u * (u.val.val ^ e * ψ u.val.val)) • (2 * (a ^ e - 1) : O) • x φ = 0 := by
    refine artin_reciprocity_of_mem_component ha ha_one hB hφ hx hq_one (congrFun hx_tors)
      (fun g ↦ ?_)
      (fun A hAl hAq ↦ ?_) hσ
    · simp [← add_eq_of_eq_sub (hr i g), ← map_nsmul, hκ_tors]
    · -- At a place off `l` and `T` the cocycle `κ` kills inertia, which therefore fixes `r i`.
      refine (h_away A hAq).imp_left fun off_T ↦ ⟨r i, by simp, fun g hg ↦ ?_⟩
      have hκ_g : κ g = 0 := apply_eq_zero_of_mem_vanishingCocycles hκ
        ⟨A, ⟨cyclotomicCharMod_eq_one_of_dvd (N.dvd_mul_right l) g.prop, hAl, hg⟩, off_T⟩
      simp [← sub_eq_zero, ← hr, hκ_g]
  choose m hm m_sum using reciprocity
  -- For each `u`, the `m i u * j` are the coordinates of `κ τ` up to the weight `u ^ e * ψ u`.
  have coords (u : (ZMod (N * l))ˣ) :
      (u.val.val ^ e * ψ u.val.val) • b.equivFun.symm (m · u * j) = κ τ := by
    have cyc_u : (cyclotomicCharMod Ω (N * l) (σ u)).val = u.val.val := by simp [hσ]
    have κ_conj :
        κ ((σ u)⁻¹ * τ * (σ u)⁻¹⁻¹) = (cyclotomicPowDirichlet l (e + 1) ψ (σ u)⁻¹).val • κ τ :=
      cocycle_conj_eq_smul (apply_mul_of_mem_vanishingCocycles hκ)
        (cyclotomicPowDirichlet_smul_eq_self τ_fix (hκ_tors _)).left
    let y : O ∙ κ τ := ⟨_, mem_span_singleton.2 ⟨_, κ_conj.symm⟩⟩
    -- `l • (m i u • π - σ u • r i)` is a unit at `B`, so `τ` moves `m i u • π - σ u • r i` by a
    -- principal unit; it moves it by the root of unity `μ (m i u * j - u * b.repr y i)`.
    have coord i : m i u * j = b.equivFun (u.val.val • y) i := by
      have unit : B.valuation (l • (m i u • π - galUnitsRep (σ u) (r i))).toMul.val = 1 := by
        simp [↓← hv.ordRat_eq_zero_iff, smul_comm, hπ, ord_q, smul_sub, ← hm]
      refine eq_of_mem_principalUnits
        (hq_one.of_mul_left.coprime_of_modEq_one.valuation_eq_one hB) ?_
      -- `using!` matches the conjugation by `σ u` inside `galUnitsRep`.
      simpa [y, smul_smul, ← hμ, hj, τ_fix, hr _ ⟨_, _⟩, ← zsmul_eq_mul, smul_sub, ↓map_nsmul, ← hL,
        ← cyclotomicCharMod_eq_of_dvd _ cyc_u, sub_sub_sub_comm, map_cyclotomicCharMod_mul] using!
        hτ.sub_nsmul_mem_principalUnits unit
    rw [b.equivFun.symm_apply_eq.2 (funext coord)]
    calc (u.val.val ^ e * ψ u.val.val : O) • u.val.val • y.val
        = (cyclotomicPowDirichlet l (e + 1) ψ (σ u)).val • y.val := by
          rw [← Nat.cast_smul_eq_nsmul O, smul_smul, mul_right_comm, ← pow_succ,
            cyclotomicPowDirichlet_smul cyc_u (hκ_tors _)]
      _ = κ τ := by simp [y, ↓κ_conj, smul_smul]
  -- By `m_sum i` the weighted sums kill the nonzero `2 (a ^ e - 1) • x φ`; with `coords` this
  -- makes `κ τ` killed by a unit.
  exact eq_zero_of_forall_smul_equivFun_symm_eq b m j coords h_ne m_sum h_totient

end ReciprocityLaw

/-!
## Stickelberger and Kolyvagin bounds for the components

The proofs of `New.OddPart.nsmul_component_eq_zero` and
`New.OddPart.exists_detecting_points_component` use Chebotarev's theorem
(`New.OddPart.exists_isFrob_notMem`) to find a Frobenius element at which a cocycle does not vanish.
They also use the reciprocity laws.
-/

section ComponentBound

open NeZero ZMod Selmer Ideal.Quotient Function QZ Finset Nat HasEnoughRootsOfUnity

variable {O : Type} [CommRing O]
  {N l e X ν : ℕ} [NeZero N] [L : Fact l.Prime] [PadicIntegerRing O l] {ψ : DirichletCharacter O N}

/-- If neither of the open subgroups `U`, `V` contains the Galois group over `ℚ(ζ_m)`, then some
Frobenius element at a place above a prime `q ≡ 1 mod m` lies outside both. -/
lemma exists_isFrob_notMem (m : ℕ) [NeZero m] {U V : OpenSubgroup Gal(Ω/ℚ)}
    (hU : ¬cycloGalGroup m ≤ U) (hV : ¬cycloGalGroup m ≤ V) :
    ∃ q : Primes, q ≡ 1 [MOD m] ∧
      ∃ (A : ClosurePlace) (σ : Gal(Ω/ℚ)),
        A.valuation (q : Ω) < 1 ∧ IsFrob A q σ ∧ σ ∉ U ∧ σ ∉ V := by
  -- A group is not the union of two proper subgroups, so the open set below is not empty.
  have h_ne : ((cycloGalGroup m : Set Gal(Ω/ℚ)) \ (U ∪ V)).Nonempty :=
    Set.sdiff_nonempty.2 fun h_sub ↦ (SubgroupClass.subset_union.1 h_sub).elim hU hV
  -- Chebotarev: it contains a Frobenius at a prime not dividing `m`.
  obtain ⟨v, hv, h_prime, A, hA, σ, ⟨hσ, hσ_not⟩, h_frob, -⟩ :=
    chebotarev (isOpen_ker_cyclotomicCharMod.out.sdiff (U.isClosed.union V.isClosed)) h_ne
      (finite_natCast_mem m)
  exact ⟨⟨v.q, h_prime⟩,
    (h_frob.mem_ker_cyclotomicCharMod_iff (hA.valuation_natCast_eq_one_iff.2 hv)).1 hσ,
    A, σ, hA.valuation_q_lt_one, h_frob, not_or.1 hσ_not⟩

lemma exists_place_above (r : Primes) : ∃ A : ClosurePlace, A.valuation (r : Ω) < 1 :=
  have : Fact (r : ℕ).Prime := ⟨r.prop⟩
  ⟨_, valuation_comap_intQpBar_lt_one (IsAlgClosed.lift : Ω →ₐ[ℚ] PadicAlgCl r).toRingHom⟩

/-- The function `x` on the Galois group vanishes on the decomposition group of every place above
the prime `r`. -/
def IsTrivialAbove {M : Type} [Zero M] (x : Gal(Ω/ℚ) → M) (r : Primes) : Prop :=
  ∀ A : ClosurePlace, A.valuation (r : Ω) < 1 → ∀ g ∈ decompGroup Gal(Ω/ℚ) A, x g = 0

omit [PadicIntegerRing O l] in
/-- The sum `∑ ⌊a x / (N lⁿ⁺¹)⌋ x ^ e ψ(x)` over `x < N lⁿ⁺¹` splits into its part over the units
modulo `N lⁿ⁺¹` and `l ^ e ψ(l)` times the same sum at level `N lⁿ`. -/
lemma sum_range_eq_sum_units_add (a n : ℕ) :
    ∑ x ∈ range (N * l ^ (n + 1)), (a * x / (N * l ^ (n + 1)) : ℕ) * (x ^ e * ψ x : O) =
      ∑ u : (ZMod (N * l ^ (n + 1)))ˣ,
          (a * ZMod.val u.val / (N * l ^ (n + 1)) : ℕ) *
            (ZMod.val u.val ^ e * ψ (ZMod.val u.val) : O) +
        l ^ e * ψ l * ∑ x ∈ range (N * l ^ n), (a * x / (N * l ^ n) : ℕ) * (x ^ e * ψ x : O) := by
  -- A number below `N lⁿ⁺¹` at which `ψ` is not zero is a unit or a multiple of `l`.
  have h_level : N * l ^ (n + 1) = l * (N * l ^ n) := by ring
  have h_lt (y : ℕ) : l * y < N * l ^ (n + 1) ↔ y < N * l ^ n := by simp [h_level, L.out.pos]
  have h_inj : Injective
      (Sum.elim (fun u : (ZMod (N * l ^ (n + 1)))ˣ ↦ u.val.val) fun y ↦ l * y) :=
    ((ZMod.val_injective _).comp Units.val_injective).sumElim (mul_right_injective₀ (NeZero.ne l))
      fun u y h_eq ↦ L.out.ne_one
        (eq_one_of_dvd_coprimes (val_coe_unit_coprime u) ⟨y, h_eq⟩ ⟨_, h_level⟩)
  rw [← sum_of_injOn (s := univ.disjSum (range (N * l ^ n))) _ h_inj.injOn ?_
    (fun x hx h_out ↦ ?_) fun _ _ ↦ rfl]
  · -- The term at `l y` is `l ^ e ψ(l)` times the term at `y` of level `N lⁿ`.
    have h_floor (y : ℕ) : a * (l * y) / (N * l ^ (n + 1)) = a * y / (N * l ^ n) := by
      rw [h_level, mul_left_comm, Nat.mul_div_mul_left _ _ L.out.pos]
    simp only [sum_disjSum, Sum.elim_inl, Sum.elim_inr, h_floor, mul_sum, Nat.cast_mul, map_mul]
    exact congrArg _ (sum_congr rfl fun y _ ↦ by ring)
  · -- Both kinds of numbers lie below `N lⁿ⁺¹`.
    simp [Set.MapsTo, val_lt, h_lt]
  · -- At the other numbers `ψ` is zero.
    suffices h_nonunit : ¬IsUnit (x : ZMod N) by simp [ψ.map_nonunit h_nonunit]
    refine fun h_unit ↦ h_out ?_
    by_cases h_dvd : l ∣ x
    · obtain ⟨y, rfl⟩ := h_dvd
      exact ⟨.inr y, by simpa [h_lt] using hx, rfl⟩
    · have h_cop : x.Coprime (N * l ^ (n + 1)) :=
        .mul_right ((isUnit_iff_coprime x N).1 h_unit) (L.out.coprime_pow_of_not_dvd h_dvd)
      exact ⟨.inl (unitOfCoprime x h_cop), by simpa [mod_eq_iff_lt, NeZero.ne] using hx⟩

/-- Let `O` be the integer ring of a finite extension of `ℚ_l` (`PadicIntegerRing O l`), and let `X`
have the Stickelberger property `IsStickelbergerBound N e X`: for `a ≡ 1 mod N`, for some `w` that
does not depend on `m`, `(a ^ (e + 1) - 1) X` is congruent modulo every `m` prime to `a` to `2 w`
times the Stickelberger sum at level `N m`. Let `cyc ^ e ψ` be odd (`hc`: its value at the complex
conjugation `cmConj` is `-1`), let `e ≠ 0`, and let `a ≡ 1 mod N` be prime to `l`. Then in
`O / lⁿ O` the sum of `floorDiff a (u / (N lⁿ)) u ^ e ψ(u)` over the units `u` modulo `N lⁿ` divides
`(a ^ (e + 1) - 1) X`. Here `floorDiff a t = ⌊a ⟨t⟩⌋ - ⌊a ⟨-t⟩⌋`, where `⟨t⟩ ∈ [0, 1)` represents
`t ∈ ℚ/ℤ`. The multiples of `l` give the Euler factor `1 - l ^ e ψ(l)`, a unit modulo `lⁿ`. -/
lemma sum_floorDiff_dvd (h : IsStickelbergerBound N e X)
    (hc : cyclotomicPowDirichlet l e ψ cmConj = -1)
    (he_ne_zero : e ≠ 0) (n : ℕ) {a : ℕ} (ha : a ≡ 1 [MOD N]) (hla : l.Coprime a) :
    ((∑ x : (ZMod (N * l ^ n))ˣ, floorDiff a (ofZMod (N * l ^ n) x) *
        ((x : ZMod (N * l ^ n)).val ^ e * ψ (x : ZMod (N * l ^ n)).val) : O) :
      QuotSpan (l ^ n : O)) ∣ ((a ^ (e + 1) - 1) * X : O) := by
  -- `cmConj` inverts roots of unity, so `hc` says that `(-1) ^ e * ψ (-1) = -1`.
  have h_odd (y : ZMod N) : -((-1) ^ e * ψ y) = ψ (-y) := by
    have h_mul :
        ((cyclotomicPowDirichlet l e ψ cmConj : Oˣ) : O) * -ψ (-y) = ((-1 : Oˣ) : O) * -ψ (-y) := by
      rw [hc]
    simpa [cyclotomicPowDirichlet, isComplexConj_cmConj.cyclotomicChar_eq_neg_one,
      isComplexConj_cmConj.cyclotomicCharMod_eq_neg_one, mul_assoc, ← map_mul] using h_mul
  have h_nil : (l : QuotSpan (l ^ n : O)) ^ n = 0 := mk_singleton_self _
  rcases n with - | n
  · -- Modulo `l ^ 0 = 1` the ring is trivial.
    have h_subsingleton : Subsingleton (QuotSpan (l ^ 0 : O)) :=
      subsingleton_of_zero_eq_one (h_nil.symm.trans (pow_zero _))
    exact ⟨0, Subsingleton.elim _ _⟩
  -- `T m` is the sum of `IsStickelbergerBound` at level `N m`, and `U` is the part of `T lⁿ⁺¹`
  -- over the units modulo `N lⁿ⁺¹`.
  let T (m : ℕ) : O := ∑ x ∈ range (N * m), ↑(a * x / (N * m)) * (x ^ e * ψ x)
  let U : O := ∑ u : (ZMod (N * l ^ (n + 1)))ˣ,
    ↑(a * u.val.val / (N * l ^ (n + 1))) * (u.val.val ^ e * ψ u.val.val)
  have h_split : T (l ^ (n + 1)) = U + l ^ e * ψ l * T (l ^ n) := sum_range_eq_sum_units_add a n
  -- Modulo `lⁿ⁺¹` our sum is `2 U`: `floorDiff` is a difference of two integer parts, and `u ↦ -u`
  -- changes the sign of `u ^ e * ψ u`.
  have h_twice : ((∑ u : (ZMod (N * l ^ (n + 1)))ˣ, floorDiff a (ofZMod _ u.val) *
      (u.val.val ^ e * ψ u.val.val) : O) : QuotSpan (l ^ (n + 1) : O)) = 2 * U := by
    have h_char : ringChar (QuotSpan (l ^ (n + 1) : O)) ∣ N * l ^ (n + 1) :=
      ringChar.dvd (by simp [h_nil])
    simp only [floorDiff, ↓← map_neg, ofZMod_apply, QZ.fracRep_mk, mul_div, mod_eq_of_lt, val_lt,
      Int.fract_div_natCast_eq_div_natCast_mod]
    norm_cast
    simp only [Int.cast_subNatNat, sub_mul, sum_sub_distrib, map_sub, map_sum, map_mul, map_natCast,
      map_pow, two_mul, U]
    nth_rw 2 [← neg_bijective.sum_comp]
    simp [← h_odd, ← mul_assoc, ← mul_pow, h_char]
  -- Use `IsStickelbergerBound` at the levels `lⁿ⁺¹` and `lⁿ`. As `e ≠ 0`, the factor `l ^ e` turns
  -- the congruence modulo `lⁿ` into one modulo `lⁿ⁺¹`.
  have hψ_odd : ψ (-1) = -(-1) ^ e := by simp [← h_odd]
  obtain ⟨w, hw⟩ := h.exists_natCast_dvd_sub_mul_sum ha O ψ hψ_odd
  obtain ⟨x, hx⟩ : (l ^ (n + 1) : O) ∣ (a ^ (e + 1) - 1) * X - 2 * w * T (l ^ (n + 1)) := by
    simpa only [Nat.cast_pow] using hw (l ^ (n + 1)) (hla.pow_left (n + 1))
  obtain ⟨y, hy⟩ : (l ^ n : O) ∣ (a ^ (e + 1) - 1) * X - 2 * w * T (l ^ n) := by
    simpa only [Nat.cast_pow] using hw (l ^ n) (hla.pow_left n)
  have h_euler : ((1 - l ^ e * ψ l) * ((a ^ (e + 1) - 1) * X) : O) =
      2 * w * U + l ^ (n + 1) * (x - l ^ (e - 1) * ψ l * y) := by
    obtain ⟨e, rfl⟩ : ∃ k : ℕ, e = k + 1 := exists_eq_add_one_of_ne_zero he_ne_zero
    rw [add_tsub_cancel_right]
    linear_combination hx - l ^ (e + 1) * ψ l * hy + 2 * w * h_split
  -- The Euler factor is a unit modulo `lⁿ⁺¹`, because `l ^ e * ψ l` is nilpotent there.
  obtain ⟨G, hG⟩ : (1 - l ^ e * ψ l : QuotSpan (l ^ (n + 1) : O)) ∣ 1 := by
    have h_dvd : (1 - l ^ e * ψ l : QuotSpan (l ^ (n + 1) : O)) ∣ 1 - (l ^ e * ψ l) ^ (n + 1) :=
      one_sub_dvd_one_sub_pow _ (n + 1)
    rwa [mul_pow, pow_right_comm, h_nil, zero_pow he_ne_zero, zero_mul, sub_zero] at h_dvd
  have h_euler_mod :
      (((1 - l ^ e * ψ l) * ((a ^ (e + 1) - 1) * X) : O) : QuotSpan (l ^ (n + 1) : O)) =
        ((2 * w * U + l ^ (n + 1) * (x - l ^ (e - 1) * ψ l * y) : O) :
          QuotSpan (l ^ (n + 1) : O)) := by
    rw [h_euler]
  use w * G
  rw [h_twice]
  -- Push the reduction modulo `lⁿ⁺¹` through both equations; there `lⁿ⁺¹ = 0`.
  simp only [map_mul, map_sub, map_add, map_pow, map_natCast, map_one, map_ofNat, h_nil, zero_mul,
    add_zero] at h_euler_mod ⊢
  linear_combination G * h_euler_mod + (a ^ (e + 1) - 1) * X * hG

private lemma ne_zero_of_coprime {a : ℕ} (hla : l.Coprime a) : a ≠ 0 := by
  rintro rfl
  exact L.out.ne_one ((Nat.coprime_zero_right l).1 hla)

/-- An analogue of Stickelberger's theorem. Let `X` have the Stickelberger property
`IsStickelbergerBound N e X` (a divisibility for each prime and a congruence for the Stickelberger
sums), let `cyc ^ e ψ` be odd (its value at the complex conjugation `cmConj` is `-1`), and let
`e ≠ 0`. Then `4 X²` kills every cocycle `z` in `component l e ψ ν`, the locally constant cocycles
`Gal(Ω/ℚ) → O/l^ν` for `(cyc ^ e ψ)⁻¹` that vanish at `cmConj` and at the elements of
`Gal(Ω/ℚ(μ_N))` lying in an inertia group at a place prime to `l` or in `shaLocalSet l ℚ 1`. -/
lemma nsmul_component_eq_zero (h_bound : IsStickelbergerBound N e X)
    (hc : cyclotomicPowDirichlet l e ψ cmConj = -1) (he_ne_zero : e ≠ 0)
    {z : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)} (hz : z ∈ component l e ψ ν) :
    (4 * X * X) • z = 0 := by
  -- At a Frobenius `σ` above `p ≡ 1 mod N l ^ ν`, Artin's law for a Jacobi sum shows that the
  -- Stickelberger sum kills `2 (a ^ e - 1) z σ`, hence `2 X² z σ = 0`. If `4 X² z ≠ 0`, Chebotarev
  -- gives such a `σ` with `2 X² z σ ≠ 0`.
  by_contra h_ne
  -- The character of `z` is `-1` at `cmConj`, so `not_cycloGalGroup_le_openCocycleKer` asks for
  -- `-2 • 2 X² z ≠ 0`.
  have h_conj_zero : ((2 * X * X) • z) cmConj = 0 := by
    simp [apply_eq_zero_of_mem_vanishingCocycles hz (Set.mem_insert cmConj _)]
  have h_char : ((cyclotomicPowDirichlet l e ψ)⁻¹ cmConj : O) - 1 = -(2 : ℕ) := by norm_num [hc]
  have h_visible : ¬cycloGalGroup (N * l ^ ν) ≤ openCocycleKer (nsmul_mem hz (2 * X * X)) := by
    refine not_cycloGalGroup_le_openCocycleKer _ cmConj h_conj_zero ?_ _
    rwa [h_char, neg_smul, cast_smul_eq_nsmul, smul_smul, neg_ne_zero, ← mul_assoc, ← mul_assoc]
  obtain ⟨p, hp : p ≡ 1 [MOD N * l ^ ν], B, σ, hB : B.valuation (p : Ω) < 1, hσ : IsFrob B p σ,
      hzσ : ((2 * X * X) • z) σ ≠ 0, -⟩ :=
    exists_isFrob_notMem (N * l ^ ν) h_visible h_visible
  obtain ⟨a, ha, hla, h_dvd⟩ := h_bound.exists_modEq_one_coprime_dvd L.out
  obtain ⟨b, hX⟩ : ∃ b : ℕ, X = (a ^ e - 1) * (a ^ (e + 1) - 1) * b := h_dvd
  -- The Jacobi sum `J (1 / (N l ^ ν))` is a unit off `p`, and its conjugates have the orders
  -- `μ u = floorDiff a (u / (N l ^ ν))` at `B`.
  obtain ⟨J, hJ⟩ := exists_isJacobiFamily hB a
  have hJ_level : IsJacobiFamily p B a (N * l ^ ν) J := hJ (N * l ^ ν) hp
  have h_tors (u : ZMod (N * l ^ ν)) : (N * l ^ ν) • ofZMod (N * l ^ ν) u = 0 := by
    rw [← map_nsmul, nsmul_eq_mul, natCast_self, zero_mul, map_zero]
  have hz_tors (g : Gal(Ω/ℚ)) : l ^ ν • z g = 0 := nsmul_quot_eq_zero dvd_rfl (z g)
  have hJ_fix (g : cycloGalGroup (N * l ^ ν)) :
      galUnitsRep g (J (ofZMod (N * l ^ ν) 1)) = J (ofZMod (N * l ^ ν) 1) := by
    rw [hJ_level.galUnitsRep_apply (h_tors 1) g 1 (by simp [MonoidHom.mem_ker.1 g.prop]),
      one_nsmul]
  have hJ_away (A : ValuationSubring Ω)
      (hA_p : A.valuation (p : Ω) = 1) :
      (∃ r : DiscreteUnits Ω, A.valuation (J (ofZMod (N * l ^ ν) 1) - l ^ ν • r).toMul = 1 ∧
        ∀ i ∈ inertiaGroup (cycloGalGroup (N * l ^ ν)) A, galUnitsRep i r = r) ∨
        ∀ g ∈ decompGroup Gal(Ω/ℚ) A, z g = 0 :=
    .inl ⟨0, by simpa using hJ_level.valuation_eq_one (h_tors 1) A hA_p, fun i _ ↦ map_zero _⟩
  -- Apply Artin's law with representatives of the units modulo `N l ^ ν` in the Galois group.
  have h_reps (u : (ZMod (N * l ^ ν))ˣ) : cyclotomicCharMod Ω (N * l ^ ν)
      (surjInv (cyclotomicCharMod_surjective _) u) = u :=
    surjInv_eq (cyclotomicCharMod_surjective _) u
  obtain ⟨μ, hμ, h_law⟩ := artin_reciprocity_of_mem_component hla ha hB hσ hz hp hz_tors hJ_fix
    (fun A _ ↦ hJ_away A) h_reps
  have h_ord (u : (ZMod (N * l ^ ν))ˣ) :
      μ u = floorDiff a (ofZMod (N * l ^ ν) (u : ZMod (N * l ^ ν))) := by
    simpa [hJ_level.galUnitsRep_apply (h_tors 1) _ _ (ZMod.natCast_zmod_val _).symm, surjInv_eq,
      ← map_nsmul, hJ_level.ordRat_eq (h_tors _)] using (hμ u).symm
  -- In `O / l ^ ν`, the Stickelberger sum `t` divides `(a ^ (e + 1) - 1) X` with quotient `k`, and
  -- `X = (a ^ e - 1) (a ^ (e + 1) - 1) b`; so `k b` times Artin's law gives `2 X² z σ = 0`.
  set t : QuotSpan (l ^ ν : O) := ((∑ u : (ZMod (N * l ^ ν))ˣ,
      floorDiff a (ofZMod (N * l ^ ν) u) *
        ((u : ZMod (N * l ^ ν)).val ^ e * ψ (u : ZMod (N * l ^ ν)).val) : O) :
      QuotSpan (l ^ ν : O)) with ht
  obtain ⟨k, hk⟩ : t ∣ ((a : QuotSpan (l ^ ν : O)) ^ (e + 1) - 1) * X := by
    simpa [ht] using sum_floorDiff_dvd h_bound hc he_ne_zero ν ha hla
  have h_law_t : t * (2 * ((a : QuotSpan (l ^ ν : O)) ^ e - 1) * z σ) = 0 := by
    simpa [ht, h_ord, Algebra.smul_def, map_ofNat] using h_law
  have hX_q : (X : QuotSpan (l ^ ν : O)) =
      ((a : QuotSpan (l ^ ν : O)) ^ e - 1) * ((a : QuotSpan (l ^ ν : O)) ^ (e + 1) - 1) * b := by
    simp [hX, Nat.pos_of_ne_zero (ne_zero_of_coprime hla)]
  have h_zero : 2 * (X : QuotSpan (l ^ ν : O)) * X * z σ = 0 := by
    linear_combination k * b * h_law_t +
      2 * ((a : QuotSpan (l ^ ν : O)) ^ e - 1) * b * z σ * hk + 2 * X * z σ * hX_q
  exact hzσ (by simpa [nsmul_eq_mul] using h_zero)

omit [NeZero N] in
lemma isUnit_natCast_of_not_dvd {k : ℕ} (hk : ¬l ∣ k) : IsUnit (k : O) := by
  have h_unit : IsUnit (k : ℤ_[l]) :=
    .of_map PadicInt.toZMod _ (by simpa [natCast_eq_zero_iff] using hk)
  simpa using h_unit.map (algebraMap ℤ_[l] O)

/-- For `l > N` the number `φ (N l) = φ(N) (l - 1)` is a unit of `O`: both factors lie strictly
between `0` and `l`. -/
lemma isUnit_totient_mul (hl : N < l) : IsUnit (φ (N * l) : O) := by
  have hl_one : 1 < l := L.out.one_lt
  rw [totient_mul (N.coprime_of_lt_prime (NeZero.ne N) hl L.out).symm, totient_prime L.out,
    Nat.cast_mul]
  exact (isUnit_natCast_of_not_dvd
      (not_dvd_of_pos_of_lt (NeZero.pos _) (N.totient_le.trans_lt hl))).mul
    (isUnit_natCast_of_not_dvd (not_dvd_of_pos_of_lt (by lia) (by lia)))

/-- For `l > N` some `a ≡ 1 mod N` prime to `l` (a primitive root modulo `l`) makes `a ^ k - 1` a
unit of `O` for all `0 < k < l - 1`. -/
lemma exists_modEq_one_forall_isUnit_pow_sub_one (hl : N < l) :
    ∃ a : ℕ, a ≡ 1 [MOD N] ∧ l.Coprime a ∧
      ∀ k : ℕ, 0 < k → k < l - 1 → IsUnit (a ^ k - 1 : O) := by
  obtain ⟨b, hb⟩ : ∃ b : ZMod l, IsPrimitiveRoot b (l - 1) :=
    exists_isPrimitiveRoot (ZMod l) (l - 1)
  -- `a` is `b` modulo `l` and `1` modulo `N`.
  obtain ⟨a, hab, ha⟩ : {a : ℕ // a ≡ b.val [MOD l] ∧ a ≡ 1 [MOD N]} :=
    chineseRemainder (N.coprime_of_lt_prime (NeZero.ne N) hl L.out) b.val 1
  obtain rfl : (a : ZMod l) = b := by simpa [← natCast_eq_natCast_iff] using hab
  have hl_one : 1 < l := L.out.one_lt
  have hla : l.Coprime a := ((isUnit_iff_coprime a l).1 (hb.isUnit (by lia))).symm
  refine ⟨a, ha, hla, fun k hk hkl ↦ ?_⟩
  -- `a ^ k ≠ 1` modulo `l`, as `k` lies strictly between `0` and the order `l - 1` of `a`.
  have h_unit : IsUnit (a ^ k - 1 : ℤ_[l]) :=
    .of_map PadicInt.toZMod _ (by simpa [sub_eq_zero] using hb.pow_ne_one_of_pos_of_lt hk.ne' hkl)
  simpa using h_unit.map (algebraMap ℤ_[l] O)

/-- For `e ≠ 0` and `l > N + e + 3`, the numbers `a ^ e - 1` and `a ^ (e + 1) - 1` are units of `O`
for some `a ≡ 1 mod N` prime to `l`. -/
lemma exists_modEq_one_coprime_isUnit_pow_sub_one (he_ne_zero : e ≠ 0) (hl : N + e + 3 < l) :
    ∃ a : ℕ, a ≡ 1 [MOD N] ∧ l.Coprime a ∧
      IsUnit (a ^ e - 1 : O) ∧ IsUnit (a ^ (e + 1) - 1 : O) := by
  obtain ⟨a, ha, hla, h_pow⟩ :=
    exists_modEq_one_forall_isUnit_pow_sub_one (O := O) (show N < l by lia)
  exact ⟨a, ha, hla, h_pow e (by lia) (by lia), h_pow (e + 1) e.succ_pos (by lia)⟩

omit [Fact l.Prime] in
/-- Let `i` lie in the inertia group of a place `A` above a prime `r ≡ 1 mod N l`. Then `i` fixes
the `N`-th roots of unity, and `A` is not above `l`. The last clause repeats `hi`, so that the
conclusion has the form of the membership condition of `inertiaOff`. -/
lemma mem_cycloGalGroup_and_valuation_eq_one {r : Primes} {A : ClosurePlace} {i : Gal(Ω/ℚ)}
    (hr : r ≡ 1 [MOD N * l]) (hA : A.valuation (r : Ω) < 1) (hi : i ∈ inertiaGroup Gal(Ω/ℚ) A) :
    i ∈ cycloGalGroup N ∧ A.valuation (l : Ω) = 1 ∧ i ∈ inertiaGroup Gal(Ω/ℚ) A :=
  ⟨decompGroup_le_cycloGalGroup hA hr.of_mul_right (IsFrob.mem_decompGroup hi),
    hr.of_mul_left.coprime_of_modEq_one.valuation_eq_one hA, hi⟩

/-- Let `O` be the integer ring of a finite extension of ℚ_l, `ψ` a Dirichlet character mod `N` with
values in `O`, and `component l e ψ ν` the locally constant cocycles for `(cyc ^ e ψ)⁻¹` on Gal(Ω/ℚ)
with values in `O / l ^ ν` that vanish at `cmConj` and at those elements of Gal(Ω/ℚ(μ_N)) lying in
an inertia group at a place prime to `l` or in `shaLocalSet l ℚ 1`. At a place `A` above a prime
`r ≡ 1 mod N l` (`A.valuation r < 1`) there is a Frobenius element `σ` with this property: every
cocycle `x` in `component l e ψ ν` that is killed by `l` and zero at `σ` is trivial above `r`
(`IsTrivialAbove x r`: it vanishes on the decomposition group of every place above `r`). -/
lemma exists_isFrob_forall_isTrivialAbove {r : Primes} {A : ClosurePlace} (hr : r ≡ 1 [MOD N * l])
    (hA : A.valuation (r : Ω) < 1) :
    ∃ σ : Gal(Ω/ℚ), IsFrob A r σ ∧
      ∀ x ∈ component l e ψ ν, l • x = 0 → x σ = 0 → IsTrivialAbove x r := by
  obtain ⟨v, ⟨hv : v.q = r, -⟩, -,
      h_over : ∀ A : ClosurePlace, A.valuation (r : Ω) < 1 → IsPlaceOver A v⟩ :=
    exists_rat_place_of_prime r.prop
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(Ω/ℚ), IsFrob A v.q σ := (h_over A hA).exists_isFrob Gal(Ω/ℚ)
  refine ⟨σ, by rwa [← hv], fun x hx h_tors hxσ B hB ↦ ?_⟩
  -- `B` is a conjugate `ρ • A`. The zeros of `x` form an open subgroup that contains inertia at
  -- `B` and the Frobenius element `ρ σ ρ⁻¹`, so it contains the decomposition group.
  have hBv : IsPlaceOver B v := h_over B hB
  obtain ⟨ρ, hρ⟩ := (h_over A hA).exists_smul Gal(Ω/ℚ) hBv
  have h_frob : IsFrob B v.q (ρ * σ * ρ⁻¹) := by
    rw [← hρ]
    exact hσ.conj ρ
  have h_inertia (i : Gal(Ω/ℚ)) (hi : i ∈ inertiaGroup Gal(Ω/ℚ) B) : x i = 0 := by
    obtain ⟨h_fix, h_val, -⟩ := mem_cycloGalGroup_and_valuation_eq_one hr hB hi
    have h_off_l : i ∈ inertiaAbove (placesDividing ℚ l)ᶜ :=
      ⟨v, hBv.valuation_natCast_eq_one_iff.1 h_val, B, hBv, hi⟩
    exact apply_eq_zero_of_mem_vanishingCocycles hx (.inr ⟨h_fix, .inl h_off_l⟩)
  -- `σ` fixes the `N l`-th roots of unity, so it fixes the values of `x`, which `l` kills.
  have h_conj : x (ρ * σ * ρ⁻¹) = 0 := by
    have h_fix : σ ∈ cycloGalGroup (N * l) :=
      decompGroup_le_cycloGalGroup hA hr hσ.mem_decompGroup
    have h_inv_fix : (cyclotomicPowDirichlet l e ψ σ)⁻¹.val • x ρ⁻¹ = x ρ⁻¹ :=
      (cyclotomicPowDirichlet_smul_eq_self h_fix (congrFun h_tors ρ⁻¹)).right
    rw [cocycle_conj_eq_smul (apply_mul_of_mem_vanishingCocycles hx) h_inv_fix, hxσ, smul_zero]
  exact hBv.decompGroup_le h_frob (openCocycleKer hx).isOpen' h_inertia h_conj

/-- Suppose no `m` points detect the cocycles in `component`: for every `γ : Fin m → Gal(Ω/ℚ)` some
non-zero `x` in `component` vanishes at all `γ i`. Then for every set `T` of at most `m` primes
`≡ 1 mod N l` some non-zero `z` in `component`, killed by `l`, is trivial above every prime of `T`
(it vanishes on the decomposition groups of the places above them). -/
lemma exists_ne_zero_forall_isTrivialAbove {m : ℕ}
    (h_blind : ∀ γ : Fin m → Gal(Ω/ℚ), ∃ x ∈ component l e ψ ν, (∀ i : Fin m, x (γ i) = 0) ∧ x ≠ 0)
    {T : Finset Primes} (hT : ∀ r ∈ T, r ≡ 1 [MOD N * l]) (h_card : #T ≤ m) :
    ∃ z ∈ component l e ψ ν, z ≠ 0 ∧ l • z = 0 ∧ ∀ r ∈ T, IsTrivialAbove z r := by
  -- Some `x ≠ 0` vanishes at the Frobenius elements `σ r`, `r ∈ T`, that detect triviality above
  -- `r`.
  choose place h_place using exists_place_above
  have h_detect : ∀ r : Primes, r ≡ 1 [MOD N * l] → ∃ σ : Gal(Ω/ℚ), IsFrob (place r) r σ ∧
      ∀ x ∈ component l e ψ ν, l • x = 0 → x σ = 0 → IsTrivialAbove x r :=
    fun r hr ↦ exists_isFrob_forall_isTrivialAbove hr (h_place r)
  choose! σ _hσ_frob hσ using h_detect
  obtain ⟨x, hx, hx_zero, hx_ne⟩ := h_blind fun i ↦ σ T.toList[i]!
  -- Replace `x` by its last non-zero multiple `l ^ k • x`.
  obtain ⟨k, hk, hk_succ⟩ : ∃ k : ℕ, l ^ k • x ≠ 0 ∧ l ^ (k + 1) • x = 0 :=
    exists_not_and_succ_of_not_zero_of_exists (p := fun k ↦ l ^ k • x = 0) (by simpa using hx_ne)
      ⟨ν, funext fun g ↦ nsmul_quot_eq_zero dvd_rfl (x g)⟩
  have h_tors : l • l ^ k • x = 0 := by rwa [← mul_nsmul]
  refine ⟨l ^ k • x, nsmul_mem hx _, hk, h_tors,
    fun r hr ↦ hσ r (hT r hr) _ (nsmul_mem hx _) h_tors ?_⟩
  have h_index : T.toList.idxOf r < m :=
    (List.idxOf_lt_length_iff.2 (mem_toList.2 hr)).trans_le (by rwa [length_toList])
  have hxσ : x (σ r) = 0 := by simpa [hr] using hx_zero ⟨_, h_index⟩
  simp [hxσ]

/-- Reciprocity modulo `l`. Let `a ≡ 1 mod N` be prime to `l`, with `2`, `φ (N l)` and `a ^ e - 1`
units of `O`. Let `z` in `component`, killed by `l`, be trivial above every prime of `T` but not
above a prime `r ≡ 1 mod N l`. Then a dual cocycle `y` for `cyc ^ (e + 1) ψ`, killed by `l`, that
vanishes on `inertiaOff N l (insert r T)`, vanishes on `inertiaOff N l T`. -/
lemma mem_vanishingCocycles_of_mem_insert {a m : ℕ} (ha : a ≡ 1 [MOD N]) (hla : l.Coprime a)
    (h_two : IsUnit (2 : O)) (h_totient : IsUnit (φ (N * l) : O)) (h_pow : IsUnit (a ^ e - 1 : O))
    {T : Finset Primes} {r : Primes} (hr : r ≡ 1 [MOD N * l])
    {z : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)} (hz : z ∈ component l e ψ ν) (hz_tors : l • z = 0)
    (hzT : ∀ t ∈ T, IsTrivialAbove z t) (hzr : ¬IsTrivialAbove z r)
    {y : Gal(Ω/ℚ) → QuotSpan (l ^ m : O)}
    (hy : y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l (insert r T)))
    (hy_tors : l • y = 0) :
    y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l T) := by
  -- Local constancy and the cocycle identity come from `hy`; it remains to show that `y` vanishes
  -- on the inertia groups of the places above neither `l` nor a prime of `T`.
  refine ⟨isLocallyConstant_of_mem_vanishingCocycles hy,
    apply_mul_of_mem_vanishingCocycles hy, ?_⟩
  rintro τ ⟨A, ⟨h_fix, h_val, hτ⟩, hA⟩
  by_cases hAr : A.valuation (r : Ω) < 1
  · obtain ⟨σ, hσ, h_detect⟩ := exists_isFrob_forall_isTrivialAbove (e := e) (ψ := ψ) (ν := ν) hr
      hAr
    -- A place that is not above `r` lies above no prime of `insert r T`, or `z` is trivial there.
    have h_away (B : ClosurePlace) (hB : B.valuation (r : Ω) = 1) :
        (∀ t ∈ insert r T, ¬B.valuation (t : Ω) < 1) ∨
          ∀ g ∈ decompGroup Gal(Ω/ℚ) B, z g = 0 := by
      rw [or_iff_not_imp_right, forall_mem_insert]
      exact fun h_nontrivial ↦ ⟨hB.not_lt, fun t ht hBt ↦ h_nontrivial (hzT t ht B hBt)⟩
    -- `z σ ≠ 0`, since `σ` detects triviality above `r`.
    have hzσ : (2 * (a ^ e - 1) : O) • z σ ≠ 0 :=
      (h_two.mul h_pow).smul_eq_zero.ne.2 fun h_zero ↦ hzr (h_detect z hz hz_tors h_zero)
    exact reciprocity_mod_ell hla ha hAr hσ hz h_totient hr hz_tors hy (congrFun hy_tors) hτ
      h_away hzσ
  · -- `A` lies above neither `r` nor a prime of `T`, so `hy` applies.
    exact apply_eq_zero_of_mem_vanishingCocycles hy
      ⟨A, ⟨h_fix, h_val, hτ⟩, (forall_mem_insert r T _).2 ⟨hAr, hA⟩⟩

/-- Let `v_l(X) = X.factorization l`. If `l ^ (v_l(X) + 1)` divides `X ≠ 0` in `O`, then `l` is a
unit of `O`: it divides the part of `X` prime to `l`. -/
lemma isUnit_natCast_of_pow_factorization_succ_dvd (hX : X ≠ 0)
    (h_dvd : (l ^ (X.factorization l + 1) : O) ∣ X) :
    IsUnit (l : O) := by
  -- Write `X = l ^ v_l(X) * X'`; cancelling `l ^ v_l(X)` gives `l ∣ X'`, and `X'` is prime to `l`.
  nth_rw 2 [← X.ordProj_mul_ordCompl_eq_self l] at h_dvd
  have h_dvd_compl : (l : O) ∣ (ordCompl[l] X : ℕ) := by
    simpa [pow_succ, NeZero.ne, mul_dvd_mul_iff_left] using h_dvd
  exact (X.coprime_ordCompl L.out hX).cast.isUnit_of_dvd h_dvd_compl

lemma finite_component : Finite (component l e ψ ν) :=
  finite_vanishingCocycles (n := ν)
    (fun g y ↦ (cyclotomicPowDirichlet_smul_eq_self g.prop (nsmul_quot_eq_zero dvd_rfl y)).right)
    fun _ ⟨h_fix, h_inertia⟩ ↦ .inr ⟨h_fix, .inl h_inertia⟩

/-- There are finitely many cocycles for `cyc ^ e ψ` modulo `l ^ m` that are unramified off `l`
over `ℚ(ζ_N)`. -/
lemma finite_vanishingCocycles_inertiaOff_empty (m : ℕ) :
    Finite (vanishingCocycles (cyclotomicPowDirichlet l e ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l ∅)) :=
  finite_vanishingCocycles (n := m)
    (fun g y ↦ (cyclotomicPowDirichlet_smul_eq_self g.prop (nsmul_quot_eq_zero dvd_rfl y)).left)
    fun _ ⟨h_fix, _, hv, A, hA, h_inertia⟩ ↦
      ⟨A, ⟨h_fix, hA.valuation_natCast_eq_one_iff.2 hv, h_inertia⟩, nofun⟩

/-- If `cyc ^ e ψ` is odd (value `-1` at `cmConj`) and `2` is a unit of `O`, a non-zero cocycle `z`
in `component` does not vanish on the Galois group over `ℚ(ζ_f)`, that is, this group does not lie
in the open subgroup `openCocycleKer hz` of zeros of `z`. The reason: `z` is zero at `cmConj`, where
the character of `z` has the value `-1`, and `-1 - 1 = -2` is a unit. -/
lemma not_cycloGalGroup_le_openCocycleKer_of_ne_zero (hc : cyclotomicPowDirichlet l e ψ cmConj = -1)
    (h_two : IsUnit (2 : O))
    {z : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)} (hz : z ∈ component l e ψ ν) (hz_ne : z ≠ 0)
    (f : ℕ) [NeZero f] : ¬cycloGalGroup f ≤ openCocycleKer hz := by
  have h_char : ((cyclotomicPowDirichlet l e ψ)⁻¹ cmConj : O) - 1 = -2 := by norm_num [hc]
  refine not_cycloGalGroup_le_openCocycleKer hz cmConj
    (apply_eq_zero_of_mem_vanishingCocycles hz (Set.mem_insert cmConj _)) ?_ f
  simpa only [h_char] using h_two.neg.smul_eq_zero.ne.2 hz_ne

/-- Let `cyc ^ e ψ` be odd (value `-1` at `cmConj`) and `2` a unit of `O`. There is a finite set `Q`
of primes `≡ 1 mod f` with this property. Let `y` be a cocycle for the dual character
`cyc ^ (e + 1) ψ` with values in `O / l ^ m`, unramified off `l` over `ℚ(ζ_N)` and not zero on the
Galois group over `ℚ(ζ_f)`, and let `z` be a non-zero cocycle in `component`. Then at some
Frobenius element `σ` at a place above a prime of `Q` neither `y` nor `z` vanishes. -/
lemma exists_finset_forall_exists_isFrob (hc : cyclotomicPowDirichlet l e ψ cmConj = -1)
    (h_two : IsUnit (2 : O)) (m f : ℕ) [NeZero f] :
    ∃ Q : Finset Primes, (∀ r ∈ Q, r ≡ 1 [MOD f]) ∧
      ∀ (y : vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
          (inertiaOff N l ∅)) (z : component l e ψ ν),
        ¬cycloGalGroup f ≤ openCocycleKer y.prop → z ≠ 0 →
          ∃ r ∈ Q, ∃ (A : ClosurePlace) (σ : Gal(Ω/ℚ)),
            A.valuation (r : Ω) < 1 ∧ IsFrob A r σ ∧ y.val σ ≠ 0 ∧ z.val σ ≠ 0 := by
  -- Choose a prime for each pair; there are finitely many pairs.
  have h_finite_y : Finite (vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ)
      (QuotSpan (l ^ m : O)) (inertiaOff N l ∅)) := finite_vanishingCocycles_inertiaOff_empty m
  have h_finite_z : Finite (component l e ψ ν) := finite_component
  have h_pair (y : {y : vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ)
      (QuotSpan (l ^ m : O)) (inertiaOff N l ∅) // ¬cycloGalGroup f ≤ openCocycleKer y.prop})
      (z : {z : component l e ψ ν // z ≠ 0}) :
      ∃ q : Primes, q ≡ 1 [MOD f] ∧ ∃ (A : ClosurePlace) (σ : Gal(Ω/ℚ)),
        A.valuation (q : Ω) < 1 ∧ IsFrob A q σ ∧ σ ∉ openCocycleKer y.val.prop ∧
          σ ∉ openCocycleKer z.val.prop :=
    exists_isFrob_notMem f y.prop (not_cycloGalGroup_le_openCocycleKer_of_ne_zero hc h_two
      z.val.prop (Subtype.coe_ne_coe.2 z.prop) f)
  choose q hq hq_frob using h_pair
  refine ⟨(Set.finite_range (uncurry q)).toFinset, fun r hr ↦ ?_, fun y z hy hz ↦ ?_⟩
  · obtain ⟨⟨y, z⟩, rfl⟩ : r ∈ Set.range (uncurry q) := (Set.Finite.mem_toFinset _).1 hr
    exact hq y z
  · have h_mem : q ⟨y, hy⟩ ⟨z, hz⟩ ∈ (Set.finite_range (uncurry q)).toFinset :=
      (Set.Finite.mem_toFinset _).2 ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
    exact ⟨q ⟨y, hy⟩ ⟨z, hz⟩, h_mem, hq_frob ⟨y, hy⟩ ⟨z, hz⟩⟩

omit [Fact l.Prime] [PadicIntegerRing O l] in
/-- A cocycle unramified off `l` over `ℚ(ζ_N)` vanishes on inertia above a prime `≡ 1 mod N l`. -/
lemma apply_eq_zero_of_mem_inertiaGroup {M : Type} [AddCommGroup M] [Module O M]
    {χ : Gal(Ω/ℚ) →* Oˣ} {y : Gal(Ω/ℚ) → M} (hy : y ∈ vanishingCocycles χ M (inertiaOff N l ∅))
    {r : Primes} (hr : r ≡ 1 [MOD N * l]) {A : ClosurePlace} (hA : A.valuation (r : Ω) < 1)
    {ι : Gal(Ω/ℚ)} (hι : ι ∈ inertiaGroup Gal(Ω/ℚ) A) : y ι = 0 :=
  apply_eq_zero_of_mem_vanishingCocycles hy
    ⟨A, mem_cycloGalGroup_and_valuation_eq_one hr hA hι, nofun⟩

variable (l e ψ) in
/-- A finite set `T` of primes is tight at level `m` when its primes are `≡ 1 mod N l` and every
cocycle for the dual character `cyc ^ (e + 1) ψ` with values in `O / l ^ m` that is killed by `l`
and vanishes on `inertiaOff N l T` (unramified over `ℚ(ζ_N)` off `l` and `T`) also vanishes on
`inertiaOff N l ∅` (unramified off `l`). -/
private def IsTight (m : ℕ) (T : Finset Primes) : Prop :=
  (∀ r ∈ T, r ≡ 1 [MOD N * l]) ∧
    ∀ y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
        (inertiaOff N l T), l • y = 0 →
        y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
          (inertiaOff N l ∅)

private lemma IsTight.modEq_one {m : ℕ} {T : Finset Primes} (hT : IsTight l e ψ m T) :
    ∀ r ∈ T, r ≡ 1 [MOD N * l] :=
  hT.1

/-- For a tight set `T`, a dual cocycle killed by `l` and unramified off `l` and `T` is unramified
off `l`. -/
private lemma IsTight.mem_vanishingCocycles_of_nsmul_eq_zero {m : ℕ} {T : Finset Primes}
    (hT : IsTight l e ψ m T) {y : Gal(Ω/ℚ) → QuotSpan (l ^ m : O)}
    (hy : y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l T))
    (hy_tors : l • y = 0) :
    y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l ∅) :=
  hT.2 y hy hy_tors

/-- Reciprocity keeps a set tight. Let `a ≡ 1 mod N` be prime to `l`, with `2`, `φ (N l)` and
`a ^ e - 1` units of `O`. If `T` is tight and some `z` in `component`, killed by `l`, is trivial
above every prime of `T` but not above a prime `r ≡ 1 mod N l`, then `insert r T` is tight. -/
private lemma IsTight.insert {a m : ℕ} (ha : a ≡ 1 [MOD N]) (hla : l.Coprime a)
    (h_two : IsUnit (2 : O)) (h_totient : IsUnit (φ (N * l) : O)) (h_pow : IsUnit (a ^ e - 1 : O))
    {T : Finset Primes} (hT : IsTight l e ψ m T) {r : Primes} (hr : r ≡ 1 [MOD N * l])
    {z : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)} (hz : z ∈ component l e ψ ν) (hz_tors : l • z = 0)
    (hzT : ∀ t ∈ T, IsTrivialAbove z t) (hzr : ¬IsTrivialAbove z r) :
    IsTight l e ψ m (insert r T) := by
  refine ⟨(forall_mem_insert r T _).2 ⟨hr, hT.modEq_one⟩, fun y hy hy_tors ↦ ?_⟩
  -- By reciprocity modulo `l`, `y` is unramified off `l` and `T`.
  have hy_T : y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l T) :=
    mem_vanishingCocycles_of_mem_insert ha hla h_two h_totient h_pow hr hz hz_tors hzT hzr hy
      hy_tors
  exact hT.mem_vanishingCocycles_of_nsmul_eq_zero hy_T hy_tors

/-- Kolyvagin's descent. Suppose no `m` points detect the cocycles in `component l e ψ ν`; let
`a ≡ 1 mod N` be prime to `l` with `2`, `φ (N l)`, `a ^ e - 1` units. Let `κ` be a Kolyvagin system
for `cyc ^ (e + 1) ψ` in `O / l ^ m` over the primes of `Q` (all `≡ 1 mod a N l ^ m`), with
auxiliary prime `p`, zero at `γ` (`cyc ^ (e + 1) ψ (γ) - 1` a unit), and `hQ_frob` supplying
detecting Frobenius elements. If `i ≤ m` and `S ⊆ Q` has at most `i` primes with `insert p S` tight,
`l ^ i • κ S` is unramified off `l`. -/
private lemma nsmul_mem_vanishingCocycles_of_isTight {a m : ℕ} [NeZero a] (ha : a ≡ 1 [MOD N])
    (hla : l.Coprime a) (h_two : IsUnit (2 : O)) (h_totient : IsUnit (φ (N * l) : O))
    (h_pow : IsUnit (a ^ e - 1 : O))
    (h_blind : ∀ δ : Fin m → Gal(Ω/ℚ),
      ∃ x ∈ component l e ψ ν, (∀ j : Fin m, x (δ j) = 0) ∧ x ≠ 0)
    {γ : Gal(Ω/ℚ)} (hγ_unit : IsUnit (cyclotomicPowDirichlet l (e + 1) ψ γ - 1 : O))
    {Q : Finset Primes} (hQ_mod : ∀ r ∈ Q, r ≡ 1 [MOD a * (N * l ^ m)])
    (hQ_frob : ∀ (y : vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
          (inertiaOff N l ∅)) (z : component l e ψ ν),
        ¬cycloGalGroup (a * (N * l ^ m)) ≤ openCocycleKer y.prop → z ≠ 0 →
          ∃ r ∈ Q, ∃ (A : ClosurePlace) (σ : Gal(Ω/ℚ)),
            A.valuation (r : Ω) < 1 ∧ IsFrob A r σ ∧ y.val σ ≠ 0 ∧ z.val σ ≠ 0)
    {p : Primes} {κ : Finset Primes → Gal(Ω/ℚ) → QuotSpan (l ^ m : O)}
    (hκ : IsKolyvaginSystem (cyclotomicPowDirichlet l (e + 1) ψ) γ N l p Q κ) {i : ℕ} (hi : i ≤ m) :
    ∀ S ⊆ Q, #S ≤ i → IsTight l e ψ m (insert p S) →
      l ^ i • κ S ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
        (inertiaOff N l ∅) := by
  -- Descent on `i`, from `i = m`, where `l ^ m` kills the coefficients.
  induction hi using decreasingInduction with
  | self =>
    intro S _ _ _
    simp [show l ^ m • κ S = 0 from funext fun g ↦ nsmul_quot_eq_zero dvd_rfl (κ S g)]
  | of_succ i hi ih =>
    intro S hS h_card h_tight
    suffices h_tors : l • l ^ i • κ S = 0 from
      h_tight.mem_vanishingCocycles_of_nsmul_eq_zero (nsmul_mem (hκ.mem_vanishingCocycles S hS) _)
        h_tors
    by_contra h_ne
    -- If `y = l ^ (i + 1) • κ S` is not zero, it is not zero on the Galois group over
    -- `ℚ(ζ_{a N l ^ m})`, because `y γ = 0` and `cyc ^ (e + 1) ψ (γ) - 1` is a unit.
    let y : vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
        (inertiaOff N l ∅) :=
      ⟨l ^ (i + 1) • κ S, ih S hS h_card.step h_tight⟩
    have hy_ne : l ^ (i + 1) • κ S ≠ 0 := by rwa [← mul_nsmul] at h_ne
    have hyγ : (l ^ (i + 1) • κ S) γ = 0 := by simp [hκ.apply_eq_zero S hS]
    have hy : ¬cycloGalGroup (a * (N * l ^ m)) ≤ openCocycleKer y.prop :=
      not_cycloGalGroup_le_openCocycleKer y.prop γ hyγ (hγ_unit.smul_eq_zero.ne.2 hy_ne) _
    -- Some `w ≠ 0` in `component`, killed by `l`, is trivial above `p` and the primes of `S`.
    obtain ⟨w, hw, hw_ne, hw_tors, hw_triv⟩ := exists_ne_zero_forall_isTrivialAbove h_blind
      h_tight.modEq_one ((card_insert_le p S).trans (Nat.succ_le_of_lt (h_card.trans_lt hi)))
    -- The prime `r` of the pair `(y, w)` is new (`w` is not trivial above it); the set stays tight.
    obtain ⟨r, hrQ, A, σ, hA, hσ, hyσ, hwσ⟩ := hQ_frob y ⟨w, hw⟩ hy (Subtype.coe_ne_coe.1 hw_ne)
    have h_level : N * l ∣ N * l ^ m := mul_dvd_mul_left N (dvd_pow_self l (Nat.ne_zero_of_lt hi))
    have hr : r ≡ 1 [MOD N * l] := (hQ_mod r hrQ).of_dvd (h_level.mul_left a)
    have hwr : ¬IsTrivialAbove w r := fun h_triv ↦
      hwσ (h_triv A hA σ hσ.mem_decompGroup)
    have hrS : r ∉ S := fun hrS ↦ hwr (hw_triv r (mem_insert_of_mem hrS))
    have h_tight_next : IsTight l e ψ m (insert p (insert r S)) := by
      simpa only [insert_comm p r] using
        h_tight.insert ha hla h_two h_totient h_pow hr hw hw_tors hw_triv hwr
    have h_next : l ^ (i + 1) • κ (insert r S) ∈ vanishingCocycles
        (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O)) (inertiaOff N l ∅) :=
      ih _ (insert_subset hrQ hS) ((card_insert_le r S).trans (Nat.succ_le_succ h_card))
        h_tight_next
    -- Hence `y σ = l ^ (i + 1) • κ (insert r S) ι = 0`, against the choice of `σ`.
    obtain ⟨ι, hι, h_eq⟩ := hκ.exists_mem_inertiaGroup_eq S hS r hrQ hrS A σ hσ hA
    refine hyσ ?_
    calc l ^ (i + 1) • κ S σ = (l ^ (i + 1) • κ (insert r S)) ι := by rw [← h_eq, Pi.smul_apply]
      _ = 0 := apply_eq_zero_of_mem_inertiaGroup h_next hr hA hι

/-- The Kolyvagin–Rubin bound, from the Euler system of Gauss sums. Let `X ≠ 0` satisfy
`IsStickelbergerBound N e X`, a divisibility for each prime plus a congruence for the Stickelberger
sums. Let `cyc ^ e ψ` be odd (value `-1` at `cmConj`), `e ≠ 0` and `l > N + e + 3`. Then there are
`v_l(X) + 1` elements `γ i` of the Galois group, where `v_l(X) = X.factorization l`, such that a
cocycle in `component l e ψ ν` vanishing at all of them is zero. That space consists of cocycles
`Gal(Ω/ℚ) → O/l^ν` for `(cyc^e ψ)⁻¹` under local conditions.

It is used instead of the Iwasawa main conjecture proved by Mazur and Wiles: for l > N + e + 3 it
bounds, at finite level, the number of Galois elements needed to detect the cocycles. -/
lemma exists_detecting_points_component (h_bound : IsStickelbergerBound N e X)
    (hc : cyclotomicPowDirichlet l e ψ cmConj = -1) (he_ne_zero : e ≠ 0) (hX : X ≠ 0)
    (hl : N + e + 3 < l) :
    ∃ γ : Fin (X.factorization l + 1) → Gal(Ω/ℚ),
      ∀ x ∈ component l e ψ ν, (∀ i : Fin (X.factorization l + 1), x (γ i) = 0) → x = 0 := by
  -- Suppose no `m = v_l(X) + 1` points detect the cocycles. Then for any `m` primes `≡ 1 mod N l`
  -- some non-zero cocycle killed by `l` is trivial above all of them. By reciprocity this bounds
  -- the ramification of Kolyvagin's cocycles `κ S`; by descent `κ ∅` is unramified at `p`, so that
  -- `l ^ m ∣ X` in `O`.
  by_contra! h_blind
  set m : ℕ := X.factorization l + 1
  have h_two : IsUnit (2 : O) := by
    exact_mod_cast isUnit_natCast_of_not_dvd (O := O)
      (not_dvd_of_pos_of_lt two_pos (by lia : 2 < l))
  have h_totient : IsUnit (φ (N * l) : O) := isUnit_totient_mul (by lia)
  obtain ⟨a, ha, hla, h_pow, h_pow_succ⟩ :=
    exists_modEq_one_coprime_isUnit_pow_sub_one (O := O) he_ne_zero hl
  have ha_ne_zero : NeZero a := ⟨ne_zero_of_coprime hla⟩
  have h_level : N * l ∣ N * l ^ m := mul_dvd_mul_left N (dvd_pow_self l (NeZero.ne m))
  -- At `γ` the dual character has the value `a ^ (e + 1)`.
  obtain ⟨P, hP⟩ := exists_place_above ⟨l, L.out⟩
  obtain ⟨γ, -, hγ⟩ := exists_inertia_cyclotomicPowDirichlet_eq (ψ := ψ) hla ha hP (e + 1)
  have hγ_unit : IsUnit (cyclotomicPowDirichlet l (e + 1) ψ γ - 1 : O) := by rwa [hγ]
  obtain ⟨Q, hQ_mod, hQ_frob⟩ :=
    exists_finset_forall_exists_isFrob (ν := ν) hc h_two m (a * (N * l ^ m))
  -- Choose `z ≠ 0` killed by `l`, and a prime `p ≡ 1` modulo `N l ^ m` and all of `Q` at which `z`
  -- is not trivial.
  obtain ⟨z, hz, hz_ne, hz_tors, -⟩ :=
    exists_ne_zero_forall_isTrivialAbove h_blind (T := ∅) (by simp) bot_le
  have h_prod_ne_zero : NeZero (∏ r ∈ Q, (r : ℕ)) := NeZero.of_pos (Q.prod_pos fun r _ ↦ r.prop.pos)
  have hz_visible : ¬cycloGalGroup (N * l ^ m * ∏ r ∈ Q, (r : ℕ)) ≤ openCocycleKer hz :=
    not_cycloGalGroup_le_openCocycleKer_of_ne_zero hc h_two hz hz_ne _
  obtain ⟨p, hp : p ≡ 1 [MOD N * l ^ m * ∏ r ∈ Q, (r : ℕ)], B, τ, hB : B.valuation (p : Ω) < 1,
      hτ : IsFrob B p τ, hzτ : z τ ≠ 0, -⟩ :=
    exists_isFrob_notMem _ hz_visible hz_visible
  have hp_split : p ≡ 1 [MOD N * l] := hp.of_dvd (h_level.mul_right _)
  have h_tight_empty : IsTight l e ψ m ∅ := ⟨by simp, fun y hy _hy_tors ↦ hy⟩
  have hp_tight : IsTight l e ψ m (insert p ∅) :=
    h_tight_empty.insert ha hla h_two h_totient h_pow hp_split hz hz_tors (by simp)
      fun h_triv ↦ hzτ (h_triv B hB τ hτ.mem_decompGroup)
  -- Kolyvagin's cocycles `κ S` for `S ⊆ Q`; if `κ ∅` is unramified at `B`, then
  -- `cyc ^ (e + 1) ψ (γ) - 1` kills the Stickelberger sum (`h_value`).
  obtain ⟨κ, hκ : IsKolyvaginSystem (cyclotomicPowDirichlet l (e + 1) ψ) γ N l p Q κ, h_value⟩ :=
    exists_isKolyvaginSystem (ψ := ψ) e a γ hQ_mod hp hB
  -- By descent down to `i = 0`, `κ ∅` is unramified off `l`, so it kills inertia at `B`.
  have h_κ_mem : κ ∅ ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l ∅) := by
    simpa using nsmul_mem_vanishingCocycles_of_isTight ha hla h_two h_totient h_pow h_blind
      hγ_unit hQ_mod hQ_frob hκ (zero_le m) ∅ (empty_subset Q) le_rfl hp_tight
  have h_inertia (ι : Gal(Ω/ℚ)) (hι : ι ∈ inertiaGroup Gal(Ω/ℚ) B) : κ ∅ ι = 0 :=
    apply_eq_zero_of_mem_inertiaGroup h_κ_mem hp_split hB hι
  -- So the Stickelberger sum is `0` modulo `l ^ m`, and `l ^ m ∣ X`.
  have h_sum_zero : ((∑ u : (ZMod (N * l ^ m))ˣ, floorDiff a (ofZMod (N * l ^ m) u) *
      ((u : ZMod (N * l ^ m)).val ^ e * ψ (u : ZMod (N * l ^ m)).val) : O) :
        QuotSpan (l ^ m : O)) = 0 :=
    hγ_unit.smul_eq_zero.1 (h_value h_inertia)
  have h_dvd_mul : (l ^ m : O) ∣ (a ^ (e + 1) - 1) * X := by
    obtain ⟨c, h_eq⟩ := sum_floorDiff_dvd h_bound hc he_ne_zero m ha hla
    simpa only [h_sum_zero, zero_mul, eq_zero_iff_dvd] using h_eq
  have h_dvd : (l ^ m : O) ∣ X := h_pow_succ.dvd_mul_left.1 h_dvd_mul
  -- Then `l` is a unit of `O`, and a unit kills no `z ≠ 0`.
  have hl_unit : IsUnit (l : O) := isUnit_natCast_of_pow_factorization_succ_dvd hX h_dvd
  exact hz_ne (hl_unit.smul_eq_zero.1 (by rwa [Nat.cast_smul_eq_nsmul]))

end ComponentBound

end New.OddPart
