module

import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.SiegelWeil.UnramifiedSeries.VacuumCoefficients
import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
public import Lib.SiegelWeil.RallisInner.Doubling
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Finset.Functor
import Mathlib.Topology.Algebra.Group.Units
public import Lib.Adelic.AutomorphicForms.Basic
import Lib.Adelic.Adeles.StrongApproximation
import Lib.Shimura.ComplexTheta.AppellHumbertData
import Lib.Shimura.Uniformisation.HolomorphicFamilies
import Mathlib.Order.Interval.Finset.Box
import TauCeti.NumberTheory.NumberField.Countable
public import Lib.ClassField.HeckeCharacter.TameModulus
public import Lib.ClassField.Avatar.HeckeBaseChange
public import Lib.Weil.Lift
import Lib.ClassField.HeckeL.ContinuationAtOne
import Lib.General.Algebra.LevelModulus
import Lib.General.LinearAlgebra.HermiteForm
import Lib.General.LinearAlgebra.PartnerAlgebra
import Lib.Weil.Unramified.HeckeTransfer

section
section
/-!
# Summability of the vacuum coefficients from the doubling formula

For `2 * card n < M`, the coefficients `New.SiegelWeil.vacuumCoeff M b` of the vacuum are absolutely
summable over the representatives `New.SiegelWeil.cosetRep` of the cosets of the points integral at
any set of places (`New.SiegelWeil.summable_norm_vacuumCoeff`).

The proof applies Rallis' inner product formula `New.SiegelWeil.inner_product_formula` to the
definite spaces `stdSpace E n`, `stdSpace E m` (with `card m = M`), the vacuum datum and the
constant function `1`: the matrix coefficient `g ↦ ⟨vac, ω(g) vac⟩` is integrable on the adelic
unitary group. Cutting the group into the cosets of the points integral at every place
(`New.hasSum_setIntegral_mul_of_existsUnique`), the integral of its modulus is the sum of the moduli
of the vacuum coefficients times a positive number.
-/

@[expose] public section

noncomputable section

open MeasureTheory Fintype

namespace New

/-- Cutting an integral over a group into cosets. Let `μ` be left invariant on `H`, let `L` be a
measurable subgroup, and let the points `r i`, for `i` in a countable type, meet every coset `g L`
exactly once. The integral of an integrable `Φ` is the sum over `i` of the integrals of
`g ↦ Φ (r i * g)` over `L`. -/
lemma hasSum_setIntegral_mul_of_existsUnique {H ι F : Type*} [Group H] [MeasurableSpace H]
    [MeasurableMul H] {μ : Measure H} [μ.IsMulLeftInvariant] {L : Subgroup H} [Countable ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hL : MeasurableSet (L : Set H)) {r : ι → H}
    (hr : ∀ g : H, ∃! i, (r i)⁻¹ * g ∈ L) {Φ : H → F} (hΦ : Integrable Φ μ) :
    HasSum (fun i ↦ ∫ g in (L : Set H), Φ (r i * g) ∂μ) (∫ g, Φ g ∂μ) := by
  -- The cosets `r i L` are disjoint, cover `H`, and each is the image of `L` under a measure
  -- preserving left translation.
  let coset (i : ι) : Set H := (fun g ↦ (r i)⁻¹ * g) ⁻¹' L
  have h_disjoint : Pairwise (Function.onFun Disjoint coset) := fun i j h_ne ↦
    Set.disjoint_left.2 fun g hi hj ↦ h_ne ((hr g).unique hi hj)
  have h_cover : ⋃ i, coset i = Set.univ :=
    Set.eq_univ_of_forall fun g ↦ Set.mem_iUnion.2 (hr g).exists
  have h_coset (i : ι) : ∫ g in coset i, Φ g ∂μ = ∫ g in (L : Set H), Φ (r i * g) ∂μ := by
    simpa using (measurePreserving_mul_left μ (r i)⁻¹).setIntegral_preimage_emb
      (measurableEmbedding_mulLeft _) (fun g ↦ Φ (r i * g)) L
  simpa only [h_coset, h_cover, Measure.restrict_univ] using
    hasSum_integral_iUnion (s := coset) (fun i ↦ measurable_const_mul _ hL) h_disjoint hΦ.restrict

namespace SiegelWeil

open Space

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]

/-- For `2 * card n < card m`, the vacuum coefficients `vacuumCoeff (card m) 1` are absolutely
summable over the cosets of the points integral at every place. -/
lemma summable_norm_vacuumCoeff_univ (h_rank : 2 * card n < card m) :
    Summable fun q : Gf E n ⧸ localLevel n Set.univ ↦
      ‖vacuumCoeff (card m) 1 (cosetRep q).val‖ := by
  classical
  -- The vacuum datum on `Hom(S, T)` for the definite spaces, paired with the constant `1`.
  let S : Space E n 1 := stdSpace E n
  let T : Space E m 1 := stdSpace E m
  let f : 𝒮 (S.hom T) := (S.hom T).vacElem
  have hf_clean : IsClean f := .inl fun _ _ ↦ rfl
  have h_one : (fun _ : G E (1 : n → ℤˣ) ↦ (1 : ℂ)) ∈ S.rapidFunctions :=
    (S.isAutomorphic_const 1).mem_rapidFunctions fun _ _ ↦ rfl
  obtain ⟨h_int, -⟩ :=
    inner_product_formula h_rank (1 : AutChar E) (1 : AutChar E) hf_clean h_one h_one
  -- The coefficient itself is integrable: the Petersson factor is the volume of `[U(S)]`.
  have h_const : S.petersson (fun _ ↦ (1 : ℂ)) (fun _ ↦ (1 : ℂ)) ≠ 0 := by
    simp [Space.petersson, measureReal_univ_ne_zero]
  have h_coeff : Integrable fun g : G E (1 : n → ℤˣ) ↦ weilMatrixCoeff 1 f f g := by
    refine (integrable_mul_const_iff (isUnit_iff_ne_zero.2 h_const) _).1 ?_
    convert h_int using 3
    rfl
  -- Cut the group into the cosets of `L`, the points whose finite part is integral everywhere.
  let L : Subgroup (G E (1 : n → ℤˣ)) :=
    (localLevel n Set.univ).comap (MonoidHom.snd (GInf E (1 : n → ℤˣ)) (Gf E n))
  let r (q : Gf E n ⧸ localLevel n Set.univ) : G E (1 : n → ℤˣ) := ((cosetRep q).val : G E 1)
  have hL_open : IsOpen (L : Set (G E (1 : n → ℤˣ))) :=
    (isOpen_coe_localLevel (E := E) (n := n) Set.univ).preimage continuous_snd
  have mem_L (q : Gf E n ⧸ localLevel n Set.univ) (g : G E (1 : n → ℤˣ)) :
      (r q)⁻¹ * g ∈ L ↔ q = (g.2 : Gf E n ⧸ localLevel n Set.univ) := by
    have h_snd : (r q)⁻¹ * g ∈ L ↔ ((cosetRep q).val)⁻¹ * g.2 ∈ localLevel n Set.univ := by
      simp [L, r]
    rw [h_snd, ← QuotientGroup.eq, mk_cosetRep]
  have hr (g : G E (1 : n → ℤˣ)) : ∃! q, (r q)⁻¹ * g ∈ L :=
    ⟨g.2, (mem_L _ g).2 rfl, fun q hq ↦ (mem_L q g).1 hq⟩
  have := countable_quotient_localLevel (E := E) (n := n) Set.univ
  have h_sum := hasSum_setIntegral_mul_of_existsUnique hL_open.measurableSet hr h_coeff.norm
  -- On `L` the vacuum coefficient comes out of the modulus.
  have hf_vac : projOn (S.hom T) Set.univ f = f := projOn_vacElem _
  set I : ℝ := ∫ g in (L : Set (G E (1 : n → ℤˣ))), ‖weilMatrixCoeff 1 f f g‖
  have h_terms (q : Gf E n ⧸ localLevel n Set.univ) :
      ∫ g in (L : Set (G E (1 : n → ℤˣ))), ‖weilMatrixCoeff 1 f f (r q * g)‖ =
        ‖vacuumCoeff (card m) 1 (cosetRep q).val‖ * I := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hL_open.measurableSet fun g (hg : g.2 ∈ localLevel n Set.univ) ↦ ?_
    simp only [r, weilMatrixCoeff_mul 1 hf_vac (by simp [Gf.mem_supportedOn]) hg, norm_mul]
  -- `I > 0`: the coefficient is continuous and equal to `1` at the identity.
  have h_cont : Continuous fun g : G E (1 : n → ℤˣ) ↦ weilMatrixCoeff 1 f f g := by
    unfold weilMatrixCoeff
    fun_prop
  have h_pos : 0 < I := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (.of_forall fun _ ↦ norm_nonneg _)
      h_coeff.norm.integrableOn]
    let U : Set (G E (1 : n → ℤˣ)) := (L : Set _) ∩ {g | weilMatrixCoeff 1 f f g ≠ 0}
    have hU_open : IsOpen U := hL_open.inter (isOpen_ne_fun h_cont continuous_const)
    have h_mem : (1 : G E (1 : n → ℤˣ)) ∈ U :=
      ⟨one_mem L, by simp [weilMatrixCoeff, f, Prod.mk_one_one, dataInner_vacElem_vacElem]⟩
    refine (hU_open.measure_pos _ ⟨1, h_mem⟩).trans_le (measure_mono ?_)
    rintro g ⟨hg_L, hg⟩
    exact ⟨norm_ne_zero_iff.2 hg, hg_L⟩
  exact (summable_mul_right_iff h_pos.ne').1 (h_sum.congr_fun fun q ↦ (h_terms q).symm).summable

/-- For `2 * card n < card m`, consider the numbers `vacuumCoeff (card m) b g = (b(det g) *
finMultiplier g ^ card m)⁻¹`. This is the factor by which `g` changes the vacuum matrix coefficient
when the second space has rank `m`. These numbers are absolutely summable over the representatives
`cosetRep q` of the cosets `q` of `Gf E n` modulo `localLevel n A`, the points integral at `A`. -/
theorem summable_norm_vacuumCoeff (h_rank : 2 * card n < card m) (b : AutChar E)
    (A : Set (FinPlace E)) :
    Summable fun q : Gf E n ⧸ localLevel n A ↦ ‖vacuumCoeff (card m) b (cosetRep q).val‖ := by
  classical
  -- The norms do not see `b`, and the cosets at `A` inject into the cosets at all places.
  let ι (q : Gf E n ⧸ localLevel n A) : Gf E n ⧸ localLevel n Set.univ := ((cosetRep q).val : _)
  have hι : Function.Injective ι := by
    intro q₁ q₂ h
    rw [← mk_cosetRep q₁, ← mk_cosetRep q₂, QuotientGroup.eq]
    exact fun w _ ↦ QuotientGroup.eq.1 h w (Set.mem_univ w)
  refine ((summable_norm_vacuumCoeff_univ (E := E) h_rank).comp_injective hι).congr fun q ↦ ?_
  have h_supp : (cosetRep q).val ∈ Gf.supportedOn n Set.univ := by simp
  simp only [Function.comp_apply, ι, norm_vacuumCoeff]
  rw [finMultiplier_cosetRep_mk h_supp]

end SiegelWeil

end New
end
end
end

/-!
# The series of translates weighted by the coefficients of the vacuum

This file proves, for `2 n < m`, that the series `New.SiegelWeil.rallisSeries` converges uniformly
(the coefficients are absolutely summable by `New.SiegelWeil.summable_norm_vacuumCoeff`, from the
doubling formula), that it keeps levels and forms and that it is multiplicative over the places. The
last section defines the sum of the coefficients `New.SiegelWeil.vacuumSum` and writes it as a
product over the pairs of conjugate places.

Let `G_f` be the finite adelic unitary group of rank `n` over the CM field `E`, and let `A` be a set
of finite places. The series `∑ mc(γ) R(γ) y` runs over the cosets `γ` of the points integral at
`A`; here `R` is right translation and `mc(γ)` is the coefficient of the vacuum for a second space
of rank `m`, of modulus `[γ L : L ∩ γ L] ^ (-m / 2)` for the standard lattice `L`. In the inner
product formula `A` is the set of the places off the level and its conjugate.

## Main definitions and results

* `New.SiegelWeil.exists_form_eq_rallisSeries`: the series keeps forms and their levels.
* `New.SiegelWeil.rallisSeries_union`: the series is multiplicative over the places.

Notions from other files:
* `localLevel n A`: the points of `G_f` integral at the places of `A`; `stdLevel E n`: the points
  integral at all finite places; `supportedOn n A`: the points with component `1` outside `A` and
  its conjugate, whose union is `A.conjClosure`.
* `HasLevel y K`: right translation by each point of `K` fixes the function `y` on the adelic points
  `G E s`, the products of a point of `GInf E s` (the real points, the only part that depends on the
  signs `s : n → ℤˣ`) and a point of `Gf E n`.
* `New.SiegelWeil.rallisSeries M b A y`: the series `∑ mc(q) R(q) y`, with coefficient
  `New.SiegelWeil.vacuumCoeff M b` and right translation taken at `New.SiegelWeil.cosetRep q`.
* `New.SiegelWeil.IsUnramifiedOn`: `b ∘ det` is trivial on the integral finite points supported on
  `A` and its conjugate.

## Relation to the literature

Part of a known result: non-vanishing of theta lifts in large rank. See
`Lib.SiegelWeil.RallisInner.SharpData`. The series is the contribution of the unramified places to
Rallis' inner product formula, left as a sum over cosets instead of being evaluated as an L-value;
for the constant `1` in rank one it is evaluated in `New.vacuumSum_eq_L_div_eulerProd`.
-/

@[expose] public section

noncomputable section

namespace New.SiegelWeil

open Matrix MeasureTheory Fintype Space Gf G WeilData NumberField Rows

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]
  {s : n → ℤˣ} {b : AutChar E} {A : Set (FinPlace E)} {y : G E s → ℂ}

/-! ### Convergence, level and forms -/

/-- For `2 * card n < card m` and `y` bounded, the series `rallisSeries` converges uniformly: its
partial sums over finite sets of cosets tend to it uniformly. -/
lemma tendstoUniformly_rallisSeries (h_rank : 2 * card n < card m) (b : AutChar E)
    (A : Set (FinPlace E)) (hy : ∃ C : ℝ, ∀ g : G E s, ‖y g‖ ≤ C) :
    TendstoUniformly
      (fun (Q : Finset (Gf E n ⧸ localLevel n A)) (g : G E s) ↦
        ∑ q ∈ Q, vacuumCoeff (card m) b (cosetRep q).val * y (g * (1, (cosetRep q).val)))
      (rallisSeries (card m) b A y) Filter.atTop := by
  obtain ⟨C, hC⟩ := hy
  exact tendstoUniformly_tsum ((summable_norm_vacuumCoeff h_rank b A).mul_right C)
    fun q g ↦ norm_mul_le_of_le le_rfl (hC _)

/-- For `2 * card n < card m` and `y` bounded by `C`, the series `rallisSeries` is bounded by `C`
times the sum of the moduli of the coefficients of the vacuum. -/
lemma norm_rallisSeries_le (h_rank : 2 * card n < card m) (b : AutChar E)
    (A : Set (FinPlace E)) {C : ℝ} (hC : ∀ g : G E s, ‖y g‖ ≤ C) (g : G E s) :
    ‖rallisSeries (card m) b A y g‖ ≤
      (∑' q : Gf E n ⧸ localLevel n A, ‖vacuumCoeff (card m) b (cosetRep q).val‖) * C :=
  tsum_of_norm_bounded ((summable_norm_vacuumCoeff h_rank b A).hasSum.mul_right C)
    fun _ ↦ norm_mul_le_of_le le_rfl (hC _)

/-- For `2 * card n < card m` and `y` continuous and bounded, the series `rallisSeries` is
continuous. -/
lemma continuous_rallisSeries (h_rank : 2 * card n < card m) (b : AutChar E)
    (A : Set (FinPlace E)) (hy_cont : Continuous y) (hy_bdd : ∃ C : ℝ, ∀ g : G E s, ‖y g‖ ≤ C) :
    Continuous (rallisSeries (card m) b A y) :=
  (tendstoUniformly_rallisSeries h_rank b A hy_bdd).continuous
    (.of_forall fun _ ↦ by fun_prop)

/-- The series `rallisSeries M b A y` is `∑_q vacuumCoeff M b (cosetRep q) · R(cosetRep q) y`, a sum
of right translates of a function `y` on the adelic points `G E s`. The sum runs over the cosets
`q`, in the finite points, of the subgroup of points integral at `A`, with representatives supported
on `A` and its conjugate. The series commutes with left translations with no convergence hypothesis:
applied to `g' ↦ y (x * g')` and evaluated at `g`, it equals `rallisSeries M b A y` at `x * g`. -/
lemma rallisSeries_comp_mul_left (M : ℕ) (b : AutChar E) (A : Set (FinPlace E)) (y : G E s → ℂ)
    (x g : G E s) :
    rallisSeries M b A (fun g' : G E s ↦ y (x * g')) g = rallisSeries M b A y (x * g) := by
  simp only [rallisSeries, mul_assoc]

/-- Let `b ∘ det` be trivial on the integral points supported on `A` and its conjugate, and let `y`
be fixed by these points. A finite point `k` integral at `A` that fixes `y` also fixes
`rallisSeries M b A y`, the series of translates of `y` weighted by the coefficients of the
vacuum. -/
lemma rallisSeries_mul_of_mem_localLevel (hb : IsUnramifiedOn b n A) (M : ℕ)
    (hy : HasLevel y (stdLevel E n ⊓ supportedOn n A)) {k : Gf E n} (hk : k ∈ localLevel n A)
    (hk_fix : ∀ g : G E s, y (g * (1, k)) = y g) (g : G E s) :
    rallisSeries M b A y (g * (1, k)) = rallisSeries M b A y g := by
  -- Write `k = a * d` with `a` supported on `A` and its conjugate and `d` trivial at `A`. Both fix
  -- `y`; `d` commutes with the representatives, and `a` permutes the cosets.
  obtain ⟨a, ha : a ∈ supportedOn n A, d, hd : d ∈ trivialOn n A, rfl : k = a * d, -⟩ :=
    k.exists_supportedOn_mul_trivialOn A
  have d_int : d ∈ localLevel n A := fun w hw ↦ by simp [mem_trivialOn.1 hd w hw]
  have a_int : a ∈ localLevel n A := (mul_mem_cancel_right d_int).1 hk
  have a_level : a ∈ stdLevel E n ⊓ supportedOn n A :=
    Subgroup.mem_inf.2 ⟨(mem_stdLevel_iff_of_supportedOn ha).2 a_int, ha⟩
  have d_fix (g : G E s) : y (g * (1, d)) = y g := by
    rw [show g * (1, d) = g * (1, a⁻¹) * (1, a * d) by simp [mul_assoc], hk_fix,
      hy a⁻¹ (inv_mem a_level)]
  let term (g : G E s) (q : Gf E n ⧸ localLevel n A) : ℂ :=
    vacuumCoeff M b (cosetRep q).val * y (g * (1, (cosetRep q).val))
  have h_term (q : Gf E n ⧸ localLevel n A) : term (g * (1, a * d)) q = term g (a • q) := by
    set r : Gf E n := (cosetRep q).val with h_rep
    have hr : r ∈ supportedOn n A := (cosetRep q).property
    have h_coset : a • q = (a * r : Gf E n) := by
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, mk_cosetRep]
    have h_coeff : vacuumCoeff M b (a * r) = vacuumCoeff M b r := by
      simpa using vacuumCoeff_mul_mul_of_mem hb M a_level (one_mem _) r
    have h_comm : g * (1, a * d) * (1, r) = g * (1, a * r) * (1, d) := by
      simp [mul_assoc, (commute_supportedOn_trivialOn hr hd).eq]
    simp only [term, h_coset, vacuumCoeff_mul_apply_cosetRep hb M hy (mul_mem ha hr), ← h_rep,
      h_coeff, h_comm, d_fix]
  rw [rallisSeries, rallisSeries]
  calc ∑' q, term (g * (1, a * d)) q = ∑' q, term g (a • q) := tsum_congr h_term
    _ = ∑' q, term g q := (MulAction.toPerm a).tsum_eq (term g)

/-- The series `rallisSeries M b A y` (the sum over cosets `q` of the points integral at `A` of the
right translates `R(cosetRep q) y`, weighted by `vacuumCoeff M b (cosetRep q)`) keeps the level. Let
`b ∘ det` be trivial on the integral points supported on `A` and its conjugate (`IsUnramifiedOn`).
Let the subgroup `J` of the finite points contain those points and lie in `localLevel n A`, the
points integral with integral inverse at each place of `A`; then if `y` is right invariant under
`J`, so is `rallisSeries M b A y`. -/
lemma hasLevel_rallisSeries (hb : IsUnramifiedOn b n A) (M : ℕ) {J : Subgroup (Gf E n)}
    (h_ge : stdLevel E n ⊓ supportedOn n A ≤ J) (h_le : J ≤ localLevel n A) (hy : HasLevel y J) :
    HasLevel (rallisSeries M b A y) J := fun k hk ↦
  rallisSeries_mul_of_mem_localLevel hb M (fun j hj ↦ hy j (h_ge hj)) (h_le hk) (hy k hk)

/-- The series `rallisSeries` may be integrated term by term. Let `2 * card n < card m`, let `y` be
bounded and measurable, `f` integrable and `j` measurable. The integral of `f z` times the series
at `j z` is the sum over the cosets `q` of the coefficient of the vacuum at `u = cosetRep q` times
the integral of `f z * y (j z * u)`. -/
lemma hasSum_integral_mul_rallisSeries (h_rank : 2 * card n < card m) (b : AutChar E)
    (A : Set (FinPlace E)) (hy : IsBoundedMeasurable y) {Z : Type*} [MeasurableSpace Z]
    {μ : Measure Z} {f : Z → ℂ} (hf : Integrable f μ) {j : Z → G E s} (hj : Measurable j) :
    HasSum (fun q : Gf E n ⧸ localLevel n A ↦ vacuumCoeff (card m) b (cosetRep q).val *
        ∫ z : Z, f z * y (j z * (1, (cosetRep q).val)) ∂μ)
      (∫ z : Z, f z * rallisSeries (card m) b A y (j z) ∂μ) := by
  obtain ⟨C, hC⟩ := hy.bounded
  let term (q : Gf E n ⧸ localLevel n A) (z : Z) : ℂ :=
    vacuumCoeff (card m) b (cosetRep q).val * (f z * y (j z * (1, (cosetRep q).val)))
  have h_int (q : Gf E n ⧸ localLevel n A) : Integrable (term q) μ :=
    (hy.integrable_mul_comp hf (fun z ↦ j z * (1, (cosetRep q).val)) (hj.mul_const _)).const_mul _
  have h_le (q : Gf E n ⧸ localLevel n A) : ∫ z, ‖term q z‖ ∂μ ≤
      ‖vacuumCoeff (card m) b (cosetRep q).val‖ * ∫ z, ‖f z‖ * C ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono (h_int q).norm ((hf.norm.mul_const C).const_mul _) fun z ↦ ?_
    simp only [term, norm_mul]
    gcongr
    exact hC _
  have h_summable : Summable fun q ↦ ∫ z, ‖term q z‖ ∂μ :=
    ((summable_norm_vacuumCoeff h_rank b A).mul_right _).of_nonneg_of_le
      (fun q ↦ integral_nonneg fun z ↦ norm_nonneg _) h_le
  have h_series (z : Z) : ∑' q, term q z = f z * rallisSeries (card m) b A y (j z) := by
    simp [term, rallisSeries, ← tsum_mul_left, mul_left_comm]
  have : Countable (Gf E n ⧸ localLevel n A) := countable_quotient_localLevel A
  simpa only [h_series, term, integral_const_mul] using
    hasSum_integral_of_summable_integral_norm h_int h_summable

/-- For `2 * card n < card m` and `y` bounded and measurable, the series `rallisSeries` commutes
with `realConv κ`, the right convolution by an integrable function `κ` on the real points. -/
lemma realConv_rallisSeries (h_rank : 2 * card n < card m) (b : AutChar E)
    (A : Set (FinPlace E)) (hy : IsBoundedMeasurable y) {κ : GInf E s → ℂ} (hκ : Integrable κ) :
    realConv κ (rallisSeries (card m) b A y) = rallisSeries (card m) b A (realConv κ y) := by
  ext g
  have h_comm (x : GInf E s) (u : Gf E n) : g * (1, u) * (x, 1) = g * (x, 1) * (1, u) := by
    simp [mul_assoc]
  have h_sum : ∑' q : Gf E n ⧸ localLevel n A, vacuumCoeff (card m) b (cosetRep q).val *
        ∫ x, κ x * y (g * (x, 1) * (1, (cosetRep q).val)) =
      ∫ x, κ x * rallisSeries (card m) b A y (g * (x, 1)) :=
    (hasSum_integral_mul_rallisSeries h_rank b A hy hκ (by fun_prop)).tsum_eq
  simpa only [rallisSeries, realConv, h_comm] using h_sum.symm

/-- The Petersson product with the series `rallisSeries` may be taken term by term. Let `S` be a
hermitian space of rank `card n` over `E` with signs `s` and adelic points `G E s`, and let
`⟨y', z⟩ = S.petersson y' z` be the integral of `conj (y' g) * z g` against `S.quotMeasure`, the
measure that computes integrals over the quotient by the rational points of `S`. Let
`2 * card n < card m`, let `y` be bounded and strongly measurable, let `y'` be integrable for this
measure, let `x` be an adelic point, and write `R(x) z` for the translate `g ↦ z (g * x)`.
Let `q` run over the cosets of `localLevel n A`, the finite points integral at `A`, with
representatives `u = cosetRep q`. Then the numbers `vacuumCoeff (card m) b u * ⟨y', R(x u) y⟩`,
where `vacuumCoeff M b u = (b(det u) * finMultiplier u ^ M)⁻¹`, have sum `⟨y', R(x) z⟩` for the
series `z = rallisSeries (card m) b A y = ∑ vacuumCoeff (card m) b u * R(u) y`. -/
lemma hasSum_petersson_rallisSeries {s : n → ℤˣ} {y : G E s → ℂ} {S : Space E n s}
    (h_rank : 2 * card n < card m) (b : AutChar E) (A : Set (FinPlace E))
    (hy : IsBoundedMeasurable y) {y' : G E s → ℂ} (hy' : Integrable y' S.quotMeasure) (x : G E s) :
    HasSum (fun q : Gf E n ⧸ localLevel n A ↦ vacuumCoeff (card m) b (cosetRep q).val *
        S.petersson y' fun g : G E s ↦ y (g * x * (1, (cosetRep q).val)))
      (S.petersson y' fun g : G E s ↦ rallisSeries (card m) b A y (g * x)) := by
  have h_conj : Integrable (fun g : G E s ↦ starRingEnd ℂ (y' g)) S.quotMeasure :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hy'
  unfold Space.petersson
  exact hasSum_integral_mul_rallisSeries h_rank b A hy h_conj (measurable_mul_const x)

/-- Let `2 * card n < card m` and let `b ∘ det` be trivial on the integral points supported on `A`
and its conjugate (`IsUnramifiedOn`). The series `rallisSeries` of a bounded automorphic function
fixed by these points is automorphic: continuous, invariant on the left by the rational points of
`S` and fixed by an open subgroup of the finite points. -/
lemma isAutomorphic_rallisSeries {S : Space E n s} (h_rank : 2 * card n < card m)
    (hb : IsUnramifiedOn b n A) (hy : S.IsAutomorphic y) (hy_bdd : ∃ C : ℝ, ∀ g : G E s, ‖y g‖ ≤ C)
    (h_level : HasLevel y (stdLevel E n ⊓ supportedOn n A)) :
    S.IsAutomorphic (rallisSeries (card m) b A y) where
  continuous := continuous_rallisSeries h_rank b A hy.continuous hy_bdd
  rat_mul δ hδ g := by simp only [← rallisSeries_comp_mul_left, hy.rat_mul δ hδ]
  exists_level := by
    -- The points of a level `K` of `y` that are integral at `A` form a level of the series.
    obtain ⟨K, hK⟩ := hy.exists_level
    refine ⟨K ⊓ ⟨localLevel n A, isOpen_coe_localLevel A⟩, fun k hk ↦ ?_⟩
    obtain ⟨k_mem, k_int⟩ : k ∈ K ∧ k ∈ localLevel n A := hk
    exact rallisSeries_mul_of_mem_localLevel hb (card m) h_level k_int (hK k k_mem)

/-- The series `rallisSeries (card m) b A y` is the sum, over the cosets `q` of the finite points
modulo those integral at `A`, of the right translates of `y` by a representative of `q`, each
weighted by the vacuum coefficient `vacuumCoeff (card m) b`; it keeps the forms of each type. Let
`2 * card n < card m` and let `b ∘ det` be unramified on `A`. Let `y` be a form of type `e` for the
hermitian space `S`, meaning it is automorphic, bounded and, if `e` is integrable, fixed by
convolution with `e` over the real points, and let it be right invariant under the integral points
supported on `A` and its conjugate. Then `rallisSeries (card m) b A y` is a form of type `e` for
`S`. -/
lemma isForm_rallisSeries {S : Space E n s} (h_rank : 2 * card n < card m)
    (hb : IsUnramifiedOn b n A) {e : GInf E s → ℂ} (hy : S.IsForm e y)
    (h_level : HasLevel y (stdLevel E n ⊓ supportedOn n A)) :
    S.IsForm e (rallisSeries (card m) b A y) where
  toIsAutomorphic := isAutomorphic_rallisSeries h_rank hb hy.toIsAutomorphic hy.bounded h_level
  bounded := by
    obtain ⟨C, hC⟩ := hy.bounded
    exact ⟨_, norm_rallisSeries_le h_rank b A hC⟩
  realConv_eq he := by
    rw [realConv_rallisSeries h_rank b A hy.isBoundedMeasurable he, hy.realConv_eq he]

/-- The series `rallisSeries (card m) b A` keeps the forms of each type and level for a hermitian
space `S : Space E n s`. This series is `∑ mc(q) R(q) y`, summed over the cosets `q` of the finite
points integral at `A`, with coefficient `vacuumCoeff (card m) b` and right translation taken at
`cosetRep q`. Let `2 * card n < card m`, let `b ∘ det` be unramified on `A`, and let `J` consist of
points integral at `A` and contain the integral points supported on `A` and its conjugate; then the
series of a form `y` of type `e` for `S` (automorphic, bounded and, if `e` is integrable, fixed by
convolution with `e`) that is fixed by `J` is again a form of type `e` for `S` fixed by `J`. -/
theorem exists_form_eq_rallisSeries {S : Space E n s} (h_rank : 2 * card n < card m)
    (hb : IsUnramifiedOn b n A) {J : Subgroup (Gf E n)} (h_ge : stdLevel E n ⊓ supportedOn n A ≤ J)
    (h_le : J ≤ localLevel n A) {e : GInf E s → ℂ} {y : S.Form e} (hy : HasLevel y J) :
    ∃ z : S.Form e, HasLevel z J ∧ ⇑z = rallisSeries (card m) b A y := by
  have h_form : S.IsForm e (rallisSeries (card m) b A y) :=
    isForm_rallisSeries h_rank hb y.property fun k hk ↦ hy k (h_ge hk)
  exact ⟨⟨_, h_form⟩, hasLevel_rallisSeries hb (card m) h_ge h_le hy, rfl⟩

/-! ### Multiplicativity over the places -/

/-- The series is multiplicative over the places. Let `2 * card n < card m`, let `A₂` be disjoint
from `A₁` and its conjugate, let `b ∘ det` be unramified on `A₁ ∪ A₂`, and let `y` be bounded and
fixed by the integral points supported on `A₁ ∪ A₂` and its conjugate. The series of `y` at
`A₁ ∪ A₂` is the series at `A₁` of the series of `y` at `A₂`. -/
lemma rallisSeries_union {A₁ A₂ : Set (FinPlace E)} (h_rank : 2 * card n < card m)
    (h_disj : Disjoint A₁.conjClosure A₂) (hb : IsUnramifiedOn b n (A₁ ∪ A₂))
    (hy_bdd : ∃ C : ℝ, ∀ g : G E s, ‖y g‖ ≤ C)
    (hy : HasLevel y (stdLevel E n ⊓ supportedOn n (A₁ ∪ A₂))) :
    rallisSeries (card m) b (A₁ ∪ A₂) y =
      rallisSeries (card m) b A₁ (rallisSeries (card m) b A₂ y) := by
  ext g
  obtain ⟨C, hC⟩ := hy_bdd
  let e : (Gf E n ⧸ localLevel n A₁) × (Gf E n ⧸ localLevel n A₂) ≃
      Gf E n ⧸ localLevel n (A₁ ∪ A₂) := .ofBijective _ (bijective_mk_cosetRep_mul h_disj)
  let term (q : Gf E n ⧸ localLevel n (A₁ ∪ A₂)) : ℂ :=
    vacuumCoeff (card m) b (cosetRep q).val * y (g * (1, (cosetRep q).val))
  have h_summable : Summable term :=
    .of_norm_bounded ((summable_norm_vacuumCoeff h_rank b _).mul_right C)
      fun q ↦ norm_mul_le_of_le le_rfl (hC _)
  have h_term (q₁ : Gf E n ⧸ localLevel n A₁) (q₂ : Gf E n ⧸ localLevel n A₂) :
      term (e (q₁, q₂)) = vacuumCoeff (card m) b (cosetRep q₁).val *
        (vacuumCoeff (card m) b (cosetRep q₂).val *
          y (g * (1, (cosetRep q₁).val) * (1, (cosetRep q₂).val))) := by
    have h_supp : (cosetRep q₁).val * (cosetRep q₂).val ∈ supportedOn n (A₁ ∪ A₂) :=
      mul_mem (supportedOn_mono Set.subset_union_left (cosetRep _).property)
        (supportedOn_mono Set.subset_union_right (cosetRep _).property)
    simp only [term, e, Equiv.ofBijective_apply, vacuumCoeff_mul_apply_cosetRep hb _ hy h_supp,
      vacuumCoeff_mul_of_disjoint h_disj _ b (cosetRep q₁).property (cosetRep q₂).property,
      mul_assoc, Prod.mk_mul_mk, mul_one]
  calc rallisSeries (card m) b (A₁ ∪ A₂) y g = ∑' p, term (e p) := (e.tsum_eq term).symm
    _ = ∑' q₁, ∑' q₂, term (e (q₁, q₂)) := (e.summable_iff.2 h_summable).tsum_prod
    _ = _ := by simp only [h_term, tsum_mul_left, rallisSeries]

/-! ### The sum of the coefficients as a product over the places -/

variable (n) in
/-- The sum `∑ mc(q)` of the coefficients of the vacuum `mc = vacuumCoeff M b` over the cosets `q`,
in the finite points, of the subgroup of the points integral at `A`, taken at the representatives
`cosetRep q`. It is the value of the series of the constant function `1` (`rallisSeries_const`),
and it is `0` if the terms are not summable. -/
def vacuumSum (M : ℕ) (b : AutChar E) (A : Set (FinPlace E)) : ℂ :=
  ∑' q : Gf E n ⧸ localLevel n A, vacuumCoeff M b (cosetRep q).val

/-- Translations fix a constant function, so its series is the constant times the sum of the
coefficients of the vacuum. -/
lemma rallisSeries_const (M : ℕ) (b : AutChar E) (A : Set (FinPlace E)) (c : ℂ) :
    rallisSeries M b A (fun _ : G E s ↦ c) = fun _ : G E s ↦ vacuumSum n M b A * c :=
  funext fun _ ↦ tsum_mul_right

omit [WeilData E] in
lemma IsUnramifiedOn.mono (hb : IsUnramifiedOn b n A) {A' : Set (FinPlace E)} (h_sub : A' ⊆ A) :
    IsUnramifiedOn b n A' :=
  fun k hk ↦ hb k (inf_le_inf_left (stdLevel E n) (supportedOn_mono h_sub) hk)

/-- Let `b ∘ det` be unramified on `A`. The coefficient of the vacuum at the chosen representative
of the coset of a point `u` supported on `A` and its conjugate is the coefficient at `u`. -/
lemma vacuumCoeff_cosetRep_mk (hb : IsUnramifiedOn b n A) (M : ℕ) {u : Gf E n}
    (hu : u ∈ supportedOn n A) :
    vacuumCoeff M b (cosetRep (u : Gf E n ⧸ localLevel n A)).val = vacuumCoeff M b u := by
  simpa only [one_mul, mul_inv_cancel_left] using
    vacuumCoeff_mul_mul_of_mem hb M (one_mem _) (inv_mul_cosetRep_mem hu) u

/-- Let `b ∘ det` be unramified on `A`. The sum `vacuumSum` may be computed with any points `r γ`
that are supported on `A` and its conjugate and represent the cosets of the points integral at
`A`. -/
lemma vacuumSum_eq_tsum (hb : IsUnramifiedOn b n A) (M : ℕ) {ι : Type*} {r : ι → Gf E n}
    (h_supp : ∀ γ : ι, r γ ∈ supportedOn n A)
    (h_rep : ∀ g : Gf E n, ∃! γ : ι, (r γ)⁻¹ * g ∈ localLevel n A) :
    vacuumSum n M b A = ∑' γ : ι, vacuumCoeff M b (r γ) := by
  have h_bij : Function.Bijective fun γ : ι ↦ (r γ : Gf E n ⧸ localLevel n A) := by
    refine (Function.bijective_iff_existsUnique _).2 fun q ↦ ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    simpa only [QuotientGroup.eq] using h_rep g
  rw [vacuumSum, ← (Equiv.ofBijective _ h_bij).tsum_eq]
  exact tsum_congr fun γ ↦ vacuumCoeff_cosetRep_mk hb M (h_supp γ)

/-- Over the empty set of places there is one coset, and the sum `vacuumSum` is `1`. -/
lemma vacuumSum_empty (M : ℕ) (b : AutChar E) : vacuumSum n M b ∅ = 1 := by
  have hb : IsUnramifiedOn b n ∅ := by
    rintro k ⟨-, hk_supp⟩
    have hk_one : k = 1 := eq_of_supportedOn hk_supp (one_mem _) (by simp)
    simp [hk_one, Prod.mk_one_one]
  rw [vacuumSum_eq_tsum hb M (r := fun _ : Unit ↦ 1) (fun _ ↦ one_mem _) (by simp [mem_localLevel]),
    vacuumCoeff_eq_one_of_mem hb M (one_mem _), tsum_const, Nat.card_unique, one_smul]

/-- The sum `vacuumSum` is multiplicative over the places. Let `2 * card n < card m`, let `A₂` be
disjoint from `A₁` and its conjugate, and let `b ∘ det` be unramified on `A₁ ∪ A₂`. The sum at
`A₁ ∪ A₂` is the product of the sums at `A₁` and at `A₂`. -/
lemma vacuumSum_union {A₁ A₂ : Set (FinPlace E)} (h_rank : 2 * card n < card m)
    (h_disj : Disjoint A₁.conjClosure A₂) (hb : IsUnramifiedOn b n (A₁ ∪ A₂)) :
    vacuumSum n (card m) b (A₁ ∪ A₂) =
      vacuumSum n (card m) b A₁ * vacuumSum n (card m) b A₂ := by
  let one : G E (1 : n → ℤˣ) → ℂ := fun _ ↦ 1
  have h_series : rallisSeries (card m) b (A₁ ∪ A₂) one =
      rallisSeries (card m) b A₁ (rallisSeries (card m) b A₂ one) :=
    rallisSeries_union h_rank h_disj hb ⟨1, by simp [one]⟩ fun _ _ _ ↦ rfl
  simpa only [one, rallisSeries_const, mul_one] using congrFun h_series 1

/-- Let `2 * card n < card m`, and let `b ∘ det` be trivial on the integral finite points supported
on `A` and its conjugate (`IsUnramifiedOn`). Let `vacuumSum n (card m) b A` be the sum, over the
cosets `q` in the finite adelic unitary group `Gf E n` of the points integral at `A`, of the vacuum
coefficients `(b(det g) * finMultiplier g ^ card m)⁻¹` at the representatives `g = cosetRep q` (and
`0` if the sum is not summable). Then, as the finite set `R` of places grows, `vacuumSum` at `A ∩ R`
tends to `vacuumSum` at `A`. -/
lemma tendsto_vacuumSum_inter (h_rank : 2 * card n < card m) (hb : IsUnramifiedOn b n A) :
    Filter.Tendsto (fun R : Finset (FinPlace E) ↦ vacuumSum n (card m) b (A ∩ R)) Filter.atTop
      (nhds (vacuumSum n (card m) b A)) := by
  -- The cosets at `A ∩ R` embed in those at `A` and exhaust them, as a point is integral off a
  -- finite set; the series at `A` converges absolutely.
  let c (q : Gf E n ⧸ localLevel n A) : ℂ := vacuumCoeff (card m) b (cosetRep q).val
  let incl (R : Finset (FinPlace E)) (q : Gf E n ⧸ localLevel n (A ∩ R)) :
      Gf E n ⧸ localLevel n A := (cosetRep q).val
  have h_inj (R : Finset (FinPlace E)) : Function.Injective (incl R) := by
    intro q q' h_eq
    rw [← mk_cosetRep q, ← mk_cosetRep q', QuotientGroup.eq]
    exact fun w hw ↦ QuotientGroup.eq.1 h_eq w hw.left
  have h_sum (R : Finset (FinPlace E)) :
      ∑' q : Gf E n ⧸ localLevel n A, (Set.range (incl R)).indicator c q =
        vacuumSum n (card m) b (A ∩ R) := by
    rw [← tsum_subtype, tsum_range c (h_inj R)]
    exact tsum_congr fun q ↦
      vacuumCoeff_cosetRep_mk hb _ (supportedOn_mono Set.inter_subset_left (cosetRep q).property)
  have h_exhaust (g : Gf E n) :
      ∀ᶠ R : Finset (FinPlace E) in Filter.atTop, ↑g ∈ Set.range (incl R) := by
    have h_finite : {w : FinPlace E | g.atPlace w ∉ localIntGL n w}.Finite :=
      eventually_atPlace_mem_localIntGL
    filter_upwards [Filter.eventually_ge_atTop h_finite.toFinset] with R hR
    let r : supportedOn n (A ∩ R) := cosetRep (g : Gf E n ⧸ localLevel n (A ∩ R))
    have hr : r.val⁻¹ * g ∈ localLevel n (A ∩ R) := QuotientGroup.eq.1 (mk_cosetRep _)
    refine ⟨g, QuotientGroup.eq.2 fun w hw ↦ ?_⟩
    change (r.val⁻¹ * g).atPlace w ∈ localIntGL n w
    by_cases hw_mem : w ∈ A ∩ R
    · exact hr w hw_mem
    by_cases hw_star : star w ∈ A ∩ R
    · exact atPlace_star_mem_iff.1 (hr _ hw_star)
    · have hg : g.atPlace w ∈ localIntGL n w :=
        by_contra fun h_not ↦ hw_mem ⟨hw, hR (h_finite.mem_toFinset.2 h_not)⟩
      simpa [mem_supportedOn.1 r.property w hw_mem hw_star] using hg
  simp only [← h_sum]
  refine tendsto_tsum_of_dominated_convergence (summable_norm_vacuumCoeff h_rank b A)
    (fun q ↦ ?_) (.of_forall fun R q ↦ norm_indicator_le_norm_self c q)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact tendsto_const_nhds.congr' ((h_exhaust g).mono fun R hR ↦ (Set.indicator_of_mem hR c).symm)

open scoped Classical in
/-- Let `vacuumSum n (card m) b A` be the sum, over the cosets `q` in `Gf E n` of the points
integral at `A`, of the vacuum coefficients `(b(det g) * finMultiplier g ^ card m)⁻¹` at
`g = cosetRep q`. It is a product over the pairs of conjugate places: let `2 * card n < card m`, let
`A` be stable under conjugation, and let `b ∘ det` be unramified on `A`; let the factors `loc w` be
`1` off `A` and have product `L`. If for each `w` in `A` the sum at `{w, w̄}` is `loc w * loc w̄` (a
single factor when `w = w̄`), then the sum at `A` is `L`. -/
lemma vacuumSum_eq_of_hasProd (h_rank : 2 * card n < card m)
    (hA : ∀ w : FinPlace E, star w ∈ A ↔ w ∈ A) (hb : IsUnramifiedOn b n A)
    {loc : FinPlace E → ℂ} {L : ℂ} (h_prod : HasProd loc L)
    (h_off : ∀ w : FinPlace E, w ∉ A → loc w = 1)
    (h_pair : ∀ w : FinPlace E, w ∈ A → vacuumSum n (card m) b {w, star w} =
      ∏ u ∈ ({w, star w} : Finset (FinPlace E)), loc u) :
    vacuumSum n (card m) b A = L := by
  -- `T R` consists of the places of `R` and their conjugates; add the places of `R` one by one.
  let T (R : Finset (FinPlace E)) : Finset (FinPlace E) := R.image star ∪ R
  have h_mem (R : Finset (FinPlace E)) (u : FinPlace E) : u ∈ T R ↔ star u ∈ R ∨ u ∈ R := by
    simp [T, star_involutive.eq_iff]
  have h_finite (R : Finset (FinPlace E)) :
      vacuumSum n (card m) b (A ∩ T R) = ∏ u ∈ T R, loc u := by
    induction R using Finset.induction with
    | empty => simp [T, vacuumSum_empty, Set.inter_empty]
    | insert w R _ ih =>
      have h_insert : T (insert w R) = {w, star w} ∪ T R := by simp [T]
      have h_star : star w ∈ T R ↔ w ∈ T R := by simp [h_mem, or_comm]
      by_cases hw : w ∈ T R
      · have h_subset : {w, star w} ⊆ T R := by simp [Finset.insert_subset_iff, hw, h_star]
        rwa [h_insert, Finset.union_eq_right.2 h_subset]
      have h_disj : Disjoint {w, star w} (T R) := by simp [hw, h_star]
      rw [h_insert, Finset.prod_union h_disj, ← ih, Finset.coe_union, Finset.coe_pair,
        Set.inter_union_distrib_left]
      by_cases hw_mem : w ∈ A
      · have h_sub : {w, star w} ⊆ A := Set.pair_subset hw_mem ((hA w).2 hw_mem)
        have h_closure : ({w, star w} : Set (FinPlace E)).conjClosure = {w, star w} := by
          ext u
          simp [star_involutive.eq_iff, or_comm]
        have h_disj_conj : Disjoint ({w, star w} : Set (FinPlace E)).conjClosure (A ∩ T R) := by
          rw [h_closure, ← Finset.coe_pair]
          exact (Finset.disjoint_coe.2 h_disj).mono_right Set.inter_subset_right
        have hb_union : IsUnramifiedOn b n ({w, star w} ∪ A ∩ T R) :=
          hb.mono (Set.union_subset h_sub Set.inter_subset_left)
        rw [Set.inter_eq_right.2 h_sub, vacuumSum_union h_rank h_disj_conj hb_union,
          h_pair w hw_mem]
      · have hw_star : star w ∉ A := (hA w).not.2 hw_mem
        have h_one : ∏ u ∈ {w, star w}, loc u = 1 :=
          Finset.prod_eq_one (by simp [h_off, hw_mem, hw_star])
        simp [h_one, Set.inter_insert_of_notMem hw_mem, hw_star]
  -- Let `R` exhaust the places.
  have h_frequently : ∃ᶠ R : Finset (FinPlace E) in Filter.atTop,
      vacuumSum n (card m) b (A ∩ R) = ∏ u ∈ R, loc u :=
    Filter.frequently_atTop.2 fun R ↦ ⟨T R, le_sup_right, h_finite R⟩
  exact tendsto_nhds_unique_of_frequently_eq (tendsto_vacuumSum_inter h_rank hb) h_prod
    h_frequently

end New.SiegelWeil
end
end
end

section
/-!
# The dual datum of a vacuum

For hermitian spaces `S`, `T` of ranks `n`, `m` with `2 n ≤ m`, a finite set `A` of places and a
datum `f` on `Hom(S, T)` that is a vacuum above `A` (fixed by `New.Space.projOn A`), this file
constructs a second datum `f'` whose matrix coefficient `g ↦ ⟨f', ω(g, 1) f⟩` is that of `f` on the
points integral at `A` and zero elsewhere (`New.SiegelWeil.exists_dualDatum`).

The datum is `ϱ(e) ω(κ) f` up to a scalar: `κ = 1 + z x xᴴ` (`New.SiegelWeil.isotropicShear`) is a
unitary of `T` along an integral isotropic frame `x`
(`New.SiegelWeil.exists_integral_isotropic_frame`), with `z̄ = -z` large at `A` and its conjugate
(`New.SiegelWeil.exists_skew_adele`), and `ϱ(e)` is the finite Heisenberg operator of the rows of
`x` that form the identity. Where the coefficient at `g` is not zero, the Heisenberg operators
fixing both `ω(κ) f` and `ω(g) f` act on `f'` by characters that must be trivial, and self-duality
of `Ô` (`New.stdLattice.forall_selfDualAddChar_mul_eq_one_iff`) then forces `g⁻¹` to be integral at
`A` and its conjugate.

## Main results

* `New.SiegelWeil.exists_dualDatum`: the dual datum.
-/

@[expose] public section

noncomputable section

open Matrix Kronecker

namespace New.SiegelWeil

open WeilData Fintype Space Prod G Gf stdLattice Valued

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] {s : n → ℤˣ} {t : m → ℤˣ} {S : Space E n s} {T : Space E m t}

omit [CMType E] in
/-- For a place `w` and `μ ≠ 0` in `E_w`, a finite adele `y` times the adele with component `μ⁻¹`
at `w` and `0` elsewhere is integral if and only if `v (y w) ≤ v μ`. -/
lemma mul_singleAdele_inv_mem_Ô [NumberField E] {w : FinPlace E} {μ : LocField w} (hμ : μ ≠ 0)
    (y : 𝔸f E) : y * singleAdele w μ⁻¹ ∈ Ô E ↔ v (y w) ≤ v μ := by
  rw [mem_Ô]
  refine ⟨fun h ↦ ?_, fun h u ↦ ?_⟩
  · have h_w := h w
    rwa [show (y * singleAdele w μ⁻¹) w = y w * μ⁻¹ from by simp, map_mul, map_inv₀,
      mul_inv_le_iff₀ (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff _).2 hμ)), one_mul] at h_w
  · by_cases hu : u = w
    · subst hu
      rw [show (y * singleAdele u μ⁻¹) u = y u * μ⁻¹ from by simp, map_mul, map_inv₀,
        mul_inv_le_iff₀ (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff _).2 hμ)), one_mul]
      exact h
    · simp [hu]

/-- Let `A` be a finite set of places. There is a finite adele `z` with `z̄ = -z`, zero outside `A`
and its conjugate, and with `v (z w) > 1` at every place `w` of `A` and its conjugate: `j / N`
there for a suitable natural number `N`, with `j` the imaginary element of the Weil data. -/
lemma exists_skew_adele {A : Set (FinPlace E)} (hA : A.Finite) :
    ∃ z : 𝔸f E, star z = -z ∧ idem A.conjClosure * z = z ∧
      ∀ w ∈ A.conjClosure, 1 < v (z w) := by
  classical
  have : Finite A.conjClosure := hA.conjClosure.to_subtype
  -- `N` carries the adeles `ϖ_w⁻¹ j⁻¹`, for `w` in `A` and its conjugate, into `Ô E`; then
  -- `v (N) ≤ v (ϖ_w j) < v (j)` at `w`, so `j / N` is large there.
  obtain ⟨N, hN, h_int⟩ := exists_forall_mul_mem_Ô fun w : A.conjClosure ↦
    singleAdele w.val (uniformizer w.val).val⁻¹ * algebraMap E (𝔸f E) j⁻¹
  refine ⟨idem A.conjClosure * algebraMap E (𝔸f E) (j / N), ?_, ?_, fun w hw ↦ ?_⟩
  · rw [star_mul', star_idem_conjClosure, star_algebraMap_finAdele, star_div₀, WeilData.star_j,
      star_natCast, neg_div, map_neg, mul_neg]
  · rw [← mul_assoc, idem_mul_self]
  · -- Read everything in `E_w`, through `φ : E → E_w`.
    let φ : E →+* LocField w := algebraMap E (LocField w)
    have h_coe (y : E) : (algebraMap E (𝔸f E) y) w = φ y := rfl
    have h_w := mem_Ô.1 (h_int ⟨w, hw⟩) w
    rw [finAdele_mul_apply, finAdele_mul_apply, finAdele_natCast_apply, singleAdele_same, h_coe,
      map_inv₀, map_mul, map_mul, map_inv₀, map_inv₀, ← mul_inv] at h_w
    rw [finAdele_mul_apply, idem_of_mem hw, one_mul, h_coe, map_div₀, map_natCast]
    have hJ : v (φ j) ≠ 0 := (Valuation.ne_zero_iff _).2 ((map_ne_zero φ).2 j_ne_zero)
    have hN' : v (N : LocField w) ≠ 0 := (Valuation.ne_zero_iff _).2 (by
      rw [← map_natCast φ]; exact (map_ne_zero φ).2 (Nat.cast_ne_zero.2 hN))
    rw [mul_inv_le_iff₀ (pos_iff_ne_zero.2 (mul_ne_zero (by simp) hJ)), one_mul,
      v_uniformizer] at h_w
    rw [map_div₀, lt_div_iff₀ (pos_iff_ne_zero.2 hN'), one_mul]
    exact h_w.trans_lt (mul_lt_of_lt_one_left (pos_iff_ne_zero.2 hJ) (by decide))

omit [WeilData E] [DecidableEq n] in
/-- If `z̄ = -z` and `xᴴ x = 0`, the matrix `1 + z x xᴴ` is unitary: `x xᴴ` is hermitian with
square `x (xᴴ x) xᴴ = 0`. -/
lemma conjTranspose_mul_isotropicShear {z : 𝔸f E} (hz : star z = -z) {x : Matrix m n (𝔸f E)}
    (hx : xᴴ * x = 0) : (1 + z • (x * xᴴ))ᴴ * 1 * (1 + z • (x * xᴴ)) = 1 := by
  have h_sq : x * xᴴ * (x * xᴴ) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc xᴴ, hx, Matrix.zero_mul, Matrix.mul_zero]
  have h_adj : (1 + z • (x * xᴴ))ᴴ = 1 - z • (x * xᴴ) := by
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, conjTranspose_mul,
      conjTranspose_conjTranspose, hz, neg_smul, sub_eq_add_neg]
  have h_sq' : z • (x * xᴴ) * (z • (x * xᴴ)) = 0 := by rw [smul_mul_smul_comm, h_sq, smul_zero]
  rw [h_adj, Matrix.mul_one]
  calc (1 - z • (x * xᴴ)) * (1 + z • (x * xᴴ)) = 1 - z • (x * xᴴ) * (z • (x * xᴴ)) := by
        rw [sub_mul, one_mul, mul_add, mul_one]
        abel
    _ = 1 := by rw [h_sq', sub_zero]

/-- The shear `1 + z x xᴴ` as an element of the finite unitary group, for `z̄ = -z` and an
isotropic frame `x` (`xᴴ x = 0`). -/
def isotropicShear {z : 𝔸f E} (hz : star z = -z) {x : Matrix m n (𝔸f E)} (hx : xᴴ * x = 0) :
    Gf E m :=
  U.of isUnit_one (1 + z • (x * xᴴ)) (conjTranspose_mul_isotropicShear hz hx)

omit [WeilData E] [DecidableEq n] in
/-- The matrix of `isotropicShear hz hx` is `1 + z x xᴴ`. -/
lemma coe_isotropicShear {z : 𝔸f E} (hz : star z = -z) {x : Matrix m n (𝔸f E)} (hx : xᴴ * x = 0) :
    ((isotropicShear hz hx : Gf E m) : Matrix m m (𝔸f E)) = 1 + z • (x * xᴴ) := rfl

omit [WeilData E] [DecidableEq n] in
/-- If `z` is zero outside `A` and its conjugate, the shear `1 + z x xᴴ` is supported there. -/
lemma isotropicShear_mem_supportedOn {A : Set (FinPlace E)} {z : 𝔸f E} (hz : star z = -z)
    (hz_supp : idem A.conjClosure * z = z) {x : Matrix m n (𝔸f E)} (hx : xᴴ * x = 0) :
    isotropicShear hz hx ∈ supportedOn m A := by
  classical
  rw [Gf.mem_supportedOn]
  intro w hw hw_star
  have hzw : z w = 0 := by
    rw [← hz_supp, finAdele_mul_apply, idem_apply,
      ite_eq_right (by simp [Set.conjClosure, hw, hw_star]), zero_mul]
  refine Units.ext (Matrix.ext fun i k ↦ ?_)
  simp [Gf.atPlace, coe_isotropicShear, hzw, Matrix.one_apply, apply_ite (fun y : 𝔸f E ↦ y w)]

omit [CMType E] [WeilData E] in
/-- For matrices over a commutative ring, the entry `(p, k)` of `M * E_{r i}(a) * N`, with
`E_{r i}(a)` the matrix with the single entry `a` at `(r, i)`, is `M p r * a * N i k`. -/
lemma mul_single_mul_apply {R : Type*} [CommRing R] (M : Matrix m m R) (r : m) (i : n) (a : R)
    (N : Matrix n n R) (p : m) (k : n) : (M * single r i a * N) p k = M p r * a * N i k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [mul_single_apply_same]
  · intro c _ hc
    rw [mul_single_apply_of_ne (hbj := hc), zero_mul]
  · simp

omit [DecidableEq n] [CMType E] [WeilData E] in
/-- Let `u` embed `n` into `m`, and let `F` be the matrix with entry `1` at the places `(u k, k)`
and `0` elsewhere. The pairing of `F` with a matrix `M`, read as vectors, is `∑ k, M (u k) k`. -/
lemma star_frame_dotProduct {R : Type*} [CommRing R] [StarRing R] (u : n ↪ m)
    (M : Matrix m n R) :
    star (matrixToVec (of fun r k ↦ if r = u k then (1 : R) else 0)) ⬝ᵥ matrixToVec M =
      ∑ k, M (u k) k := by
  rw [dotProduct, Fintype.sum_prod_type, Finset.sum_comm]
  simp [matrixToVec, apply_ite star]

omit [WeilData E] in
/-- The points of `G_f` whose inverse has integral entries at every place of `A` and its conjugate
are integral at `A`: by unitarity `g` is the conjugate transpose of `g⁻¹`, and conjugation
exchanges a place with its conjugate. -/
lemma mem_localLevel_of_inv {A : Set (FinPlace E)} {g : Gf E n}
    (h : ∀ w ∈ A.conjClosure, ∀ i k : n, v (((g⁻¹ : Gf E n) : Matrix n n (𝔸f E)) i k w) ≤ 1) :
    g ∈ localLevel n A := by
  intro w hw
  have h_val : (g : Matrix n n (𝔸f E)) = ((g⁻¹ : Gf E n) : Matrix n n (𝔸f E))ᴴ := by
    simpa using U.inv_val_eq_conjTranspose g⁻¹
  refine mem_intGL.2 ⟨fun i k ↦ mem_LocInt.2 ?_, fun i k ↦ mem_LocInt.2 ?_⟩
  · change v ((g : Matrix n n (𝔸f E)) i k w) ≤ 1
    rw [h_val, conjTranspose_apply, finAdele_star_apply, v_conjLoc]
    exact h (star w) (Or.inr (by simpa using hw)) k i
  · rw [← map_inv]
    exact h w (Or.inl hw) i k

omit [WeilData E] in
/-- In `Hom(S, T)`, read as `m × n` matrices, the finite part of `onHom (g, h)` acts by
`X ↦ h X g⁻¹`. -/
lemma onHom_snd_mulVec_matrixToVec (p : G E s × G E t) (X : Matrix m n (𝔸f E)) :
    ((onHom p).2 : Matrix (m × n) (m × n) (𝔸f E)) *ᵥ matrixToVec X =
      matrixToVec ((p.2.2 : Matrix m m (𝔸f E)) * X * ((p.1.2⁻¹ : Gf E n) : Matrix n n (𝔸f E))) := by
  rw [onHom_snd, kronecker_mulVec_eq_matrixToVec, vecToMatrix_matrixToVec]

/-- Let `f` be a vacuum above `A` (fixed by `projOn A`) and `p` a point of the unitary group. Then
`ω(p) f` is fixed by the finite Heisenberg operator of `idem (A ∪ Ā) • p y` for every integral
vector `y`. -/
lemma finHeisenbergOp_omega_of_projOn {k : Type} [Fintype k] [DecidableEq k] {r : k → ℤˣ}
    {V : Space E k r} {A : Set (FinPlace E)} {f : 𝒮 V} (hf : V.projOn A f = f) (p : G E r)
    {y : k → 𝔸f E} (hy : y ∈ stdLattice E k) :
    V.finHeisenbergOp (idem A.conjClosure • ((p.2 : Matrix k k (𝔸f E)) *ᵥ y)) (V.ω p f) =
      V.ω p f := by
  have h_fix : V.finHeisenbergOp (idem A.conjClosure • y) f = f := by
    simpa [hf] using V.finHeisenbergOp_projOn (S := A) hy f
  conv_rhs => rw [← h_fix]
  rw [omega_finHeisenbergOp, Matrix.mulVec_smul]

/-- If finite Heisenberg operators `ϱ(e)` and `ϱ(Y)` are given, and `ϱ(Y)` fixes `f₀` and `u`, then
`ϱ(Y)` multiplies `ϱ(e) f₀` by `ψ(ē ⬝ Y)`; so if `⟨ϱ(e) f₀, u⟩ ≠ 0`, then `ψ(ē ⬝ Y) = 1`. Here
`ψ = selfDualAddChar E`. -/
lemma selfDualAddChar_eq_one_of_dataInner_ne_zero {k : Type} [Fintype k] [DecidableEq k]
    {r : k → ℤˣ} {V : Space E k r} {e Y : k → 𝔸f E} {f₀ u : 𝒮 V}
    (h₀ : V.finHeisenbergOp Y f₀ = f₀) (hu : V.finHeisenbergOp Y u = u)
    (h_ne : V.dataInner (V.finHeisenbergOp e f₀) u ≠ 0) :
    selfDualAddChar E (star e ⬝ᵥ Y) = 1 := by
  have h := V.dataInner_finHeisenbergOp Y (V.finHeisenbergOp e f₀) u
  rw [finHeisenbergOp_comm, h₀, hu, map_smulₛₗ, _root_.smul_apply, smul_eq_mul] at h
  have h_conj : (starRingEnd ℂ) (selfDualAddChar E (star e ⬝ᵥ Y) : ℂ) = 1 :=
    (mul_eq_right₀ h_ne).1 h
  simpa using congrArg (starRingEnd ℂ) h_conj

open scoped Classical in
/-- The dual datum. Let `2 rk S ≤ rk T`, let `A` be a finite set of places and let `f` be a vacuum
above `A` (fixed by `projOn A`). There is a datum `f'` whose matrix coefficient
`g ↦ ⟨f', ω(g, 1) f⟩` against `f` equals that of `f` at the points `g` integral at `A` and is zero
at the others.

The datum is `f' = ϱ(e) ω(κ) f`, up to a scalar: `κ = 1 + z x xᴴ` is a shear of `T` along an
integral isotropic frame `x`, with `z` large at `A` and its conjugate (`exists_skew_adele`), and
`ϱ(e)` is the finite Heisenberg operator of the rows of `x` that form the identity. If the
coefficient at `g` is not zero, the Heisenberg operators that fix both `ω(κ) f` and `ω(g) f` act on
`f'` by characters that must be trivial, and this forces `g⁻¹` to be integral at `A`. -/
theorem exists_dualDatum (b : AutChar E) (h_rank : 2 * card n ≤ card m) {f : 𝒮 (S.hom T)}
    {A : Set (FinPlace E)} (hf : projOn (S.hom T) A f = f) (hA : A.Finite) :
    ∃ f' : 𝒮 (S.hom T), ∀ g : G E s,
      weilMatrixCoeff b f f' g = if g.2 ∈ localLevel n A then weilMatrixCoeff b f f g else 0 := by
  obtain ⟨x, hx_int, hx_iso, u, hu⟩ := exists_integral_isotropic_frame (E := E) h_rank
  obtain ⟨z, hz_star, hz_supp, hz_big⟩ := exists_skew_adele hA
  let κ : Gf E m := isotropicShear hz_star hx_iso
  -- `K` acts on `Hom(S, T)` by `X ↦ κ X`; it is supported on `A` and its conjugate.
  let K : Gf E (m × n) := (onHom ((1 : G E s), ((1, κ) : G E t))).2
  have hK_supp : K ∈ supportedOn (m × n) A :=
    onHom_mem_supportedOn (one_mem _) (isotropicShear_mem_supportedOn hz_star hz_supp hx_iso)
  have hK_act (X : Matrix m n (𝔸f E)) :
      (K : Matrix (m × n) (m × n) (𝔸f E)) *ᵥ matrixToVec X =
        matrixToVec ((κ : Matrix m m (𝔸f E)) * X) := by
    simp [K, onHom_snd_mulVec_matrixToVec]
  let f₀ : 𝒮 (S.hom T) := finMultiplier K⁻¹ • (S.hom T).ω (K : G E (homSigns s t)) f
  have h_proj₀ : (S.hom T).projOn A f₀ = f := by
    rw [map_smul, projOn_omega (S.hom T) hK_supp hf, smul_smul,
      mul_inv_cancel₀ (finMultiplier_ne_zero _), one_smul]
  -- the frame vector: the matrix with `1` at the places `(u k, k)`, cut to `A` and its conjugate
  let F : Matrix m n (𝔸f E) := of fun r k ↦ if r = u k then 1 else 0
  have hF_int : matrixToVec F ∈ stdLattice E (m × n) := by
    rw [mem_stdLattice]
    rintro ⟨r, k⟩
    simp [F, matrixToVec, ite_mem]
  let e : m × n → 𝔸f E := idem A.conjClosure • matrixToVec F
  refine ⟨(S.hom T).finHeisenbergOp e f₀, fun g ↦ ?_⟩
  set w₀ : 𝒮 (S.hom T) := pairWeil S T 1 b (g, 1) f with hw₀
  split_ifs with hg
  · -- At `g` integral at `A`, `ω(g) f` is a vacuum above `A`, fixed by `ϱ(e)` and `projOn A`.
    have h_vac : (S.hom T).projOn A w₀ = w₀ :=
      projOn_pairWeil hf (g, 1) fun w hw ↦ onHom_atPlace_mem (hg w hw) (by simp)
    have h_e : (S.hom T).finHeisenbergOp e w₀ = w₀ := by
      conv_lhs => rw [← h_vac]
      rw [(S.hom T).finHeisenbergOp_projOn hF_int, h_vac]
    calc weilMatrixCoeff b f ((S.hom T).finHeisenbergOp e f₀) g
        = (S.hom T).dataInner ((S.hom T).finHeisenbergOp e f₀)
            ((S.hom T).finHeisenbergOp e w₀) := by rw [h_e]
      _ = (S.hom T).dataInner f₀ ((S.hom T).projOn A w₀) := by rw [dataInner_finHeisenbergOp, h_vac]
      _ = weilMatrixCoeff b f f g := by rw [← dataInner_projOn, h_proj₀]
  · -- Otherwise suppose the coefficient is not zero; then `g⁻¹` is integral at `A ∪ Ā`.
    by_contra h_ne
    apply hg
    have h_ne' : (S.hom T).dataInner ((S.hom T).finHeisenbergOp e f₀)
        ((S.hom T).ω (onHom (g, (1 : G E t))) f) ≠ 0 := by
      intro h_zero
      apply h_ne
      change (S.hom T).dataInner _ (pairWeil S T 1 b (g, 1) f) = 0
      rw [pairWeil_apply, map_smul, h_zero, smul_zero]
    have hP_act (X : Matrix m n (𝔸f E)) :
        ((onHom (g, (1 : G E t))).2 : Matrix (m × n) (m × n) (𝔸f E)) *ᵥ matrixToVec X =
          matrixToVec (X * ((g.2⁻¹ : Gf E n) : Matrix n n (𝔸f E))) := by
      simp [onHom_snd_mulVec_matrixToVec]
    refine mem_localLevel_of_inv fun w hw i k ↦ ?_
    set h : Matrix n n (𝔸f E) := ((g.2⁻¹ : Gf E n) : Matrix n n (𝔸f E))
    by_contra h_big
    rw [not_le] at h_big
    have : Nonempty n := ⟨i⟩
    -- a largest entry `h i l` of the row `i` at `w`, and `μ` with `v μ = max (v (z w)) (v (h i l))`
    obtain ⟨l, hl⟩ := Finite.exists_max fun l ↦ v (h i l w)
    have h_il : 1 < v (h i l w) := h_big.trans_le (hl k)
    have hz_w : 1 < v (z w) := hz_big w hw
    let μ : LocField w := if v (z w) ≤ v (h i l w) then h i l w else z w
    have hμ : v μ = max (v (z w)) (v (h i l w)) := by
      by_cases h_le : v (z w) ≤ v (h i l w)
      · simp [μ, h_le]
      · simp [μ, h_le, max_eq_left (le_of_not_ge h_le)]
    have hμ_one : 1 < v μ := hμ ▸ hz_w.trans_le (le_max_left _ _)
    have hμ_ne : μ ≠ 0 := (Valuation.ne_zero_iff _).1 (ne_of_gt (zero_lt_one.trans hμ_one))
    set σ : 𝔸f E := singleAdele w μ⁻¹
    have hσ (y : 𝔸f E) : y * σ ∈ Ô E ↔ v (y w) ≤ v μ := mul_singleAdele_inv_mem_Ô hμ_ne y
    have hσ_idem : idem A.conjClosure * σ = σ := by
      ext u'
      by_cases hu' : u' = w
      · subst hu'; simp [σ, hw]
      · simp [σ, hu']
    -- the integrality of the vectors used below
    have hσ_int : σ ∈ Ô E := by simpa using (hσ 1).2 (by simpa using hμ_one.le)
    have hzσ_int : z * σ ∈ Ô E := (hσ z).2 (hμ ▸ le_max_left _ _)
    have hhσ_int (k' : n) : h i k' * σ ∈ Ô E := (hσ _).2 (hμ ▸ (hl k').trans (le_max_right _ _))
    -- `κ` applied to the single entry `d σ` at `(u l, i)`
    have hκ_entry (r : m) :
        (κ : Matrix m m (𝔸f E)) r (u l) = (if r = u l then 1 else 0) + z * x r l := by
      simp [κ, coe_isotropicShear, Matrix.one_apply, Matrix.mul_apply, conjTranspose_apply, hu,
        Pi.single_apply, apply_ite star]
    -- For every integral `d`, the character of `ē ⬝ Y` is trivial, `Y = κ E_{u l, i}(d σ) h`.
    have h_char (d : 𝔸f E) (hd : d ∈ Ô E) :
        selfDualAddChar E (idem A.conjClosure * ((1 + z) * (d * σ) * h i l)) = 1 := by
      let D : Matrix m n (𝔸f E) := single (u l) i (d * σ)
      let Y : m × n → 𝔸f E := idem A.conjClosure •
        matrixToVec ((κ : Matrix m m (𝔸f E)) * D * h)
      have hY₀ : (S.hom T).finHeisenbergOp Y f₀ = f₀ := by
        have h_lat : matrixToVec (D * h) ∈ stdLattice E (m × n) := by
          rw [mem_stdLattice]
          rintro ⟨r, k'⟩
          by_cases hr : r = u l
          · subst hr
            simpa [D, matrixToVec, Matrix.single_mul_apply_same, mul_assoc, mul_comm σ] using
              mul_mem hd (hhσ_int k')
          · simp [D, matrixToVec, Matrix.single_mul_apply_of_ne (h := hr)]
        have := finHeisenbergOp_omega_of_projOn hf ((1, K) : G E (homSigns s t)) h_lat
        rw [map_smul]
        simp only [hK_act] at this
        simp only [Y, Matrix.mul_assoc, this]
        rfl
      have hYu : (S.hom T).finHeisenbergOp Y ((S.hom T).ω (onHom (g, (1 : G E t))) f) =
          (S.hom T).ω (onHom (g, (1 : G E t))) f := by
        have h_lat : matrixToVec ((κ : Matrix m m (𝔸f E)) * D) ∈ stdLattice E (m × n) := by
          rw [mem_stdLattice]
          rintro ⟨r, k'⟩
          by_cases hk' : k' = i
          · subst hk'
            simp only [D, matrixToVec, mul_single_apply_same, hκ_entry, add_mul]
            refine add_mem (mul_mem (by simp [ite_mem]) (mul_mem hd hσ_int)) ?_
            rw [show z * x r l * (d * σ) = x r l * d * (z * σ) by ring]
            exact mul_mem (mul_mem (hx_int r l) hd) hzσ_int
          · simp [D, matrixToVec, mul_single_apply_of_ne (hbj := hk')]
        simpa [hP_act] using finHeisenbergOp_omega_of_projOn hf (onHom (g, (1 : G E t))) h_lat
      have h_one := selfDualAddChar_eq_one_of_dataInner_ne_zero hY₀ hYu h_ne'
      have h_dot : star e ⬝ᵥ Y = idem A.conjClosure * ((1 + z) * (d * σ) * h i l) := by
        change star (idem A.conjClosure •
            matrixToVec (of fun r k ↦ if r = u k then (1 : 𝔸f E) else 0)) ⬝ᵥ
          (idem A.conjClosure •
            matrixToVec ((κ : Matrix m m (𝔸f E)) * single (u l) i (d * σ) * h)) = _
        rw [star_smul, smul_dotProduct, dotProduct_smul, star_frame_dotProduct,
          star_idem_conjClosure, smul_eq_mul, smul_eq_mul, ← mul_assoc, idem_mul_self]
        congr 1
        simp only [mul_single_mul_apply, hκ_entry, hu, Pi.single_apply, u.injective.eq_iff,
          add_mul, Finset.sum_add_distrib]
        simp
      rwa [h_dot] at h_one
    -- so `z σ h i l` is integral, against the choice of `μ`
    have h_mem : z * h i l * σ ∈ Ô E := by
      refine (forall_selfDualAddChar_mul_eq_one_iff _).1 fun d hd ↦ ?_
      have h_split := h_char d hd
      rw [show idem A.conjClosure * ((1 + z) * (d * σ) * h i l) =
          d * (h i l * σ) + z * h i l * σ * d by
        rw [show idem A.conjClosure * ((1 + z) * (d * σ) * h i l) =
          (1 + z) * d * h i l * (idem A.conjClosure * σ) by ring, hσ_idem]
        ring,
        AddChar.map_add_eq_mul, selfDualAddChar_eq_one_of_mem (mul_mem hd (hhσ_int l)), one_mul]
        at h_split
      exact h_split
    have h_le := (hσ _).1 h_mem
    rw [finAdele_mul_apply, map_mul, hμ] at h_le
    exact (max_lt (lt_mul_of_one_lt_right (zero_lt_one.trans hz_w) h_il)
      (lt_mul_of_one_lt_left (zero_lt_one.trans h_il) hz_w)).not_ge h_le

end New.SiegelWeil
end
end
end

/-!
# Rallis' inner product formula for sharp data and injectivity of the theta lift

This file proves Rallis' inner product formula for the theta lift `New.Space.lift` from `U(S)` to
`U(T)` when `rk T > 2 rk S`, for data `v ⊗ F` with `F` sharp (`New.SiegelWeil.IsSharp`). It starts
from `New.SiegelWeil.inner_product_formula`. For `v` an edge from type `e`, the lift is injective
on `J`-invariant forms of type `e`. The file then derives `IsSharp` from `New.SiegelWeil.IsSharpFn`,
a condition on a level `J` and a function `Ψ` on matrices modulo 𝔪, if all signs of `S` agree or
𝔪 ≠ (1), with `S₀` the set of places of 𝔪𝔪̄ and the mass `c` the mean of `|Ψ|²` over the index of
`J`. Finally it computes the vacuum sum in rank one as a partial Hecke L-value over a partial
Euler product.

## Main definitions and results

* `New.SiegelWeil.IsSharp.petersson_lift_eq_integral`: for a sharp datum the Petersson product
  (`New.Space.petersson`) of two lifts is a real integral against the series
  `New.SiegelWeil.rallisSeries` of the places off `S₀`. The finite points are cut into cosets in
  `New.SiegelWeil.IsSharp.hasSum_integral_weilMatrixCoeff_mul`.
* `New.SiegelWeil.exists_petersson_formLift_eq_rallisSeries`: for `v` an edge (`New.IsEdge`) from
  type `e`, the lift is injective on `J`-invariant forms of type `e`, and the product of two lifts
  is a multiple of the pairing with the series; `New.SiegelWeil.rallis_inner_product_cosetTerm`
  expands the series.
* `New.SiegelWeil.IsSharpFn.isSharp`: if all signs of `S` agree or 𝔪 ≠ (1), a function on matrices
  modulo 𝔪 that is sharp for a level J (`New.SiegelWeil.IsSharpFn`) gives a finite datum whose
  matrix coefficient is constant on J and zero at the other points integral off 𝔪𝔪̄
  (`New.SiegelWeil.IsSharp`). `New.SiegelWeil.isSharp_vacuumDatum_of_mul_eq_one` is the case of the
  principal level.
* `New.vacuumSum_eq_L_div_eulerProd`: in rank one and for target rank 2k with k > 1, the sum
  `New.SiegelWeil.vacuumSum` of the vacuum coefficient over the cosets at the places off a set and
  its conjugate, where the tame part is trivial, is a partial Hecke L-value at k over the partial
  Euler product of the signs `New.placeSign` (a partial value of ζ_F at 2k if E is unramified
  over its real subfield F).

Notions from other files:
* `New.Space.integrated`: the datum v ⊗ F = ∫ v(y) ϱ(y) F dy, for v in the Fock model and ϱ the
  Heisenberg operators of the real vectors y.
* `New.IsEdge`: what the formula uses of the real vector v and the types e, e'. The vector of the
  joint harmonic of corresponding parameters is an edge between the types of these parameters
  (`New.ParamsCorrespond.isEdge_jointHarmonic`).
* `New.Modulus.liftFn`: a function of vectors modulo 𝔪, read on finite adelic vectors: its value at
  the reduction if the components at the places of 𝔪 are integral, and 0 otherwise.
* `New.SiegelWeil.IsSharp` (from `Lib.SiegelWeil.RallisInner.Doubling`): `F` is a vacuum off a
  set `S₀` of places; at the finite points integral off `S₀` the coefficient `⟨F, ω(g) F⟩` is
  `⟨F, F⟩` on `J ∩ stdLevel E n` and zero otherwise, and `⟨F, F⟩` over the index of
  `J ∩ stdLevel E n` in `stdLevel E n` is the mass `c`.

## Relation to the literature

Rallis inner product formula by doubling. Here the unramified integrals are left as a convergent
sum over cosets. For its sources see `Lib.SiegelWeil.RallisInner.Doubling`.

Non-vanishing of theta lifts in large rank. Here it is proved for unitary groups with target rank
more than twice the source rank, for finite data sharp at a level and without L-functions. If the
lift vanishes, the real matrix coefficient of the datum convolves the form to zero. Source:
S. Rallis, Injectivity properties of liftings associated to Weil representations, Compositio 52
(1984); J.-S. Li, Non-vanishing theorems for the cohomology of certain arithmetic quotients,
Crelle 428 (1992).

Critical Hecke L-values of CM fields as squared norms of theta lifts from U(1). Here the values are
taken at integers k at least 2, and the trivial character of U(1) is lifted to a definite U(2k),
with the tame Hecke character entering through the splitting. The squared norm is an explicit
constant times the L-value, and the lift is integral. Galois conjugates of the lift belong to
conjugate characters. This file contains only the local sum and the Euler product; the norm formula
is `New.LValueData.inner_trivialLift_self_eq_L`. Source: G. Shimura, On some arithmetic properties
of modular forms of one and several variables, Ann. of Math. 102 (1975); method: T. Yang, Theta
liftings and Hecke L-functions, J. reine angew. Math. 485 (1997); Harris, Li, Skinner, The Rallis
inner product formula and p-adic L-functions (2005); Finis, Ann. of Math. 163 (2006).
-/

@[expose] public section

noncomputable section

/-!
## Rallis' inner product formula for sharp data, and injectivity

Rallis' inner product formula for the theta lift `New.Space.lift` from `U(S)` to `U(T)` in the range
`rk T > 2 rk S`, for data `φ = v ⊗ F` (`New.Space.integrated`) with `v` in the Fock space and `F` a
sharp finite datum (`New.SiegelWeil.IsSharp`): a vacuum off a set `S₀` of places, whose matrix
coefficient at the points integral off `S₀` is supported on `J ∩ stdLevel E n` and constant there,
of mass `c`.

The proofs start from the doubling formula `New.SiegelWeil.inner_product_formula`, an integral over
`U(S)(𝔸)`.
-/

namespace New.SiegelWeil

open MeasureTheory Fock Space Fintype Set

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] {s : n → ℤˣ} {t : m → ℤˣ} {S : Space E n s} {a b : AutChar E}
  {S₀ : Set (FinPlace E)} {J : Subgroup (Gf E n)} {c : ℂ} {T : Space E m t} {F : 𝒮 (S.hom T)}
  {γ' : NumberField.InfinitePlace E → ℤ} {ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ}
  {y : G E s → ℂ}

/-- If the finite datum `F` is sharp for the group `J`, then `J` is open. -/
lemma IsSharp.isOpen_level (hF : IsSharp b S₀ F J c) : IsOpen (J : Set (Gf E n)) := by
  -- The matrix coefficient of `F` is continuous, nonzero at `1` and zero on `stdLevel E n` outside
  -- `J`.
  let U : Set (Gf E n) := (stdLevel E n : Set (Gf E n)) ∩ {g | weilMatrixCoeff b F F (1, g) ≠ 0}
  have h_open : IsOpen U := isOpen_stdLevel.inter isOpen_ne.preimage_of_continuous
  have h_one : 1 ∈ U := by simp [U, weilMatrixCoeff, hF.self_ne_zero, Prod.mk_one_one]
  have h_sub : U ⊆ J := fun g ⟨g_int, h_ne⟩ ↦ by_contra fun h_not ↦ h_ne <|
    (hF.weilMatrixCoeff_eq g (stdLevel_le_localLevel g_int)).trans
      (ite_eq_right (mt And.left h_not))
  exact J.isOpen_of_mem_nhds (mem_nhds_iff.2 ⟨U, h_sub, h_open, h_one⟩)

lemma IsSharp.mass_ne_zero (hF : IsSharp b S₀ F J c) : c ≠ 0 := by
  simp [← hF.mass_eq, hF.self_ne_zero, isCompact_stdLevel.relIndex_ne_zero hF.isOpen_level]

open scoped Classical in
/-- For `F` sharp for `J`, of mass `c`, the function equal to `⟨F, F⟩` on `J ⊓ stdLevel E n` and to
zero elsewhere has integral `c` over the finite points, for the Haar measure that gives
`stdLevel E n` volume `1`. -/
lemma IsSharp.integral_ite_eq_mass (hF : IsSharp b S₀ F J c) :
    ∫ g : Gf E n, (if g ∈ J ⊓ stdLevel E n then dataInner (S.hom T) F F else 0) = c := by
  -- As `stdLevel E n` has volume `1`, the volume of `J ⊓ stdLevel E n` is the inverse of its index.
  trans ∫ g, (J ∩ stdLevel E n : Set (Gf E n)).indicator (fun _ ↦ dataInner (S.hom T) F F) g
  · simp [Set.indicator]
  rw [integral_indicator_const _ (hF.isOpen_level.inter isOpen_stdLevel).measurableSet,
    ← hF.mass_eq]
  simp [measure_inter_eq_inv_relIndex isCompact_stdLevel hF.isOpen_level, Measure.real, field]

/-- Let `F` be a finite datum, `v` a vector of the Fock space and `φ = v ⊗ F`. The matrix
coefficient of `φ` at the point `(x, g)` is the real coefficient `⟨v, Ω(x) v⟩` times the finite
coefficient `⟨F, ω(g) F⟩`. Here `Ω(x) = realPairWeil γ γ' (x, 1)`, with `γ'` the weight of `b` and
any `γ`. -/
lemma weilMatrixCoeff_integrated [b.HasWeight γ' ψ] (hF : F ∈ finitePart (S.hom T))
    (γ : NumberField.InfinitePlace E → ℤ) (v : PairFock E s t) (x : GInf E s) (g : Gf E n) :
    weilMatrixCoeff b (integrated (S.hom T) v F) (integrated (S.hom T) v F) (x, g) =
      fockInner v (realPairWeil γ γ' (x, 1) v) * weilMatrixCoeff b F F (1, g) := by
  rw [weilMatrixCoeff, pairWeil_integrated_all, dataInner_integrated, ← pairWeil_integrated_fin]
  simp [hF, realPairWeil, Prod.mk_one_one]

open scoped Classical in
/-- The coefficient of a sharp datum. Let `F` be sharp for `J` off `S₀`, `v` a vector of the Fock
space and `φ = v ⊗ F`. For a real point `x`, a finite point `u` supported on `S₀ᶜ` and its conjugate
and a finite point `g` integral off `S₀`, `⟨φ, ω(x u g) φ⟩` is the product of the real coefficient
`⟨v, Ω(x) v⟩`, the coefficient of the vacuum at `u`, and `⟨F, F⟩` times the indicator of
`J ⊓ stdLevel E n` at `g`. Here `Ω(x) = realPairWeil γ γ' (x, 1)`, with `γ'` the weight of `b` and
any `γ`. -/
theorem IsSharp.weilMatrixCoeff_integrated_mul (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ]
    (γ : NumberField.InfinitePlace E → ℤ) (v : PairFock E s t) (x : GInf E s) {u g : Gf E n}
    (hu : u ∈ Gf.supportedOn n S₀ᶜ) (hg : g ∈ localLevel n S₀ᶜ) :
    weilMatrixCoeff b (integrated (S.hom T) v F) (integrated (S.hom T) v F) (x, u * g) =
      fockInner v (realPairWeil γ γ' (x, 1) v) * vacuumCoeff (card m) b u *
        if g ∈ J ⊓ stdLevel E n then dataInner (S.hom T) F F else 0 := by
  rw [show ((x, u * g) : G E s) = (1, u) * (x, g) by simp,
    weilMatrixCoeff_mul b (hF.vacuum_off S₀ᶜ v disjoint_compl_right) hu hg,
    weilMatrixCoeff_integrated hF.mem_finitePart γ, hF.weilMatrixCoeff_eq g hg, mul_left_comm,
    mul_assoc]

/-- Let `b` have weight `γ'` and tame part `ψ`, and let `F` be sharp for `J` off `S₀` (see
`IsSharp`). Then `J` contains every point of `stdLevel E n`, the stabiliser in `G_f` of `Ô ^ n`,
whose component is 1 at every place outside `S₀ᶜ` and the conjugate places of `S₀ᶜ`. -/
lemma IsSharp.inf_supportedOn_le (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ] :
    stdLevel E n ⊓ Gf.supportedOn n S₀ᶜ ≤ J := by
  -- Compute the coefficient of `vac ⊗ F` at `k = k * 1 = 1 * k` in two ways.
  rintro k ⟨k_int, k_supp⟩
  by_contra h_not
  let φ : 𝒮 (S.hom T) := integrated (S.hom T) vacVector F
  have h_ne : weilMatrixCoeff b φ φ (1, k * 1) ≠ 0 := by
    rw [hF.weilMatrixCoeff_integrated_mul 0 vacVector 1 k_supp (one_mem _)]
    simp [Prod.mk_one_one, vacuumCoeff, finMultiplier_ne_zero, hF.self_ne_zero, Fock.realVac]
  have h_zero : weilMatrixCoeff b φ φ (1, 1 * k) = 0 := by
    rw [hF.weilMatrixCoeff_integrated_mul 0 vacVector 1 (one_mem _) (stdLevel_le_localLevel k_int)]
    simp [h_not]
  exact h_ne (by rw [mul_one, ← h_zero, one_mul])

/-- Let `b` have a weight and a tame part. If `F` is sharp, a vacuum off `S₀`, then `b ∘ det` is
trivial on the integral points supported on the places of `S₀ᶜ` and their conjugates. -/
lemma IsSharp.isUnramifiedOn (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ] :
    IsUnramifiedOn b n S₀ᶜ := by
  -- Compute the coefficient of `vac ⊗ F` at `k = k * 1 = 1 * k` in two ways.
  intro k hk
  let φ : 𝒮 (S.hom T) := integrated (S.hom T) vacVector F
  let realCoeff : ℂ := fockInner (vacVector : PairFock E s t) (realPairWeil 0 γ' (1, 1) vacVector)
  have h_left : weilMatrixCoeff b φ φ (1, k) =
      realCoeff * vacuumCoeff (card m) b k * dataInner (S.hom T) F F := by
    rw [← mul_one k, hF.weilMatrixCoeff_integrated_mul 0 vacVector 1 hk.2 (one_mem _),
      ite_eq_left (one_mem _), mul_one]
  have h_right : weilMatrixCoeff b φ φ (1, k) =
      realCoeff * vacuumCoeff (card m) b (1 : Gf E n) * dataInner (S.hom T) F F := by
    rw [← one_mul k, hF.weilMatrixCoeff_integrated_mul 0 vacVector 1 (one_mem _)
      (stdLevel_le_localLevel hk.1), ite_eq_left ⟨hF.inf_supportedOn_le hk, hk.1⟩]
  have h_real : realCoeff ≠ 0 := by simp [realCoeff, Prod.mk_one_one, Fock.realVac]
  have h_coeff : vacuumCoeff (card m) b k = vacuumCoeff (card m) b (1 : Gf E n) :=
    mul_left_cancel₀ h_real (mul_right_cancel₀ hF.self_ne_zero (h_left.symm.trans h_right))
  simpa [vacuumCoeff, finMultiplier_eq_one_of_mem hk.1, Prod.mk_one_one, ← Circle.coe_inj,
    finMultiplier_eq_one_of_mem (one_mem (stdLevel E n))] using h_coeff

/-- Let `F` be sharp for `J` off `S₀`, of mass `c`, let `v` be a vector of the Fock space,
`φ = v ⊗ F` and `x` a real point, and let `P` be a right `J`-invariant function on the finite
points. If `g ↦ ⟨φ, ω(x g) φ⟩ P(g)` is integrable, its integral is the sum, over the cosets `q` of
the points integral off `S₀`, of `c ⟨v, Ω(x) v⟩` times the coefficient of the vacuum and the value
of `P` at `cosetRep q`, the representative of `q` supported on `S₀ᶜ` and its conjugate. Here
`Ω(x) = realPairWeil γ γ' (x, 1)`, with `γ'` the weight of `b` and any `γ`. -/
lemma IsSharp.hasSum_integral_weilMatrixCoeff_mul (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ]
    (γ : NumberField.InfinitePlace E → ℤ) (v : PairFock E s t) (x : GInf E s) {P : Gf E n → ℂ}
    (hP : ∀ k ∈ J, ∀ g : Gf E n, P (g * k) = P g)
    (h_int : Integrable fun g : Gf E n ↦
      weilMatrixCoeff b (integrated (S.hom T) v F) (integrated (S.hom T) v F) (x, g) * P g) :
    HasSum (fun q : Gf E n ⧸ localLevel n S₀ᶜ ↦ c * (fockInner v (realPairWeil γ γ' (x, 1) v) *
        (vacuumCoeff (card m) b (cosetRep q).val * P (cosetRep q).val)))
      (∫ g : Gf E n,
        weilMatrixCoeff b (integrated (S.hom T) v F) (integrated (S.hom T) v F) (x, g) * P g) := by
  -- Cut the finite points into the cosets; on each, `weilMatrixCoeff_integrated_mul` gives the
  -- integrand, a multiple of the function whose integral is the mass.
  let φ : 𝒮 (S.hom T) := integrated (S.hom T) v F
  have h_meas : MeasurableSet (localLevel n S₀ᶜ : Set (Gf E n)) :=
    (isOpen_coe_localLevel S₀ᶜ).measurableSet
  have h_coset (u : Gf E n) (hu : u ∈ Gf.supportedOn n S₀ᶜ) :
      ∫ g in (localLevel n S₀ᶜ : Set (Gf E n)), weilMatrixCoeff b φ φ (x, u * g) * P (u * g) =
      c * (fockInner v (realPairWeil γ γ' (x, 1) v) * (vacuumCoeff (card m) b u * P u)) := by
    rw [← integral_indicator h_meas, ← hF.integral_ite_eq_mass, ← integral_mul_const]
    refine integral_congr_ae (.of_forall fun g ↦ ?_)
    by_cases h_level : g ∈ J ⊓ stdLevel E n
    · have hg : g ∈ localLevel n S₀ᶜ := stdLevel_le_localLevel h_level.2
      simp only [φ, Set.indicator_of_mem hg, hF.weilMatrixCoeff_integrated_mul γ v x hu hg,
        ite_eq_left h_level, hP g h_level.1]
      ring
    · simp +contextual only [φ, Set.indicator_apply_eq_zero, SetLike.mem_coe, ite_eq_right h_level,
        hF.weilMatrixCoeff_integrated_mul γ v x hu, mul_zero, zero_mul, implies_true]
  have : Countable (Gf E n ⧸ localLevel n S₀ᶜ) := countable_quotient_localLevel S₀ᶜ
  exact (hasSum_setIntegral_mul_of_existsUnique h_meas
    (r := fun q : Gf E n ⧸ localLevel n S₀ᶜ ↦ (cosetRep q).val)
    (fun g ↦ by simp [← QuotientGroup.eq, mk_cosetRep]) h_int).congr_fun
      fun q ↦ (h_coset _ (cosetRep q).property).symm

/-- Inner product formula. Let `2 * card n < card m`, let `F` be sharp for `J` off `S₀` with mass
`c` (see `IsSharp`), let `v` be a Fock-space vector, and let `Θ` be the lift by `v ⊗ F` for the
characters `a`, `b`. Let `y`, `y'` be rapidly decreasing automorphic functions with `y` fixed by
`J`. Let `z = rallisSeries (card m) b S₀ᶜ y` be the series `∑ mc(q) R(q) y` over the cosets `q` of
the finite points integral at `S₀ᶜ`, with `mc` the vacuum coefficient. Then `⟨Θ y', Θ y⟩` equals the
volume of `[U(T)]` times `c` times the absolutely convergent integral of `⟨v, Ω(x) v⟩ ⟨y', R(x) z⟩`
over the real points `x` of `U(S)`. Here `R` is right translation and
`Ω(x) = realPairWeil γ γ' (x, 1)`, with `γ'` the weight of `b` and `γ` arbitrary. -/
theorem IsSharp.petersson_lift_eq_integral {S₀ : Set (FinPlace E)} {F : 𝒮 (S.hom T)}
    {J : Subgroup (Gf E n)} {c : ℂ} (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ]
    (h_rank : 2 * card n < card m) (a : AutChar E) (γ : NumberField.InfinitePlace E → ℤ)
    (v : PairFock E s t) {y y' : G E s → ℂ} (hy : y ∈ S.rapidFunctions)
    (hy' : y' ∈ S.rapidFunctions) (hJ : HasLevel y J) :
    Integrable (fun x : GInf E s ↦ fockInner v (realPairWeil γ γ' (x, 1) v) *
      S.petersson y' fun g : G E s ↦ rallisSeries (card m) b S₀ᶜ y (g * (x, 1))) ∧
    T.petersson (lift (pairThetaKer S T a b) (integrated (S.hom T) v F) y')
        (lift (pairThetaKer S T a b) (integrated (S.hom T) v F) y) =
      T.quotMeasure.real Set.univ * c * ∫ x : GInf E s, fockInner v (realPairWeil γ γ' (x, 1) v) *
        S.petersson y' fun g : G E s ↦ rallisSeries (card m) b S₀ᶜ y (g * (x, 1)) := by
  -- `inner_product_formula` gives the product as an absolutely convergent adelic integral;
  -- integrate first over the finite points.
  let φ : 𝒮 (S.hom T) := integrated (S.hom T) v F
  let P (g : G E s) : ℂ := S.petersson y' fun g' ↦ y (g' * g)
  obtain ⟨h_int, h_adelic⟩ : Integrable (fun g : G E s ↦ weilMatrixCoeff b φ φ g * P g) volume ∧
      T.petersson (lift (pairThetaKer S T a b) φ y') (lift (pairThetaKer S T a b) φ y) =
        T.quotMeasure.real Set.univ * ∫ g, weilMatrixCoeff b φ φ g * P g :=
    inner_product_formula h_rank a b (hF.clean v) hy hy'
  obtain ⟨y_aut : S.IsAutomorphic y, y_rapid : S.IsRapid y⟩ := hy
  obtain ⟨y'_aut : S.IsAutomorphic y', y'_rapid : S.IsRapid y'⟩ := hy'
  have y_bdd : IsBoundedMeasurable y := .of_continuous y_rapid.bounded y_aut.continuous
  have y'_int : Integrable y' S.quotMeasure := y'_rapid.integrable y'_aut.continuous
  have h_level (x : GInf E s) (k : Gf E n) (hk : k ∈ J) (g : Gf E n) : P (x, g * k) = P (x, g) := by
    have h_split : ((x, g * k) : G E s) = (x, g) * (1, k) := by simp
    simp only [P, h_split, ← mul_assoc, hJ k hk]
  have h_finite : ∀ᵐ x : GInf E s, ∫ g : Gf E n, weilMatrixCoeff b φ φ (x, g) * P (x, g) =
      c * (fockInner v (realPairWeil γ γ' (x, 1) v) *
        S.petersson y' fun g ↦ rallisSeries (card m) b S₀ᶜ y (g * (x, 1))) := by
    filter_upwards [h_int.prod_right_ae] with x hx
    have h_series : HasSum (fun q : Gf E n ⧸ localLevel n S₀ᶜ ↦
        vacuumCoeff (card m) b (cosetRep q).val * P (x, (cosetRep q).val))
        (S.petersson y' fun g ↦ rallisSeries (card m) b S₀ᶜ y (g * (x, 1))) := by
      simpa [P, mul_assoc] using hasSum_petersson_rallisSeries h_rank b S₀ᶜ y_bdd y'_int (x, 1)
    exact (hF.hasSum_integral_weilMatrixCoeff_mul γ v x (h_level x) hx).unique
      ((h_series.mul_left _).mul_left c)
  refine ⟨(integrable_const_mul_iff hF.mass_ne_zero.isUnit _).1
    (h_int.integral_prod_left.congr h_finite), ?_⟩
  rw [h_adelic, Measure.volume_eq_prod, integral_prod _ h_int, integral_congr_ae h_finite,
    integral_const_mul, mul_assoc]

/-! ### Partial integrals and injectivity by the dual datum -/

/-- The integral of `Φ` over the points `g` of the adelic unitary group whose finite part is
integral at every place of `A`. -/
def partialIntegral (A : Set (FinPlace E)) (Φ : G E s → ℂ) : ℂ :=
  ∫ g in {g : G E s | g.2 ∈ localLevel n A}, Φ g

omit [WeilData E] in
open Filter Topology in
/-- For `Φ` integrable on the adelic unitary group, the integral of `Φ` over the points integral at
the places of `R` outside `B` tends, as the finite set `R` grows to all places, to the integral over
the points integral at every place outside `B`. -/
lemma tendsto_partialIntegral (B : Set (FinPlace E)) {Φ : G E s → ℂ} (hΦ : Integrable Φ) :
    Tendsto (fun R : Finset (FinPlace E) ↦ partialIntegral ((R : Set (FinPlace E)) \ B) Φ) atTop
      (𝓝 (partialIntegral Bᶜ Φ)) := by
  -- The sets of points integral at `R \ B` decrease as `R` grows, with intersection the set of
  -- points integral at every place outside `B`.
  let K (A : Set (FinPlace E)) : Set (G E s) := {g | g.2 ∈ localLevel n A}
  have h_meas (A : Set (FinPlace E)) : MeasurableSet (K A) :=
    ((isOpen_coe_localLevel A).preimage continuous_snd).measurableSet
  have h_anti : Antitone fun R : Finset (FinPlace E) ↦ K ((R : Set (FinPlace E)) \ B) :=
    fun R R' h_le g hg w hw ↦ hg w ⟨h_le hw.1, hw.2⟩
  have h_inter : (⋂ R : Finset (FinPlace E), K ((R : Set (FinPlace E)) \ B)) = K Bᶜ := by
    ext g
    simp only [K, Set.mem_iInter, Set.mem_ofPred_eq, mem_localLevel]
    exact ⟨fun h w hw ↦ h {w} w ⟨Finset.mem_singleton_self w, hw⟩, fun h R w hw ↦ h w hw.2⟩
  have h_lim := tendsto_setIntegral_of_antitone (μ := volume) (f := Φ)
    (fun R : Finset (FinPlace E) ↦ h_meas _) h_anti ⟨∅, hΦ.integrableOn⟩
  rwa [h_inter] at h_lim

/-- Let `F` be sharp for `J` off `S₀`, of mass `c`, let `v` be a vector of the Fock space and
`φ = v ⊗ F`, let `y` be fixed by `J`, `y'` any function and `u` a finite point. The integral of
`⟨φ, ω(g) φ⟩ ⟨y', R(u g) y⟩` over the points `g` integral off `S₀` is `c` times the real integral of
`⟨v, Ω(x) v⟩ ⟨y', R(x u) y⟩`. Here `R` is right translation and
`Ω(x) = realPairWeil γ γ' (x, 1)`. -/
lemma IsSharp.partialIntegral_eq (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ]
    (γ : NumberField.InfinitePlace E → ℤ) (v : PairFock E s t) (hJ : HasLevel y J)
    (y' : G E s → ℂ) (u : Gf E n) :
    partialIntegral S₀ᶜ (fun g ↦
        weilMatrixCoeff b (integrated (S.hom T) v F) (integrated (S.hom T) v F) g *
          S.petersson y' (rightRegular ℂ (G E s) ℂ ((u : G E s) * g) y)) =
      c * ∫ x : GInf E s, fockInner v (realPairWeil γ γ' (x, 1) v) *
        S.petersson y' (fun h ↦ y (h * (x, 1) * (u : G E s))) := by
  classical
  -- On the points integral off `S₀` the integrand is a product of a function of the real part and
  -- the function of the finite part whose integral is the mass `c`.
  let φ : 𝒮 (S.hom T) := integrated (S.hom T) v F
  let realPart (x : GInf E s) : ℂ := fockInner v (realPairWeil γ γ' (x, 1) v) *
    S.petersson y' (fun h ↦ y (h * (x, 1) * (u : G E s)))
  let finPart (k : Gf E n) : ℂ := if k ∈ J ⊓ stdLevel E n then dataInner (S.hom T) F F else 0
  have h_meas : MeasurableSet {g : G E s | g.2 ∈ localLevel n S₀ᶜ} :=
    ((isOpen_coe_localLevel S₀ᶜ).preimage continuous_snd).measurableSet
  have h_point (g : G E s) : {g : G E s | g.2 ∈ localLevel n S₀ᶜ}.indicator (fun g ↦
      weilMatrixCoeff b φ φ g * S.petersson y' (rightRegular ℂ (G E s) ℂ ((u : G E s) * g) y)) g =
      realPart g.1 * finPart g.2 := by
    obtain ⟨x, k⟩ := g
    by_cases hk : k ∈ localLevel n S₀ᶜ
    · rw [indicator_of_mem (show (x, k) ∈ {g : G E s | g.2 ∈ localLevel n S₀ᶜ} from hk),
        weilMatrixCoeff_integrated hF.mem_finitePart γ, hF.weilMatrixCoeff_eq k hk]
      by_cases hJk : k ∈ J ⊓ stdLevel E n
      · -- Right translation by `k ∈ J` does not change `y`.
        have h_translate : rightRegular ℂ (G E s) ℂ ((u : G E s) * (x, k)) y =
            fun h ↦ y (h * (x, 1) * (u : G E s)) := by
          funext h
          have h_split : h * ((u : G E s) * (x, k)) = h * (x, 1) * (u : G E s) * (1, k) := by
            simp [Prod.mul_def, mul_assoc]
          simp only [rightRegular_apply_apply, h_split, hJ k hJk.1]
        simp only [h_translate, realPart, finPart, hJk, ite_true]
        ring
      · simp only [finPart, ite_eq_right hJk, mul_zero, zero_mul]
    · have hJk : k ∉ J ⊓ stdLevel E n := fun h ↦ hk (stdLevel_le_localLevel h.2)
      rw [indicator_of_notMem (show (x, k) ∉ {g : G E s | g.2 ∈ localLevel n S₀ᶜ} from hk)]
      simp only [finPart, ite_eq_right hJk, mul_zero]
  rw [partialIntegral, ← integral_indicator h_meas, funext h_point, Measure.volume_eq_prod,
    integral_prod_mul, hF.integral_ite_eq_mass, mul_comm]

/-- Let `card m > 2 * card n`, `F` sharp for `J` off `S₀`, `y` rapidly decreasing, automorphic and
fixed by `J`, with zero theta lift by `v ⊗ F`. For every rapidly decreasing automorphic `y'`, the
integral over the real points `x` of `⟨v, Ω(x) v⟩ ⟨y', R(x) y⟩` is zero, where
`Ω(x) = realPairWeil γ γ' (x, 1)`. The proof pairs `v ⊗ F` with the dual datum
(`exists_dualDatum`) of a finite set of places `R \ S₀` in the inner product formula, and lets `R`
exhaust the places. -/
lemma integral_eq_zero_of_lift_eq_zero (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ]
    (v : PairFock E s t) (hJ : HasLevel y J) (hy : y ∈ S.rapidFunctions)
    (h_rank : 2 * card n < card m)
    (h_lift : lift (pairThetaKer S T a b) (integrated (S.hom T) v F) y = 0)
    (γ : NumberField.InfinitePlace E → ℤ) {y' : G E s → ℂ} (hy' : y' ∈ S.rapidFunctions) :
    ∫ x : GInf E s, fockInner v (realPairWeil γ γ' (x, 1) v) *
      S.petersson y' (fun h ↦ y (h * (x, 1))) = 0 := by
  classical
  -- By the inner product formula with the dual datum of `R \ S₀`, the integral over the points
  -- integral at `R \ S₀` vanishes for every finite `R`; let `R` exhaust the places.
  set φ : 𝒮 (S.hom T) := integrated (S.hom T) v F
  let Φ (g : G E s) : ℂ := weilMatrixCoeff b φ φ g * S.petersson y' (rightRegular ℂ (G E s) ℂ g y)
  have h_formula (f' : 𝒮 (S.hom T)) := inner_product_formula h_rank a b (hF.clean v) hy hy' f'
  obtain ⟨h_int, -⟩ := h_formula φ
  have h_zero (R : Finset (FinPlace E)) : partialIntegral ((R : Set (FinPlace E)) \ S₀) Φ = 0 := by
    obtain ⟨f', hf'⟩ : ∃ f' : 𝒮 (S.hom T), ∀ g : G E s, weilMatrixCoeff b φ f' g =
        if g.2 ∈ localLevel n ((R : Set (FinPlace E)) \ S₀) then weilMatrixCoeff b φ φ g else 0 :=
      exists_dualDatum b h_rank.le (hF.vacuum_off _ v disjoint_sdiff_right)
      R.finite_toSet.sdiff
    obtain ⟨-, h_eq⟩ := h_formula f'
    have h_vanish : ∫ g, weilMatrixCoeff b φ f' g * S.petersson y' (rightRegular ℂ (G E s) ℂ g y) =
        0 := by
      simpa [φ, h_lift, petersson, measureReal_univ_ne_zero] using h_eq.symm
    have h_meas : MeasurableSet {g : G E s | g.2 ∈ localLevel n ((R : Set (FinPlace E)) \ S₀)} :=
      ((isOpen_coe_localLevel _).preimage continuous_snd).measurableSet
    rw [partialIntegral, ← integral_indicator h_meas, ← h_vanish]
    refine integral_congr_ae (.of_forall fun g ↦ ?_)
    by_cases hg : g.2 ∈ localLevel n ((R : Set (FinPlace E)) \ S₀)
    · rw [indicator_of_mem (show g ∈ {g : G E s | g.2 ∈ localLevel n ((R : Set (FinPlace E)) \ S₀)}
        from hg)]
      simp only [Φ, hf' g, hg, ↓reduceIte]
    · rw [indicator_of_notMem
        (show g ∉ {g : G E s | g.2 ∈ localLevel n ((R : Set (FinPlace E)) \ S₀)} from hg)]
      simp only [hf' g, hg, ↓reduceIte, zero_mul]
  have h_lim : partialIntegral S₀ᶜ Φ = 0 :=
    tendsto_nhds_unique (tendsto_partialIntegral S₀ h_int) (by simp [h_zero])
  have h_sharp := hF.partialIntegral_eq γ v hJ y' 1
  simp only [Prod.mk_one_one, one_mul, mul_one] at h_sharp
  simpa [hF.mass_ne_zero] using h_sharp.symm.trans h_lim

/-- Let `card m > 2 * card n` and let `F` on `Hom(S, T)` be sharp for `J` off `S₀` with mass `c`
(see `IsSharp`). Let `y` be automorphic, rapidly decreasing and fixed by `J`, let `v` be a
Fock-space vector and let `a`, `b` be characters. If the theta lift of `y` by `v ⊗ F` for
`pairThetaKer S T a b` vanishes and `x ↦ ⟨v, Ω(x) v⟩` is integrable, then its convolution `realConv`
with `y` is zero. Here `Ω(x) = realPairWeil γ γ' (x, 1)`, with `γ'` the weight of `b`. -/
lemma realConv_eq_zero_of_lift_eq_zero (hF : IsSharp b S₀ F J c) [b.HasWeight γ' ψ]
    (v : PairFock E s t) (hJ : HasLevel y J) (hy : y ∈ S.rapidFunctions)
    (h_rank : 2 * card n < card m)
    (h_lift : lift (pairThetaKer S T a b) (integrated (S.hom T) v F) y = 0)
    (γ : NumberField.InfinitePlace E → ℤ)
    (h_int : Integrable fun x : GInf E s ↦ fockInner v (realPairWeil γ γ' (x, 1) v)) :
    realConv (fun x : GInf E s ↦ fockInner v (realPairWeil γ γ' (x, 1) v)) y = 0 := by
  -- The convolution `y₁` is automorphic and bounded; `⟨y₁, y₁⟩` is an average of products of `y₁`
  -- with real translates of `y`, each zero by `integral_eq_zero_of_lift_eq_zero`.
  set κ : GInf E s → ℂ := fun x ↦ fockInner v (realPairWeil γ γ' (x, 1) v)
  obtain ⟨y_aut, y_rapid⟩ : S.IsAutomorphic y ∧ S.IsRapid y := hy
  have y_bdd : IsBoundedMeasurable y := .of_continuous y_rapid.bounded y_aut.continuous
  obtain ⟨K, hK⟩ := y_aut.exists_level
  obtain ⟨y₁_aut, y₁_bdd⟩ : S.IsAutomorphic (realConv κ y) ∧ IsBoundedMeasurable (realConv κ y) :=
    isAutomorphic_realConv K y_bdd y_aut.rat_mul hK h_int
  have h_translate (x : GInf E s) : S.petersson (fun g ↦ y (g * (x, 1))) (realConv κ y) = 0 := by
    rw [petersson_realConv_right y_bdd h_int (y_bdd.comp (measurable_mul_const (x, 1)))]
    exact integral_eq_zero_of_lift_eq_zero hF v hJ ⟨y_aut, y_rapid⟩ h_rank h_lift γ
      ⟨y_aut.comp_mul_right _, y_rapid.comp_mul_right⟩
  refine y₁_aut.eq_zero_of_petersson_self (y₁_bdd.memLp_top.mono_exponent le_top) ?_
  rw [petersson_realConv_right y_bdd h_int y₁_bdd]
  simp [← conj_petersson (F' := realConv κ y), h_translate]

/-- Injectivity and norm of the lift, in Weil's range `2 * card n < card m`. Let the vector `v` of
the Fock space be an edge (a real datum that carries type `e` to type `e'`, such as the vector of
the joint harmonic of corresponding parameters) for the weights `γ`, `γ'`. There is `C ≠ 0`,
depending only on these real data and the spaces, with the following property. Let `a`, `b` be
characters of weights `γ`, `γ'`, let the finite datum `F` be sharp for `J`
off `S₀`, of mass `c` (see `IsSharp`), and let `L` be the lift by `v ⊗ F`. On the forms `y` of type
`e` fixed by `J` the lift is injective, and `⟨L y', L y⟩` is `C c` times the Petersson product of
`y'` with the series `rallisSeries` of `y` off `S₀`, for all forms `y'` of type `e`. -/
theorem exists_petersson_formLift_eq_rallisSeries {γ : NumberField.InfinitePlace E → ℤ}
    {v : PairFock E s t} {e : GInf E s → ℂ} {e' : GInf E t → ℂ}
    (h_edge : IsEdge (realPairWeil γ γ') e e' v) (h_rank : 2 * card n < card m) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ (a b : AutChar E) {ψ ψ' : ∀ w : FinPlace E, MulChar (ResField w) ℂ}
      {S₀ : Set (FinPlace E)} {J : Subgroup (Gf E n)} {F : 𝒮 (S.hom T)} {c : ℂ}
      [a.HasWeight γ ψ] [b.HasWeight γ' ψ'], IsSharp b S₀ F J c →
      ∀ y : S.Form e, HasLevel y J →
        let L : S.Form e →ₗ[ℂ] T.Form e' :=
          formLift (pairThetaKer S T a b) e e' ((S.hom T).integrated v F)
        (L y = 0 → y = 0) ∧
        ∀ y' : S.Form e,
          T.petersson (L y') (L y) = C * c * S.petersson y' (rallisSeries (card m) b S₀ᶜ y) := by
  -- The real integral `Z` of `⟨v, Ω(x) v⟩` against the coefficient of the type `e` is not zero for
  -- an edge.
  let Z : ℂ :=
    ∫ x : GInf E s, fockInner v (realPairWeil γ γ' (x, 1) v) * (starRingEnd ℂ (e x) / e 1)
  have hZ : Z ≠ 0 := h_edge.zetaIntegral_ne_zero
  refine ⟨T.quotMeasure.real univ * Z, by simp [hZ, measureReal_univ_ne_zero], ?_⟩
  intro a b ψ ψ' S₀ J F c _ _ hF y hJ
  -- Forms of type `e` are rapid, and on them `formLift` is the lift of functions.
  have h_arr : IsArrow (pairThetaKer S T a b) e e' ((S.hom T).integrated v F) :=
    (h_edge.isArrow a b hF.mem_finitePart).1
  simp only [h_arr.coe_formLift]
  -- On forms of type `e`, real translates scale the Petersson product by `conj (e x) / e 1`.
  have h_real (y' z : S.Form e) : ∫ x : GInf E s, fockInner v (realPairWeil γ γ' (x, 1) v) *
      S.petersson y' (fun g : G E s ↦ z.val (g * (x, 1))) = Z * S.petersson y' z := by
    simp [y'.property.petersson_real_translate h_edge.isCuspKernel_source z.property, ← mul_assoc,
      Z, integral_mul_const]
  -- The series `z` of `y` is a form of type `e`, so the real integral of the inner product formula
  -- is `h_real` for `z`.
  have y_level : HasLevel y (stdLevel E n ⊓ Gf.supportedOn n S₀ᶜ) :=
    fun k hk ↦ hJ k (hF.inf_supportedOn_le hk)
  obtain ⟨z : S.Form e, -, hz : ⇑z = rallisSeries (card m) b S₀ᶜ y⟩ :=
    exists_form_eq_rallisSeries h_rank hF.isUnramifiedOn le_rfl
      (inf_le_left.trans stdLevel_le_localLevel) y_level
  rw [← hz]
  set Θ : (G E s → ℂ) → G E t → ℂ := lift (pairThetaKer S T a b) ((S.hom T).integrated v F)
  have h_norm (y' : S.Form e) :
      T.petersson (Θ y') (Θ y) = T.quotMeasure.real univ * Z * c * S.petersson y' z := by
    obtain ⟨y_rapid, -⟩ := h_arr y
    obtain ⟨y'_rapid, -⟩ := h_arr y'
    obtain ⟨-, h_integral⟩ := hF.petersson_lift_eq_integral h_rank a γ v y_rapid y'_rapid hJ
    rw [h_integral, ← hz, h_real y' z]
    ring
  refine ⟨fun h_zero ↦ ?_, h_norm⟩
  -- If the lift vanishes, the real integral of `⟨y, R(x) y⟩` is zero, and it is `Z ⟨y, y⟩`.
  have h_lift : Θ y = 0 := (h_arr.coe_formLift y).symm.trans (congrArg Subtype.val h_zero)
  obtain ⟨y_rapid, -⟩ := h_arr y
  have h_self : Z * S.petersson y y = 0 := by
    rw [← h_real y y]
    exact integral_eq_zero_of_lift_eq_zero hF v hJ y_rapid h_rank h_lift γ y_rapid
  exact Subtype.ext (y.property.eq_zero_of_petersson_self y.property.memLp
    ((mul_eq_zero.1 h_self).resolve_left hZ))

/-- Rallis' inner product formula with the series written out as a sum over cosets. Let
`2 * card n < card m` and let `v` be an edge from type `e` to type `e'` for the weights `γ`, `γ'`.
There is `A ≠ 0`, depending only on the spaces `S`, `T` and the real data, with the following
property. Let `a`, `b` be characters of weights `γ`, `γ'`, let the finite datum `F` be sharp for `J`
off `S₀`, of mass `c`, and let `L` be the lift by `v ⊗ F`. Then `L` is injective on the forms of
type `e` fixed by `J`, and for such a form `y` and any form `y'` of type `e`, `⟨L y', L y⟩` is the
absolutely convergent sum of `A * c` times `cosetTerm` (the vacuum coefficient at `q` times
`⟨y', R(q) y⟩`) over the cosets `q` of the points integral off `S₀`. -/
lemma rallis_inner_product_cosetTerm {γ : NumberField.InfinitePlace E → ℤ} {v : PairFock E s t}
    {e : GInf E s → ℂ} {e' : GInf E t → ℂ} (h_edge : IsEdge (realPairWeil γ γ') e e' v)
    (h_rank : 2 * card n < card m) :
    ∃ A : ℂ, A ≠ 0 ∧ ∀ (a b : AutChar E) {ψ ψ' : ∀ w : FinPlace E, MulChar (ResField w) ℂ}
      {S₀ : Set (FinPlace E)} {J : Subgroup (Gf E n)} {F : 𝒮 (S.hom T)} {c : ℂ}
      [a.HasWeight γ ψ] [b.HasWeight γ' ψ'], IsSharp b S₀ F J c →
      ∀ y : S.Form e, HasLevel y J →
        let L : S.Form e →ₗ[ℂ] T.Form e' :=
          formLift (pairThetaKer S T a b) e e' ((S.hom T).integrated v F)
        (L y = 0 → y = 0) ∧
        ∀ y' : S.Form e,
          HasSum (fun q : Gf E n ⧸ localLevel n S₀ᶜ ↦ A * c * cosetTerm (card m) b S₀ᶜ y' y q)
            (T.petersson (L y') (L y)) := by
  obtain ⟨C, hC, h_rallis⟩ :=
    exists_petersson_formLift_eq_rallisSeries (S := S) (T := T) h_edge h_rank
  refine ⟨C, hC, ?_⟩
  intro a b ψ ψ' S₀ J F c _ _ hF y hJ L
  obtain ⟨h_inj, h_norm⟩ : (L y = 0 → y = 0) ∧ ∀ y' : S.Form e,
      T.petersson (L y') (L y) = C * c * S.petersson y' (rallisSeries (card m) b S₀ᶜ y) :=
    h_rallis a b hF y hJ
  refine ⟨h_inj, fun y' ↦ ?_⟩
  -- Expand the pairing with the series term by term.
  have h_series : HasSum (fun q : Gf E n ⧸ localLevel n S₀ᶜ ↦
      vacuumCoeff (card m) b (cosetRep q).val *
        S.petersson y' fun g : G E s ↦ y (g * (1, (cosetRep q).val)))
      (S.petersson y' (rallisSeries (card m) b S₀ᶜ y)) := by
    simpa only [mul_one] using hasSum_petersson_rallisSeries h_rank b S₀ᶜ
      y.property.isBoundedMeasurable (y'.property.memLp.integrable one_le_two) 1
  rw [h_norm y']
  exact h_series.mul_left (C * c)

end New.SiegelWeil

/-!
## Sharp data modulo 𝔪 and the vacuum sum in rank one

A modulus 𝔪 (`New.Modulus`) is a nonzero ideal of O_E prime to its conjugate; `𝔪.ResidueRing` is
O_E/𝔪 and `𝔪.places` the set of places dividing 𝔪.
-/

namespace New

open HeckeChar Gf Matrix Fintype Valued Rows Space Modulus SiegelWeil WeilData Finset NumberField
variable {E n m : Type} [Field E] [CMType E] {𝔪 : Modulus E} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] {s : n → ℤˣ} {t : m → ℤˣ} [WeilData E] {w : FinPlace E}
  {ν : AutChar E}

/-- A function `Ψ ≠ 0` on matrices modulo `𝔪` is sharp for a group `J` with `J(𝔪) ≤ J` if `J`
fixes `Ψ ⊗ vac` and, for a fixed matrix `A`, the matrix `A x` lies in the image of `J` whenever
`Ψ x ≠ 0`. Here `K₀ = stdLevel E n` is the group of integral points, `J(𝔪)` consists of those that
are `1` modulo `𝔪`, and `Ψ ⊗ vac = vacuumDatum S T 𝔪 Ψ`. -/
structure SiegelWeil.IsSharpFn (S : Space E n s) (T : Space E m t) (b : AutChar E) (𝔪 : Modulus E)
    (J : Subgroup (Gf E n)) (Ψ : Matrix m n 𝔪.ResidueRing → ℂ) : Prop where
  /-- The principal level of `𝔪` lies in `J`. -/
  principal_le : 𝔪.levelOfSubgroup ⊥ ≤ J
  /-- The function is not zero. -/
  ne_zero : Ψ ≠ 0
  /-- The group `J` fixes the datum `Ψ ⊗ vac`. -/
  fixes : ∀ k ∈ J, pairWeil S T 1 b ((1, k), 1) (vacuumDatum S T 𝔪 Ψ).1 = (vacuumDatum S T 𝔪 Ψ).1
  /-- On the support of `Ψ` the matrix `A x` is the reduction of a point of `J`. -/
  exists_mul_eq : ∃ A : Matrix n m 𝔪.ResidueRing,
    ∀ x : Matrix m n 𝔪.ResidueRing,
      Ψ x ≠ 0 → ∃ k : stdLevel E n, k.val ∈ J ∧ (𝔪.reductionGL k).val = A * x

section IsSharpFn

variable {S : Space E n s} {T : Space E m t} {b : AutChar E} {J : Subgroup (Gf E n)}
  {Ψ : Matrix m n 𝔪.ResidueRing → ℂ}

/-- If `Ψ` is sharp for `J`, then at a place of `𝔪` every matrix in the support of the lift of `Ψ`
to finite adelic vectors is primitive: integral with an integral left inverse. -/
lemma SiegelWeil.IsSharpFn.isPrimitiveMatrix (hΨ : IsSharpFn S T b 𝔪 J Ψ) {w : FinPlace E}
    (hw : w ∈ 𝔪.places) {x : m × n → 𝔸f E} (hx : 𝔪.liftFn (Ψ ∘ vecToMatrix) x ≠ 0) :
    IsPrimitiveMatrix (LocInt w).toSubring ((vecToMatrix x).map (evalAt w)) := by
  obtain ⟨A, hA⟩ := hΨ.exists_mul_eq
  refine isPrimitiveMatrix_of_liftFn_ne_zero (of Prod.mk) (fun y hy ↦ ?_) hw hx
  -- The matrix `A y` is invertible, so `y` has a left inverse modulo `𝔪`.
  obtain ⟨k, -, hk⟩ := hA (vecToMatrix y) hy
  have h_inv : (𝔪.reductionGL k)⁻¹.val * A * vecToMatrix y = (1 : Matrix n n 𝔪.ResidueRing) := by
    rw [Matrix.mul_assoc, ← hk, Units.inv_mul]
  exact ⟨_, h_inv⟩

/-- Let `Ψ` be sharp for `J` and let the integral point `g` lie outside `J`. Then `x` and `x ḡ`,
where `ḡ` is `g` modulo `𝔪`, are not both in the support of `Ψ`. -/
lemma SiegelWeil.IsSharpFn.eq_zero_or_eq_zero (hΨ : IsSharpFn S T b 𝔪 J Ψ) {g : stdLevel E n}
    (hg : g.val ∉ J) (x : Matrix m n 𝔪.ResidueRing) :
    Ψ x = 0 ∨ Ψ (x * (𝔪.reductionGL g).val) = 0 := by
  -- Otherwise `g` would be congruent to `(A x)⁻¹ (A x g)`, a quotient of points of `J`.
  obtain ⟨A, hA⟩ := hΨ.exists_mul_eq
  by_contra! ⟨hx, hxg⟩
  obtain ⟨k₁, hk₁_mem, hk₁⟩ := hA _ hx
  obtain ⟨k₂, hk₂_mem, hk₂⟩ := hA _ hxg
  have red_eq : 𝔪.reductionGL (k₂⁻¹ * (k₁ * g)) = 1 := by
    simp [inv_mul_eq_one, Units.ext_iff, hk₁, hk₂, Matrix.mul_assoc]
  have h_mem : k₂.val⁻¹ * (k₁.val * g.val) ∈ J := hΨ.principal_le ⟨_, red_eq, rfl⟩
  exact hg (by simpa [mul_mem_cancel_left, hk₁_mem, hk₂_mem] using h_mem)

/-- An integral finite point `k` of `U(S)` sends the datum `Ψ ⊗ vac` to `b(det k)⁻¹` times the datum
of `x ↦ Ψ (x k̄)`, where `k̄` is `k` modulo `𝔪`. -/
lemma SiegelWeil.pairWeil_stdLevel_vacuumDatum (S : Space E n s) (T : Space E m t) (b : AutChar E)
    (k : stdLevel E n) (Ψ : Matrix m n 𝔪.ResidueRing → ℂ) :
    pairWeil S T 1 b ((1, k.val), 1) (vacuumDatum S T 𝔪 Ψ).val = ((b.val (detFin s k.val))⁻¹ : ℂ) •
      (vacuumDatum S T 𝔪 fun x : Matrix m n 𝔪.ResidueRing ↦ Ψ (x * (𝔪.reductionGL k).val)).val := by
  simpa [vacuumDatum, Prod.mk_one_one] using pairWeil_modDatum_stdLevel S T 1 b 𝔪 k 1 Ψ
    Fock.vacVector

/-- Let `Ψ` be sharp for `J` and let the integral point `g` lie outside `J`. Then the matrix
coefficient at `g` of the datum `Ψ ⊗ vac` is zero. -/
lemma SiegelWeil.IsSharpFn.weilMatrixCoeff_eq_zero_of_mem_stdLevel_of_notMem
    (hΨ : IsSharpFn S T b 𝔪 J Ψ) (g : stdLevel E n) (hg : g.val ∉ J) :
    weilMatrixCoeff b (vacuumDatum S T 𝔪 Ψ).val (vacuumDatum S T 𝔪 Ψ).val (1, g.val) = 0 := by
  -- The point `g` acts on `Ψ` through its reduction, up to a scalar.
  have h_sum : star (Ψ ∘ vecToMatrix) ⬝ᵥ (fun x ↦ Ψ (x * (𝔪.reductionGL g).val)) ∘ vecToMatrix =
    0 :=
    sum_eq_zero fun x _ ↦ by simpa using hΨ.eq_zero_or_eq_zero hg (vecToMatrix x)
  rw [weilMatrixCoeff, pairWeil_stdLevel_vacuumDatum]
  simp [vacuumDatum, h_sum, ↓ isConjDisjoint_places, ↓ dataInner_schrodingerOp, ↓ localInner_liftFn]

/-- Let `Ψ` be sharp for `J` and let the finite point `g` be integral off `𝔪 𝔪̄` but not everywhere.
Then the matrix coefficient at `g` of the datum `Ψ ⊗ vac` is zero. -/
lemma SiegelWeil.IsSharpFn.weilMatrixCoeff_eq_zero_of_notMem_stdLevel (hΨ : IsSharpFn S T b 𝔪 J Ψ)
    {g : Gf E n} (g_off : g ∈ localLevel n 𝔪.places.conjClosureᶜ) (hg : g ∉ stdLevel E n) :
    weilMatrixCoeff b (vacuumDatum S T 𝔪 Ψ).val (vacuumDatum S T 𝔪 Ψ).val (1, g) = 0 := by
  -- If `x` and `x g` were both primitive at the places of `𝔪`, `g` would be integral there, hence
  -- everywhere.
  have h_supp (x : m × n → 𝔸f E) : 𝔪.liftFn (Ψ ∘ vecToMatrix) x = 0 ∨
      𝔪.liftFn (Ψ ∘ vecToMatrix) (matrixToVec (vecToMatrix x * g.val.val)) = 0 := by
    by_contra! ⟨hx, hxg⟩
    have h_integral (w : FinPlace E) (hw : w ∈ 𝔪.places) : g.atPlace w ∈ localIntGL n w := by
      have h_prod : IsPrimitiveMatrix (LocInt w).toSubring
          ((vecToMatrix x).map (evalAt w) * (g.atPlace w).val) := by
        simpa [Matrix.map_mul] using! hΨ.isPrimitiveMatrix hw hxg
      exact (isPrimitiveMatrix_iff_mem_intGL _).1 ((hΨ.isPrimitiveMatrix hw hx).mul_iff.1 h_prod)
    -- Integrality passes from a place to its conjugate by unitarity.
    grind [mem_stdLevel_iff, atPlace_star_mem_iff, mem_localLevel]
  -- The point `g` translates `Ψ` (`omega_schrodingerOp`), so the matrix coefficient is a multiple
  -- of the integral of `conj (Ψ x) * Ψ (x g)`, whose integrand vanishes.
  let p : G E (homSigns s t) := G.onHom ((1, g), 1)
  have h_local : localInner 𝔪.places (𝔪.liftFn (Ψ ∘ vecToMatrix))
      (fun x ↦ 𝔪.liftFn (Ψ ∘ vecToMatrix) (p.2⁻¹.val.val *ᵥ x)) = 0 :=
    MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x _ ↦ by simpa [p] using h_supp x
  rw [vacuumDatum, weilMatrixCoeff, pairWeil_apply,
    (omega_schrodingerOp 𝔪.isConjDisjoint_places _ p _).2,
    map_smul, dataInner_schrodingerOp 𝔪.isConjDisjoint_places, h_local, zero_mul, smul_zero]

/-- The coefficient of a sharp datum. Let the signs of `S` agree or `𝔪 ≠ (1)`, and let `Ψ` be sharp
for `J` relative to `b` (`IsSharpFn`): `Ψ ≠ 0` is a function on `m × n` matrices modulo `𝔪`,
`J(𝔪) ≤ J`, `J` fixes `Ψ ⊗ vac`, and for a fixed matrix `A` the matrix `A x` lies in the image
of `J` whenever `Ψ x ≠ 0`. Write `K₀ = stdLevel E n`. Then `Ψ ⊗ vac` (`vacuumDatum`) satisfies
`IsSharp` for `J` off the places of `𝔪 𝔪̄`: its matrix coefficient at the finite points integral off
`𝔪 𝔪̄` is the mean of `|Ψ|²` times the indicator of `J`, and its mass is this mean divided by the
index `[K₀ : J ∩ K₀]`. -/
lemma SiegelWeil.IsSharpFn.isSharp (hΨ : IsSharpFn S T b 𝔪 J Ψ)
    (hn : (∀ i j : n, s i = s j) ∨ Nonempty 𝔪.places) :
    IsSharp b 𝔪.places.conjClosure (vacuumDatum S T 𝔪 Ψ).val J
      (star Ψ ⬝ᵥ Ψ / card (m × n → 𝔪.ResidueRing) / stdLevelIndex J) := by
  -- On `J` the datum is fixed. If the coefficient at `g` is not zero, some `x` and `x g` lie in the
  -- support of `Ψ`; this makes `g` integral and then puts it in `J` (the two lemmas above). The
  -- hypothesis `hn` serves only for cleanness.
  -- Sums over matrices are sums over vectors indexed by `m × n`.
  have h_curry : star (Ψ ∘ vecToMatrix) ⬝ᵥ (Ψ ∘ vecToMatrix) = star Ψ ⬝ᵥ Ψ :=
    comp_equiv_dotProduct_comp_equiv (star Ψ) Ψ (Equiv.curry m n 𝔪.ResidueRing)
  have h_norm : dataInner (S.hom T) (vacuumDatum S T 𝔪 Ψ).val (vacuumDatum S T 𝔪 Ψ).val =
      star Ψ ⬝ᵥ Ψ / card (m × n → 𝔪.ResidueRing) := by
    simp [vacuumDatum, ← h_curry, ↓ isConjDisjoint_places, ↓ dataInner_schrodingerOp,
      ↓ localInner_liftFn]
  refine ⟨?_, (vacuumDatum S T 𝔪 Ψ).property, fun B v hB ↦ ?_, fun g g_off ↦ ?_, by rw [h_norm],
    fun v ↦ hn.imp_right fun ⟨w⟩ ↦ ?_⟩
  · open scoped ComplexOrder in simp [h_norm, dotProduct_star_self_eq_zero, hΨ.ne_zero]
  · -- a vacuum off `𝔪 𝔪̄`
    simp [vacuumDatum, projOn_schrodingerOp_vacElem, hB]
  · -- the coefficient at a point `g` integral off `𝔪 𝔪̄`
    split_ifs with g_lvl
    · exact congrArg _ (hΨ.fixes g g_lvl.1)
    by_cases g_int : g ∈ stdLevel E n
    · exact hΨ.weilMatrixCoeff_eq_zero_of_mem_stdLevel_of_notMem ⟨g, g_int⟩ fun h_mem ↦
        g_lvl ⟨h_mem, g_int⟩
    · exact hΨ.weilMatrixCoeff_eq_zero_of_notMem_stdLevel g_off g_int
  · -- cleanness: if `𝔪` has a place `w`, primitive matrices have a left inverse there
    refine ⟨𝔪.places, 𝔪.liftFn (Ψ ∘ vecToMatrix), w.val, _, 𝔪.isConjDisjoint_places,
      inferInstance, fun y hy ↦ ?_, integrated_schrodingerOp ..⟩
    exact (hΨ.isPrimitiveMatrix w.property hy).2.imp fun L h ↦ h.2

end IsSharpFn

/-- Let `b` have weight `γ` and tame part `ψ` trivial at every finite place not dividing `𝔪`. Let
`F ≠ 0` be a function on `m × n` matrices modulo `𝔪` with `A * x = 1` whenever `F x ≠ 0`. Then `F`
is sharp (`IsSharpFn`) for the principal level `J(𝔪) = 𝔪.levelOfSubgroup ⊥`, the points of
`stdLevel E n` that are `1` modulo `𝔪`: `J(𝔪)` fixes `F ⊗ vac`, and `A x` lies in the trivial image
of `J(𝔪)` modulo `𝔪` whenever `F x ≠ 0`. Examples are the point datum, which is the indicator of the
matrix with blocks `1` and `0`, and the constant `1` for `𝔪 = (1)`. -/
lemma SiegelWeil.isSharpFn_of_mul_eq_one (S : Space E n s) (T : Space E m t) (b : AutChar E)
    {γ : InfinitePlace E → ℤ} {ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ} [hb : b.HasWeight γ ψ]
    (hψ : ∀ w : FinPlace E, w ∉ 𝔪.places → ψ w = 1) {F : Matrix m n 𝔪.ResidueRing → ℂ}
    (hF_ne : F ≠ 0) (A : Matrix n m 𝔪.ResidueRing)
    (hA : ∀ x : Matrix m n 𝔪.ResidueRing, F x ≠ 0 → A * x = 1) :
    IsSharpFn S T b 𝔪 (𝔪.levelOfSubgroup ⊥) F := by
  refine
    { principal_le := le_rfl
      ne_zero := hF_ne
      fixes := ?_
      exists_mul_eq := ⟨A, fun x hx ↦ ⟨1, one_mem _, by simp [hA x hx]⟩⟩ }
  rintro _ ⟨k, hk, rfl⟩
  -- An element `k ≡ 1` modulo `𝔪` acts by the scalar `b (det k)⁻¹ = 1`.
  have h_red : 𝔪.reductionGL k = 1 := by simpa using hk
  change pairWeil S T 1 b ((1, k.val), 1) (vacuumDatum S T 𝔪 F).val = (vacuumDatum S T 𝔪 F).val
  simp [pairWeil_stdLevel_vacuumDatum, h_red, hb.apply_det_eq_charOfTamePart hψ k]

/-- The case of the principal level. Let the signs of `S` agree or `𝔪 ≠ (1)`, let `b` have trivial
tame part off `𝔪`, and let `F ≠ 0` be supported in `{x | A x = 1}`. Then the datum
`vacuumDatum S T 𝔪 F`, which is `F` at `𝔪` and the vacuum elsewhere, satisfies `IsSharp` for
`J(𝔪)` off the places of `𝔪 𝔪̄`. Its mass is the mean of `|F|²` divided by the order of
`GL_n(𝓞/𝔪)`. -/
lemma SiegelWeil.isSharp_vacuumDatum_of_mul_eq_one {S : Space E n s} (T : Space E m t)
    (b : AutChar E) (hn : (∀ i j : n, s i = s j) ∨ Nonempty 𝔪.places) (A : Matrix n m 𝔪.ResidueRing)
    {F : Matrix m n 𝔪.ResidueRing → ℂ} (hA : ∀ x : Matrix m n 𝔪.ResidueRing, F x ≠ 0 → A * x = 1)
    {γ : InfinitePlace E → ℤ} {ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ} [hb : b.HasWeight γ ψ]
    (hψ : ∀ w : FinPlace E, w ∉ 𝔪.places → ψ w = 1) (h_norm : star F ⬝ᵥ F ≠ 0) :
    IsSharp b 𝔪.places.conjClosure (vacuumDatum S T 𝔪 F).val (𝔪.levelOfSubgroup ⊥)
      (star F ⬝ᵥ F / card (m × n → 𝔪.ResidueRing) / card (GL n 𝔪.ResidueRing)) := by
  simpa [stdLevelIndex_levelOfSubgroup] using
    (isSharpFn_of_mul_eq_one S T b hψ (fun h ↦ h_norm (by simp [h])) A hA).isSharp hn

/-! ### The value of the vacuum coefficient -/

/-! ### The vacuum sum in rank one -/

open scoped Classical in
/-- The sign −1 if w precedes w̄ in a fixed well-ordering, else 1: so 1 if w = w̄, and one of
each sign on a split pair. The product over the places w above a place of norm q of the real
subfield F of the factors 1 − ε_w q_w^(−k) is 1 − q^(−2k) if this place is split or inert, an
inverse Euler factor of ζ_F(2k). -/
noncomputable def placeSign (w : FinPlace E) : ℂ := if WellOrderingRel w (star w) then -1 else 1

omit [WeilData E] in
lemma norm_placeSign_le (w : FinPlace E) : ‖placeSign w‖ ≤ 1 := by
  simp [placeSign, apply_ite]

omit [WeilData E] in
/-- At a place `w` that differs from its conjugate `w̄`, the signs `placeSign` of `w` and `w̄`
are opposite, so `(1 - ε_w̄ x) (1 - ε_w x) = 1 - x ^ 2`. -/
lemma placeSign_factor_mul (hw : w.IsSplit) (x : ℂ) :
    (1 - placeSign (star w) * x) * (1 - placeSign w * x) = 1 - x ^ 2 := by
  -- Exactly one of `w`, `star w` precedes the other, so the two coefficients are `1` and `-1`.
  have h_one : WellOrderingRel (star w) w ↔ ¬WellOrderingRel w (star w) :=
    ⟨asymm, fun h ↦ ((trichotomous_of _ w (star w)).resolve_left h).resolve_left (Ne.symm hw)⟩
  grind [placeSign, star_star]

/-- The value of the multiplier `glMultiplier` of the Weil representation at `singleGL w (ϖ_w ^ z)`,
the adelic point that is the power `z` of the uniformiser at `w` and `1` elsewhere: it is
`(υ(ϖ_w) √q_w) ^ (-z)` for `z ≤ 0` and `1` for `z ≥ 0`. -/
lemma glMultiplier_singleGL_uniformizer_zpow (z : ℤ) :
    glMultiplier (singleGL w (diagGL fun _ : Unit ↦ uniformizer w ^ z)) =
      (υ.atUniformizer w * √w.q) ^ (-z).toNat := by
  -- Apply `glMultiplier_eq_pow_of_local` with the denominator `y`: both `y` and
  -- `uniformizer w ^ z * y` are integral, and one of them is `1`.
  let g : GL Unit (LocField w) := diagGL fun _ ↦ uniformizer w ^ z
  let y : GL Unit (LocField w) := diagGL fun _ ↦ uniformizer w ^ (-z).toNat
  have h_pow (i : ℕ) : (uniformizer w).val ^ i ∈ LocInt w :=
    (LocInt w).pow_mem ((v_uniformizer w).trans_le (by decide)) i
  have h_sat : IsSaturating (LocInt w).matrix ((singleGL w g).map (evalAt w)) y := by
    -- The witnesses are `l = y⁻¹ - g` and `m = 1` in `y⁻¹ = l + m g`.
    refine ⟨?_, ?_, _, ?_, 1, ?_, eq_add_of_sub_eq rfl⟩
    all_goals cases z <;> simp [g, y, mem_subring_matrix_iff, sub_mem, h_pow]
  have h_ord : (-(v y.val.det).log).toNat = (-z).toNat := by cases z <;> simp [y]
  rw [glMultiplier_eq_pow_of_local (by simp +contextual [g]) h_sat, h_ord]

omit [WeilData E] in
/-- In rank one a point at `w` lies in the integral level `localIntGL Unit w` exactly when its
determinant has order zero. -/
lemma mem_localIntGL_unit_iff (g : GL Unit (LocField w)) :
    g ∈ localIntGL Unit w ↔ (v g.val.det).log = 0 := by
  have h_ne : v g.val.det ≠ 0 := by simp [-det_unique, GeneralLinearGroup.det_ne_zero]
  rw [← WithZero.exp_eq_one, WithZero.exp_log h_ne]
  refine mem_intGL_iff_det.trans ⟨And.right, fun hv ↦ ⟨?_, hv⟩⟩
  intro i j
  cases i
  cases j
  simpa only [Matrix.det_unique] using hv.le

/-- The vacuum coefficient in rank one at a split place `w`. Here `vacuumCoeff M b g = (b(det g) *
finMultiplier g ^ M)⁻¹` is the factor by which `g` changes the matrix coefficient of a vacuum. Let
`ν` have weight `l` and tame part `ψ`, trivial at `w` and `w̄`. Let `γ = ofSplitPlace (ϖ_w ^ z)` be
the unitary point with component `ϖ_w ^ z` at `w`, its conjugate inverse at `w̄` and `1` elsewhere.
Write `υ` for the splitting character (`upsilonU1` on `U(1)`), and
`ν̃(ϖ_u) = ν.baseChange.atUniformizer u` for the value of the base change of `ν`. Then
`vacuumCoeff (2 k) (ν υ ^ k) γ` is `(ν̃(ϖ_u) / q_u ^ k) ^ |z|`, with `u = w̄` if `z ≥ 0` and `u = w`
otherwise, where `q_u` is the norm of `u`. -/
lemma vacuumCoeff_ofSplitPlace_uniformizer_zpow {l : InfinitePlace E → ℤ}
    {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} (hν : ν.HasWeight l ψ) (hw : w.IsSplit)
    (hψ : ψ w = 1) (hψ_star : ψ (star w) = 1) (k : ℕ) (z : ℤ) :
    vacuumCoeff (2 * k) (ν * upsilonU1 ^ k)
        (ofSplitPlace hw (diagGL fun _ : Unit ↦ uniformizer w ^ z)) =
      (ν.baseChange.atUniformizer (star w) / (star w).q ^ k) ^ z.toNat *
        (ν.baseChange.atUniformizer w / w.q ^ k) ^ (-z).toNat := by
  set g : GL Unit (LocField w) := diagGL fun _ ↦ uniformizer w ^ z with hg
  let χ : HeckeChar E := (ν * upsilonU1 ^ k).baseChange
  -- The multiplier is the product of the factors at `w` and `w̄`.
  have h_mult : finMultiplier (ofSplitPlace hw g) =
      (υ.atUniformizer w * √w.q) ^ (-z).toNat * starRingEnd ℂ
        ((υ.atUniformizer w * √w.q) ^ z.toNat) := by
    have h_split : finMultiplier (ofSplitPlace hw g) = glMultiplier
      (singleGL w g * star (singleGL w g⁻¹)) :=
      rfl
    rw [h_split, glMultiplier_mul_of_map_evalAt_eq_one
        (by grind [evalAt_star_singleGL, evalAt_singleGL_of_ne]),
      glMultiplier_star]
    simp [hg, ← map_inv, Pi.inv_def, ← _root_.zpow_neg, glMultiplier_singleGL_uniformizer_zpow]
  -- The determinant is `x / x̄` for the idele `x` of `det g` at `w`, where `χ` is unramified.
  have h_idele : detFin 1 (ofSplitPlace hw g) = divStar (locFullIdele w g.det) := by
    simp [G.detFin_of_mem_supportedOn (by simp [hw]) (ofSplitPlace_mem_supportedOn hw g),
      ← coe_singleton, detOn_eq_prod]
  have h_det : ((ν * upsilonU1 ^ k).val (detFin 1 (ofSplitPlace hw g)) : ℂ) = χ.atUniformizer w ^
    z := by
    have h_unram : CharUnramifiedAt χ.finPart w :=
      (hν.mul_upsilonU1_pow k).charUnramifiedAt hψ hψ_star
    rw [h_idele]
    exact (h_unram.apply_locFullIdele g.det).trans (by simp [hg])
  have h_unif : χ.atUniformizer w = ν.baseChange.atUniformizer w * υ.atUniformizer w ^ (2 * k) := by
    simp [χ, HeckeChar.atUniformizer, pow_mul]
  have h_conj : starRingEnd ℂ (υ.atUniformizer w) = (υ.atUniformizer w)⁻¹ := by
    simp [HeckeChar.atUniformizer, finPart, ← Circle.coe_inv_eq_conj]
  rw [vacuumCoeff, h_det, h_mult, h_unif, hν.atUniformizer_star hψ hψ_star, q_star,
    w.coe_q_eq_sq_sqrt]
  have h_ne : υ.atUniformizer w ≠ 0 := Units.ne_zero _
  -- For either sign of `z` the powers of `υ.atUniformizer w` cancel.
  obtain ⟨i, rfl | rfl⟩ := z.eq_nat_or_neg
  all_goals
    simp [h_conj, mul_pow]
    field

open scoped Classical in
/-- Let `ν` have weight `l` and tame part `ψ`, trivial at the place `w` and at its conjugate `w̄`,
and let `k > 1`.
There is a family `r` of finite points of `U(1)` supported at `w` and `w̄` such that (a) `r`
represents the cosets of the points integral at `w`, and (b) the sum over `r` of the vacuum
coefficients `vacuumCoeff (2 k) (ν υ ^ k)` is the product over `u ∈ {w, w̄}` of
`(1 - ε_u q_u ^ (-k)) / (1 - ν̃(ϖ_u)⁻¹ q_u ^ (-k))`, where `ν̃` is the base change `ν.baseChange`.
Here `ε = placeSign` is the sign that is `1` when `u = ū` (inert or ramified), and `-1` for one
place and `1` for the other of a split pair `u ≠ ū` (fixed by a well-ordering); `υ` is the splitting
character, `upsilonU1` its restriction to `U(1)`, and `localLevel Unit {w}` consists of the points
integral at `w`. -/
lemma exists_hasSum_vacuumCoeff_at_place {l : InfinitePlace E → ℤ}
    {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} {k : ℕ} (hν : ν.HasWeight l ψ) (hψ : ψ w = 1)
    (hψ_star : ψ (star w) = 1) (hk : 1 < k) :
    ∃ (ι : Type) (r : ι → supportedOn Unit {w}),
      (∀ g : Gf E Unit, ∃! γ : ι, (r γ).val⁻¹ * g ∈ localLevel Unit {w}) ∧
      HasSum (fun γ : ι ↦ vacuumCoeff (2 * k) (ν * upsilonU1 ^ k) (r γ).val)
        (∏ u ∈ {w, star w},
          (1 - placeSign u / u.q ^ k) / (1 - (ν.baseChange.atUniformizer u)⁻¹ / u.q ^ k)) := by
  -- The coset of `g` is determined by the valuation of its component at `w`. If `star w = w`
  -- there is one coset; if not, the cosets are those of the powers of the uniformiser, and the sum
  -- over `ℤ` splits into two geometric series.
  by_cases hw : star w = w
  · refine ⟨Unit, 1, fun g ↦ ?_, ?_⟩
    · -- Unitarity makes the valuation equal to its negative.
      have h_log : (v (g.atPlace w).val.det).log = 0 := by
        simpa [self_eq_neg] using congrArg (fun A ↦ (v A.det).log) (g.atPlace_star hw)
      simpa [mem_localIntGL_unit_iff, localLevel] using h_log
    · -- Both sides are `1`: the coefficient at `g = 1`, and the factor, as `placeSign w` and
      -- `ν.baseChange.atUniformizer w` are both `1`.
      have h_value : ν.baseChange.atUniformizer w = 1 := by
        rw [HeckeChar.atUniformizer, hν.baseChange_finPart_locIdele_eq_one hw hψ, Units.val_one]
      simp [vacuumCoeff, finMultiplier_eq_one_of_mem, placeSign, irrefl, hw, h_value,
        hk.ne_zero, w.one_lt_q.ne', Prod.mk_one_one, sub_eq_zero]
  -- Split case: `r z` has the component `uniformizer w ^ z` at `w`.
  let r (z : ℤ) : supportedOn Unit {w} :=
    ⟨_, ofSplitPlace_mem_supportedOn hw (diagGL fun _ ↦ uniformizer w ^ z)⟩
  have h_coset (g : Gf E Unit) (z : ℤ) :
      (r z).val⁻¹ * g ∈ localLevel Unit {w} ↔ z = -(v (g.atPlace w).val.det).log := by
    simp [r, mem_localIntGL_unit_iff, localLevel, add_eq_zero_iff_eq_neg, -det_unique,
      GeneralLinearGroup.det_ne_zero]
  refine ⟨ℤ, r, fun g ↦ by simp only [h_coset, existsUnique_eq], ?_⟩
  -- The ratios of the two geometric series.
  let ξ (u : FinPlace E) : ℂ := ν.baseChange.atUniformizer u / u.q ^ k
  have norm_lt (u : FinPlace E) : ‖ξ u‖ < 1 := by simp [ξ, field, one_lt_pow₀, hk.ne_zero]
  have geometric (u : FinPlace E) : HasSum (fun i : ℕ ↦ ξ u ^ i) (1 - ξ u)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (norm_lt u)
  have at_star : ν.baseChange.atUniformizer (star w) = (ν.baseChange.atUniformizer w)⁻¹ :=
    hν.atUniformizer_star hψ hψ_star
  have h_coeff (z : ℤ) : vacuumCoeff (2 * k) (ν * upsilonU1 ^ k) (r z).val =
      ξ (star w) ^ z.toNat * ξ w ^ (-z).toNat :=
    vacuumCoeff_ofSplitPlace_uniformizer_zpow hν hw hψ hψ_star k z
  -- By `placeSign_factor_mul` the numerators multiply to `1 - x ^ 2` with `x = (w.q ^ k)⁻¹`,
  -- and `x ^ 2` is the product of the two ratios.
  have numerator : (1 - placeSign w / w.q ^ k) *
      (1 - placeSign (star w) / (star w).q ^ k) = 1 - ξ (star w) * ξ w := by
    have h_ne : ν.baseChange.atUniformizer w ≠ 0 := Units.ne_zero _
    rw [mul_comm, q_star, div_eq_mul_inv, div_eq_mul_inv, placeSign_factor_mul hw]
    simp [ξ, at_star, q_star, field]
  have denominator : (1 - (ν.baseChange.atUniformizer w)⁻¹ / w.q ^ k) *
      (1 - (ν.baseChange.atUniformizer (star w))⁻¹ / (star w).q ^ k) = (1 - ξ (star w)) *
        (1 - ξ w) := by
    simp [ξ, at_star, q_star]
  have ne_zero (u : FinPlace E) : 1 - ξ u ≠ 0 := (isUnit_one_sub_of_norm_lt_one (norm_lt u)).ne_zero
  have sum_eq : (1 - ξ (star w) * ξ w) / ((1 - ξ (star w)) * (1 - ξ w)) =
      (1 - ξ (star w))⁻¹ + (1 - ξ w)⁻¹ * ξ w := by
    field_simp [ne_zero]
    ring
  rw [prod_pair (Ne.symm hw), div_mul_div_comm, numerator, denominator, sum_eq, funext h_coeff]
  -- The terms with `z ≥ 0` and those with `z < 0` form one geometric series each.
  refine .of_nat_of_neg_add_one (by simpa using geometric (star w)) ?_
  have h_toNat (i : ℕ) : (-1 + -(i : ℤ)).toNat = 0 := by omega
  simpa [pow_succ, add_nonneg, h_toNat] using (geometric w).mul_right (ξ w)

variable {l : InfinitePlace E → ℤ} {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}

open scoped Classical in
/-- The sum of the vacuum coefficients at one place of the real subfield. Let `ν` have weight `l`
and tame part `ψ`, trivial at `w` and `w̄`, and let `k > 1`. In rank one the sum `vacuumSum` at
`{w, w̄}` of the coefficients `vacuumCoeff (2 k) (ν υ ^ k)` is the product over `u ∈ {w, w̄}` of
`(1 - ε_u q_u ^ (-k)) / (1 - ν̃(ϖ_u)⁻¹ q_u ^ (-k))`. Here `υ` is the splitting character
(`upsilonU1` on `U(1)`), `ε` is `placeSign`, `ν̃` is the base change `ν.baseChange`, `ϖ_u` is
the uniformiser at `u` and `q_u` the norm of `u`. -/
lemma vacuumSum_pair {k : ℕ} (hν : ν.HasWeight l ψ) (hψ : ψ w = 1) (hψ_star : ψ (star w) = 1)
    (hk : 1 < k) :
    vacuumSum Unit (2 * k) (ν * upsilonU1 ^ k) {w, star w} =
      ∏ u ∈ {w, star w},
        (1 - placeSign u / u.q ^ k) / (1 - (ν.baseChange.atUniformizer u)⁻¹ / u.q ^ k) := by
  obtain ⟨ι, r, h_rep, h_sum⟩ := exists_hasSum_vacuumCoeff_at_place hν hψ hψ_star hk
  have hψ_pair : ∀ u ∈ ({w, star w} : Set (FinPlace E)).conjClosure, ψ u = 1 := by
    grind [star_star, star_inj]
  have h_unram : IsUnramifiedOn (ν * upsilonU1 ^ k) Unit {w, star w} :=
    (hν.mul_upsilonU1_pow k).isUnramifiedOn hψ_pair
  -- A point is integral at `w̄` if and only if it is integral at `w`.
  have h_level : localLevel Unit ({w, star w} : Set (FinPlace E)) = localLevel Unit {w} :=
    Subgroup.ext fun g ↦ by simp [mem_localLevel]
  rw [vacuumSum_eq_tsum h_unram (2 * k) (r := fun γ : ι ↦ (r γ).val)
    (fun γ ↦ supportedOn_mono (by simp) (r γ).property) (by rwa [h_level]), h_sum.tsum_eq]

omit [DecidableEq m] in
/-- The Euler product in rank one. Let `ν` have weight `l` and tame part `ψ`, trivial off the set
`S` of places, let `D = S ∪ S̄`, and let the second space have rank `card m = 2 k` with `k > 1`. The
sum `vacuumSum` of the coefficients `vacuumCoeff (2 k) (ν υ ^ k)` over the cosets at the places off
`D` is `L^D(k)` divided by the Euler product at `k` of the signs `placeSign` off `D`. Here `υ` is
the splitting character (`upsilonU1` on `U(1)`), and `L^D = ν⁻¹.L S` is the `L`-function of the base
change of `ν⁻¹` without the factors at `D`, equal to `ν.L S` (`New.AutChar.HasWeight.L_inv`). If `E`
is unramified over its real subfield `F` off `D`, the denominator is the value at `2 k` of the zeta
function of `F` without the places below `D`. -/
theorem vacuumSum_eq_L_div_eulerProd {k : ℕ} (hν : ν.HasWeight l ψ) {S : Set (FinPlace E)}
    (hψ : ∀ w : FinPlace E, w ∉ S → ψ w = 1) (h_rank : card m = 2 * k) (hk : 1 < k) :
    vacuumSum Unit (card m) (ν * upsilonU1 ^ k) S.conjClosureᶜ =
      ν⁻¹.L S k / eulerProd (S.conjClosureᶜ.indicator placeSign) k := by
  -- Both sides are products over the pairs `{w, w̄}` off `D`, and `vacuumSum_pair` compares the
  -- factors.
  let D : Set (FinPlace E) := S.conjClosure
  have hD_star (w : FinPlace E) : star w ∈ Dᶜ ↔ w ∈ Dᶜ := by simp [D, and_comm]
  have hψ_off (w : FinPlace E) (hw : w ∈ Dᶜ) : ψ w = 1 := hψ w fun h ↦ hw (.inl h)
  have hk_real : 1 < (k : ℝ) := by exact_mod_cast hk
  let a : FinPlace E → ℂ := heckeCoeff ν⁻¹.baseChange.finPart D
  let ε : FinPlace E → ℂ := Dᶜ.indicator placeSign
  have ha (w : FinPlace E) : ‖a w‖ ≤ 1 := hν.inv.isHeckeOfType.norm_heckeCoeff_le w
  have hε (w : FinPlace E) : ‖ε w‖ ≤ 1 :=
    (norm_indicator_le_norm_self _ w).trans (norm_placeSign_le w)
  have hζ_ne : eulerProd ε k ≠ 0 := by
    simp [eulerProd_eq_exp_neg_tsum_log_of_norm_le_one hε hk_real]
  let loc (w : FinPlace E) : ℂ :=
    (1 - a w * w.q ^ (-(k : ℝ) : ℂ))⁻¹ / (1 - ε w * w.q ^ (-(k : ℝ) : ℂ))⁻¹
  have h_prod : HasProd loc (ν⁻¹.L S k / eulerProd ε k) :=
    (hasProd_eulerProd ha hk_real).div₀ (hasProd_eulerProd hε hk_real) hζ_ne
  have h_loc_one (w : FinPlace E) (hw : w ∉ Dᶜ) : loc w = 1 := by
    simp [loc, a, ε, heckeCoeff, Set.indicator_of_notMem hw]
  have h_loc_eq (w : FinPlace E) (hw : w ∈ Dᶜ) : loc w =
      (1 - placeSign w / w.q ^ k) / (1 - (ν.baseChange.atUniformizer w)⁻¹ / w.q ^ k) := by
    simp [loc, a, ε, heckeCoeff, Set.indicator_of_mem hw, HeckeChar.atUniformizer, Complex.cpow_neg,
      div_eq_mul_inv, mul_comm]
  have h_unram : IsUnramifiedOn (ν * upsilonU1 ^ k) Unit Dᶜ :=
    (hν.mul_upsilonU1_pow k).isUnramifiedOn fun w hw ↦ hψ_off w (hw.elim id (hD_star w).1)
  refine vacuumSum_eq_of_hasProd (by simp [h_rank, hk]) hD_star h_unram h_prod h_loc_one
    fun w hw ↦ ?_
  have hw_star : star w ∈ Dᶜ := (hD_star w).2 hw
  rw [h_rank, vacuumSum_pair hν (hψ_off w hw) (hψ_off _ hw_star) hk]
  exact prod_congr rfl (by simp [h_loc_eq w hw, h_loc_eq _ hw_star])

end New

end
