module

import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Lib.GaloisRep.BaseChange.PrimeDegreeTransfer
public import Lib.GaloisRep.LocalGlobal.LocalFormTypes
import Lib.Adelic.Landherr
import Lib.GaloisRep.BaseChange.StepMatchingPairs
import Lib.GaloisRep.Hilbert90.TameActions
import Lib.GaloisRep.Hilbert90.UnitaryGroups
import Lib.General.LinearAlgebra.Eigenvalues
import Lib.General.LinearAlgebra.MatrixPolynomials
import Lib.LocalGL.Iwahori.HeckeDegrees
import Lib.LocalGL.Iwahori.QuadraticRelation
import Lib.PadicComparison.Descent.TestCategory
import Mathlib.Algebra.Order.Star.Int
public import Lib.GaloisRep.Main.AllRanks
public import Lib.LocalGL.Iwahori.SphericalExponents
public import Lib.Weil.Unramified.HeckeGL
import Lib.ClassField.Global.AlbertBrauerHasseNoether
import Lib.ClassField.Global.ArtinMap
import Lib.ClassField.Global.ExistenceTheorem
import Lib.ClassField.Places.TameInertia
import Lib.GaloisRep.Main.OddRank
import Lib.General.Algebra.LevelModulus
import Lib.General.NumberTheory.FrobeniusOrbits
import Lib.LocalGL.Iwahori.SortedExponents
import Lib.PadicHodge.Crystalline.Regularity

section
/-!
# Hilbert 90 for the pro-p Iwahori group and base change of Iwahori eigenforms

`F` is a valued field with compact ring of integers, and `σ` is an isometric endomorphism with
`σ ^ p = 1`. `New.proIwahori` is the pro-`p` Iwahori subgroup of `GL n F`, the matrices that are
upper unitriangular modulo the maximal ideal. `New.twistedNorm τ p δ = δ * τ δ * ⋯ * τ ^ (p - 1) δ`
is the twisted norm. The file proves a Hilbert 90 statement and a matching of dominant double cosets
for this group. These local results give matching local data at a place with exactly one place above
it.

## Main definitions and results

* `New.exists_coboundary_proIwahori`: if some integer of `F` has `σ`-trace `1`, an element of
  `New.proIwahori` of norm `1` is a coboundary `t * (σ t)⁻¹` with `t` in `New.proIwahori`.
* `New.proIwahori_doubleCoset_match`: the double cosets of a strictly dominant diagonal matrix over
  `F` and of its norm over the fixed field correspond under `γ ↦ z γ` for a polynomial `z`
  (`New.IsIwahoriMatchingPolynomial`).
* `New.isLocalMatching_proIwahori`: the indicator functions of the double cosets `K N(t) K` at `w`
  and `K' t K'` at `u` are matching local data (`New.IsLocalMatching`). It globalises
  `New.proIwahori_doubleCoset_match` and `New.exists_coboundary_proIwahori`.
* `New.exists_baseChange_isIwahoriEigen`: feeding these into
  `New.exists_isWeakBaseChange_of_matching` gives a base change whose eigencharacter at `u` is that
  of `f` at `w` composed with `N`.

Notions from other files:
* `New.IsStep E' μ`: a step `E'/E`. The field `E` contains a primitive `5040`-th root of unity,
  `E'` is a CM field Galois over `E` of prime degree with an integer of trace `1`, and `μ` is the
  character of the finite ideles of `E` that goes with the extension.
* `New.locIdele`: the homomorphism that sends `x` in the units of the completion at `v` to the
  finite idele with component `x` at `v` and `1` elsewhere.
* `New.iwahoriDoubleCoset t`: the double coset `K t K` of the diagonal matrix `t`, where `K` is
  `New.proIwahori`.
* `New.diagGL t`: the diagonal matrix with the units `t i` on the diagonal, as an element of `GL`.

## Relation to the literature

Known; see `Lib.GaloisRep.BaseChange.PrimeDegreeTransfer` for sources.
-/

@[expose] public section

namespace New

/-!
## Hilbert 90 and matching of dominant double cosets

The matching uses that such a double coset is `σ`-conjugate into the torus
(`New.exists_inv_mul_mul_map_eq_diagGL_mul`) and that the eigenvalues are told apart by their
valuations.
-/

section IwahoriMatching

open Matrix WithZero Valued Polynomial GeneralLinearGroup DoubleCoset Finset Function

variable {F F' : Type*}
  {N : ℕ} [Field F] [Valued F ℤᵐ⁰] [Field F'] [Valued F' ℤᵐ⁰]
  [CompactSpace 𝒪[F']] {σ : F →+* F} {p : ℕ}

/-- Let `σ` be an endomorphism of `F` that keeps the valuation. Then `g ∈ GL N F` lies in the
pro-`p` Iwahori subgroup `New.proIwahori` exactly when `σ g`, with `σ` applied to the entries,
does. -/
lemma map_mem_proIwahori_iff_of_isometry (hv : ∀ x : F, v (σ x) = v x) {g : GL (Fin N) F} :
    g.map σ ∈ proIwahori ↔ g ∈ proIwahori :=
  map_mem_proIwahori_iff_of_isEquiv (.of_eq (Valuation.ext hv : v.comap σ = v))

lemma v_ringHom_pow_apply (hv : ∀ x : F, v (σ x) = v x) (i : ℕ) (x : F) :
    v ((σ ^ i) x) = v x := by
  rw [RingHom.coe_pow]
  induction i with
  | zero => rfl
  | succ i ih => rw [iterate_succ_apply', hv, ih]

/-- Hilbert 90 for the pro-`p` Iwahori subgroup `New.proIwahori` of `GL N F`. Let `σ` be an
endomorphism of `F` that keeps the valuation, with `σ ^ p = 1`, and let `c` be an integer of `F`
with trace `∑ i < p, σ ^ i c = 1`. If `s ∈ proIwahori` has twisted norm
`s * σ s * ⋯ * σ ^ (p - 1) s = 1` (`New.twistedNorm`, with `σ` acting on the entries), then
`s * σ t = t` for some `t ∈ proIwahori`. -/
lemma exists_coboundary_proIwahori (hv : ∀ x : F, v (σ x) = v x) (hσ : σ ^ p = 1) {c : F}
    (hc_int : v c ≤ 1) (hc_trace : ∑ i ∈ range p, (σ ^ i) c = 1)
    {s : GL (Fin N) F} (hs_mem : s ∈ proIwahori) (hs_norm : twistedNorm (.map σ) p s = 1) :
    ∃ t ∈ proIwahori, s * t.map σ = t := by
  -- Take `t = ∑ l < p, σ ^ l c • n l`, where `n l` is the partial twisted norm of `s` of length
  -- `l`. Every `n l` lies in `proIwahori`, which gives three conditions on its entries.
  have hn (l : ℕ) := mem_proIwahori.mp <| twistedNorm_mem (GeneralLinearGroup.map σ) l
    (fun _ ↦ (map_mem_proIwahori_iff_of_isometry hv).mpr) hs_mem
  let a (l : ℕ) : Matrix (Fin N) (Fin N) F := (σ ^ l) c • (twistedNorm (.map σ) l s).val
  let M := ∑ l ∈ range p, a l
  have hc_pow (l : ℕ) : v ((σ ^ l) c) ≤ 1 := by rwa [v_ringHom_pow_apply hv]
  have hM (i j : Fin N) : M i j = ∑ l ∈ range p, (σ ^ l) c * twistedNorm (.map σ) l s i j := by
    simp [M, a, Matrix.sum_apply]
  -- Modulo the maximal ideal `M` is upper triangular, with diagonal entries `∑ σ ^ l c = 1`.
  obtain ⟨t, ht, htM⟩ := exists_proIwahori_coe_eq_of_residue_unitriangular M
    (fun i j ↦ hM i j ▸ v.map_sum_le fun l _ ↦
      (v.map_mul _ _).trans_le (mul_le_one' (hc_pow l) ((hn l).1 i j)))
    (fun i j hij ↦ hM i j ▸ v.map_sum_lt one_ne_zero fun l _ ↦
      (v.map_mul _ _).trans_lt (mul_lt_of_le_one_of_lt (hc_pow l) ((hn l).2.1 i j hij)))
    (fun i ↦ by
      rw [show M i i - 1 = ∑ l ∈ range p, (σ ^ l) c * (twistedNorm (.map σ) l s i i - 1) by
        simp [hM, mul_sub_one, hc_trace, -RingHom.coe_pow]]
      exact v.map_sum_lt one_ne_zero fun l _ ↦
        (v.map_mul _ _).trans_lt (mul_lt_of_le_one_of_lt (hc_pow l) ((hn l).2.2 i)))
  -- The map `τ : m ↦ s * σ m` sends `a l` to `a (l + 1)` and `a p = a 0`, so `τ` fixes `M`.
  let τ : Matrix (Fin N) (Fin N) F →+ Matrix (Fin N) (Fin N) F :=
    (AddMonoidHom.mulLeft s.val).comp σ.mapMatrix.toAddMonoidHom
  have h_period : a p = a 0 := by
    simp only [a, hσ, hs_norm]
    simp [twistedNorm]
  refine ⟨t, ht, Units.ext ?_⟩
  change τ t.val = t.val
  rw [htM, fixed_sum τ a h_period fun l ↦ by
    simp [a, τ, pow_succ', twistedNorm_succ', map_smul', -RingHom.coe_pow]]

/-- Let `σ` be a continuous endomorphism of `F` that keeps the valuation, with `σ ^ p = 1` for some
`p > 0`, and let `t` be diagonal with `v (t i)` strictly increasing. Let `K` be the pro-`p` Iwahori
subgroup `New.proIwahori`. Every `δ` in the double coset `K t K` (`New.iwahoriDoubleCoset t`) is
`σ`-conjugate to `t * d` for some `d` diagonal in `K`: `k⁻¹ * δ * σ k = t * d` with `k ∈ K`. The
same `k` conjugates the twisted norm of `δ` (`New.twistedNorm`) to that of `t * d`. -/
private lemma exists_twisted_conj_diag_and_twistedNorm_conj [CompactSpace 𝒪[F]]
    (hv : ∀ x : F, v (σ x) = v x)
    (hσ : σ ^ p = 1) (hp : 0 < p) (hσ_cont : Continuous σ) {t : Fin N → Fˣ}
    (ht_mono : StrictMono fun i : Fin N ↦ v (t i).val) {δ : GL (Fin N) F}
    (hδ : δ ∈ iwahoriDoubleCoset t) :
    ∃ k ∈ proIwahori, ∃ d : Fin N → Fˣ, diagGL d ∈ proIwahori ∧
      k⁻¹ * δ * k.map σ = diagGL (t * d) ∧
      k⁻¹ * twistedNorm (.map σ) p δ * k = twistedNorm (.map σ) p (diagGL (t * d)) := by
  -- As `σ ^ p = 1` with `p > 0`, `σ` acts on `GL N F` with period `p`, hence onto.
  have h_iterate (i : ℕ) (k : GL (Fin N) F) : (map (n := Fin N) σ)^[i] k = k.map (σ ^ i) := by
    induction i generalizing k with
    | zero => rfl
    | succ i ih => exact ih (k.map σ)
  have h_period (k : GL (Fin N) F) : (map (n := Fin N) σ)^[p] k = k := by
    simp [h_iterate, hσ, RingHom.one_def]
  obtain ⟨k, hk, d, hd, h_conj⟩ := exists_inv_mul_mul_map_eq_diagGL_mul ht_mono σ hv hσ_cont
    (fun k ↦ periodicPts_subset_range ⟨p, hp, h_period k⟩) hδ
  refine ⟨k, hk, d, hd, h_conj, ?_⟩
  -- A twisted conjugation by `k`, which is fixed by `σ ^ p`, conjugates twisted norms.
  rw [← h_conj, twistedNorm_conj (GeneralLinearGroup.map σ) p (h_period k)]

/-- A point `x` of the double coset `K' s K'` over `F'` (`New.iwahoriDoubleCoset s`) is sent by `ι`
to a conjugate, by some `k ∈ New.proIwahori`, of the twisted norm (`New.twistedNorm`) of
`diagGL (t * d)` with `diagGL d ∈ New.proIwahori`. This uses that `ι s` is the twisted norm of
`diagGL t` (`hs_norm`) and that the `1`-units of `F'` are norms of `1`-units of `F` (`h_norms`). -/
private lemma exists_conj_map_eq_twistedNorm_diagGL {ι : F' →+* F} (h_val : (v.comap ι).IsEquiv v)
    (h_norms : ∀ x : F', v (ι x - 1) < 1 → ∃ y : Fˣ,
      v (y.val - 1) < 1 ∧ ∏ i ∈ range p, (σ ^ i) y = ι x)
    {t : Fin N → Fˣ} {s : Fin N → F'ˣ} (hs_mono : StrictMono fun i : Fin N ↦ v (s i).val)
    (hs_norm : (diagGL s).map ι = twistedNorm (GeneralLinearGroup.map σ) p (diagGL t))
    {x : GL (Fin N) F'} (hx : x ∈ iwahoriDoubleCoset s) :
    ∃ k ∈ proIwahori, ∃ d : Fin N → Fˣ, diagGL d ∈ proIwahori ∧
      k⁻¹ * x.map ι * k = twistedNorm (.map σ) p (diagGL (t * d)) := by
  -- With the trivial twist, `x` is conjugate to `diagGL (s * e)` with `e` diagonal in `K'`. The
  -- entries of `ι e` are norms of units `d i`, and then `ι (s * e)` is the twisted norm of
  -- `diagGL (t * d)`.
  obtain ⟨k, hk, e, he_mem, h_conj⟩ :=
    exists_inv_mul_mul_map_eq_diagGL_mul hs_mono (1 : F' →+* F') (by simp) continuous_id
      surjective_id hx
  have he_sub_one (i : Fin N) : v (ι (e i : F') - 1) < 1 := by
    simpa using h_val.lt_one_iff_lt_one.mpr (diagGL_mem_proIwahori.mp he_mem i)
  choose d hd hd_norm using fun i : Fin N ↦ h_norms (e i) (he_sub_one i)
  refine ⟨k.map ι, (map_mem_proIwahori_iff_of_isEquiv h_val).mpr hk, d,
    diagGL_mem_proIwahori.mpr hd, Units.ext ?_⟩
  -- Apply `ι` to `k⁻¹ * x * k = diagGL (s * e)` and compare the diagonal entries.
  rw [twistedNorm_diagGL]
  simpa [Units.ext_iff, hs_norm, hd_norm, prod_mul_distrib, -RingHom.coe_pow] using
    congrArg (GeneralLinearGroup.map ι) h_conj

/-- Let `σ` be an endomorphism of `F` that keeps the valuation, let `p > 0`, let `t` be diagonal
with `v (t i)` strictly increasing, and let `d`, `d'` be diagonal in the pro-`p` Iwahori subgroup
`New.proIwahori`. If the norms `∏ l < p, σ ^ l (t i * d i)` and `∏ l < p, σ ^ l (t j * d' j)` agree,
then `i = j`, since the valuation of the first is `v (t i) ^ p`. -/
private lemma eq_of_prod_ringHom_pow_apply_eq (hv : ∀ x : F, v (σ x) = v x) (hp : 0 < p)
    {t d d' : Fin N → Fˣ} (ht_mono : StrictMono fun i : Fin N ↦ v (t i).val)
    (hd : diagGL d ∈ proIwahori) (hd' : diagGL d' ∈ proIwahori) (i j : Fin N)
    (h_eq : ∏ l ∈ range p, (σ ^ l) ((t * d) i : F) = ∏ l ∈ range p, (σ ^ l) ((t * d') j : F)) :
    i = j := by
  have h_unit {e : Fin N → Fˣ} (he_mem : diagGL e ∈ proIwahori) (m : Fin N) : v (e m : F) = 1 := by
    simpa using v_diag_eq_one_of_mem_proIwahori he_mem m
  refine ht_mono.injective (show v (t i : F) = v (t j : F) from ?_)
  simpa [hp.ne', h_unit hd, h_unit hd', v_ringHom_pow_apply hv, -RingHom.coe_pow] using
    congrArg v h_eq

omit [Valued F ℤᵐ⁰] in
/-- Let `σ ^ p = 1`, and let the values `c i = ∏ l < p, σ ^ l (e i)` be distinct. If the polynomial
`z` takes the value `e i` at `c i` for every `i`, then the characteristic polynomial
`∏ i, (X - c i)` of `diagonal c` divides `N(z) - X`, where `N(z) = ∏ l < p, σ ^ l z` is the
twisted norm (`New.twistedNorm`) of `z`. -/
private lemma charpoly_diagonal_dvd_twistedNorm_sub_X (hσ : σ ^ p = 1) {c e : Fin N → F}
    (hc_inj : Injective c) (hc : ∀ i : Fin N, c i = ∏ l ∈ range p, (σ ^ l) (e i)) {z : F[X]}
    (hz : ∀ i : Fin N, z.eval (c i) = e i) :
    (diagonal c).charpoly ∣ twistedNorm (Polynomial.map σ) p z - X := by
  -- The roots `c i` are distinct, so it suffices that each is a root of `N(z) - X`. As `c i` is a
  -- norm, it is fixed by `σ`, so `(σ ^ l z) (c i) = σ ^ l (z (c i)) = σ ^ l (e i)`.
  rw [charpoly_diagonal]
  refine Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hc_inj) fun i ↦ ?_
  have h_eval_map (l : ℕ) : (z.map (σ ^ l)).eval (c i) = (σ ^ l) (e i) := by
    rw [← hz, ← eval_map_apply, σ.coe_pow, hc, (isFixedPt_prod_range_pow_apply hσ).iterate]
  have h_eval_norm : (twistedNorm (Polynomial.map σ) p z).eval (c i) = c i := by
    rw [twistedNorm_map_eq_prod, eval_prod]
    exact (prod_congr rfl fun l _ ↦ h_eval_map l).trans (hc i).symm
  rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_X, h_eval_norm, sub_self]

omit [Valued F ℤᵐ⁰] in
/-- Let `γ` have the characteristic polynomial of the diagonal matrix `diagonal c`, and let
`k⁻¹ * γ * k = diagonal c'`, where `c' i = c l` holds only for `i = l`. Then for every polynomial
`z` the matrix `z γ` is `k * diagonal (z ∘ c) * k⁻¹`. -/
private lemma aeval_eq_conj_diagonal_eval {c c' : Fin N → F} {k γ : GL (Fin N) F}
    (hγ : γ.val.charpoly = (diagonal c).charpoly) (h_conj : (k⁻¹ * γ * k).val = diagonal c')
    (h_inj : ∀ i l : Fin N, c' i = c l → i = l) (z : F[X]) :
    aeval γ.val z = k.val * diagonal (fun i : Fin N ↦ z.eval (c i)) * k⁻¹.val := by
  -- Each `c' i` is a root of the characteristic polynomial of `γ`, so it is some `c l`, and then
  -- `l = i`. So `k` intertwines `diagonal c` with `γ`, hence `z (diagonal c)` with `z γ`.
  have h_charpoly : (diagonal c').charpoly = (diagonal c).charpoly := by
    simp only [← h_conj, Units.val_mul, coe_units_inv, charpoly_units_conj', hγ]
  have h_eq : c' = c := by
    funext i
    have h_root : (diagonal c).charpoly.eval (c' i) = 0 := by
      simp [← h_charpoly, charpoly_diagonal, eval_prod, prod_eq_zero_iff, sub_eq_zero]
    obtain ⟨l, hl⟩ : ∃ l : Fin N, c' i = c l := by
      simpa [charpoly_diagonal, eval_prod, prod_eq_zero_iff, sub_eq_zero] using h_root
    rw [hl, h_inj i l hl]
  have h_semi : k.val * diagonalAlgHom F c = γ.val * k.val := by
    simp [← h_eq, ← h_conj, ← mul_assoc]
  have h_aeval_diag : aeval (diagonalAlgHom F c) z = diagonal fun i : Fin N ↦ z.eval (c i) := by
    rw [aeval_algHom_apply, diagonalAlgHom_apply, aeval_pi_apply]
    simp
  rw [← h_aeval_diag, aeval_semiconj h_semi z, mul_assoc, Units.mul_inv, mul_one]

omit [CompactSpace 𝒪[F']] in
/-- Descent for clause (a) of `New.proIwahori_doubleCoset_match`. Let `σ` preserve `v` and let the
`σ`-fixed elements of `F` lie in the range of `ι : F' →+* F`, with `v ∘ ι` equivalent to `v`. Let
`ι (diagGL s)` be the twisted norm (`New.twistedNorm`, over `σ`, `p` factors) of `diagGL t`, and let
`k, diagGL d ∈ New.proIwahori`, `a = k * diagGL (t * d₀) * k⁻¹` and
`k⁻¹ * a * σ k = diagGL (t * d)`. If `k⁻¹ * ι x * k` is the twisted norm of `diagGL (t * d)`, then
`x` lies in `I₁ diag(s) I₁` over `F'` (`New.iwahoriDoubleCoset s`). -/
private lemma mem_iwahoriDoubleCoset_of_conj_map_eq_twistedNorm (hv : ∀ x : F, v (σ x) = v x)
    {ι : F' →+* F} (h_range : ∀ x : F, σ x = x → x ∈ ι.range) (h_val : (v.comap ι).IsEquiv v)
    {t : Fin N → Fˣ} {s : Fin N → F'ˣ}
    (hs_norm : (diagGL s).map ι = twistedNorm (GeneralLinearGroup.map σ) p (diagGL t))
    {k a : GL (Fin N) F} (hk : k ∈ proIwahori) {d₀ d : Fin N → Fˣ} (hd : diagGL d ∈ proIwahori)
    (h_twist : k⁻¹ * a * k.map σ = diagGL (t * d)) (ha : k * diagGL (t * d₀) * k⁻¹ = a)
    {x : GL (Fin N) F'} (hx : k⁻¹ * x.map ι * k = twistedNorm (.map σ) p (diagGL (t * d))) :
    x ∈ iwahoriDoubleCoset s := by
  -- Let `e` be the diagonal of `k`. As `σ` multiplies each column of `k` by a scalar,
  -- `k * diagGL e⁻¹` is fixed by `σ`, so it is `ι g` for some `g` over `F'`. Then `x = g * s * r`,
  -- where `ι r = diagGL e * N(diagGL d) * k⁻¹` lies in `proIwahori`, as the twisted norm
  -- `N(t * d)` is `N(t) * N(d) = ι s * N(d)`.
  have hk_map : k.map σ = k * ((diagGL (t * d₀))⁻¹ * diagGL (t * d)) := by
    rw [← h_twist, ← ha]
    group
  have hσk (i j : Fin N) : σ (k i j) = k i j * (((t * d₀) j : F)⁻¹ * (t * d) j) := by
    simpa [← map_inv, mul_assoc] using congrArg (fun g : GL (Fin N) F ↦ g i j) hk_map
  have hk_diag (i : Fin N) : k i i ≠ 0 :=
    v.ne_zero_iff.mp (by simp [v_diag_eq_one_of_mem_proIwahori hk i])
  let e (i : Fin N) : Fˣ := .mk0 (k i i) (hk_diag i)
  obtain ⟨-, -, hk_diag_one⟩ := mem_proIwahori.mp hk
  have he_mem : diagGL e ∈ proIwahori := diagGL_mem_proIwahori.mpr hk_diag_one
  have h_fixed : (k * diagGL e⁻¹).map σ = k * diagGL e⁻¹ := by
    -- `map_inv` is left out: it would turn the diagonal of inverses into a matrix inverse.
    simp [Units.ext_iff, ← ext_iff, -map_inv, hσk, e, mul_assoc]
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin N) F', g.map ι = k * diagGL e⁻¹ :=
    exists_gl_map_eq_of_fixed ι.injective h_range h_fixed
  have h_map_r : ((g * diagGL s)⁻¹ * x).map ι =
      ((diagGL s).map ι)⁻¹ * (diagGL e * (k⁻¹ * x.map ι * k)) * k⁻¹ := by
    simp only [map_mul, map_inv, hg]
    group
  -- The diagonal matrices `diagGL e`, `N(t)` and `N(d)` commute, and `N(t * d) = N(t) * N(d)`.
  have h_diag_eq : diagGL e * twistedNorm (.map σ) p (diagGL (t * d)) =
      (diagGL s).map ι * (diagGL e * twistedNorm (.map σ) p (diagGL d)) := by
    simp only [hs_norm, Units.ext_iff, Units.val_mul, twistedNorm_diagGL]
    simp [prod_mul_distrib, mul_left_comm]
  have hr : ((g * diagGL s)⁻¹ * x).map ι = diagGL e * twistedNorm (.map σ) p (diagGL d) * k⁻¹ := by
    rw [h_map_r, hx, h_diag_eq, inv_mul_cancel_left]
  have hg_mem : g ∈ proIwahori := by
    rw [← map_mem_proIwahori_iff_of_isEquiv h_val, hg, map_inv]
    exact mul_mem hk (inv_mem he_mem)
  have hr_mem : (g * diagGL s)⁻¹ * x ∈ proIwahori := by
    rw [← map_mem_proIwahori_iff_of_isEquiv h_val, hr]
    exact mul_mem (mul_mem he_mem (twistedNorm_mem (GeneralLinearGroup.map σ) p
      (fun _ ↦ (map_mem_proIwahori_iff_of_isometry hv).mpr) hd)) (inv_mem hk)
  exact mem_doubleCoset.mpr ⟨g, hg_mem, _, hr_mem, (mul_inv_cancel_left _ x).symm⟩

/-- Let `σ` be an endomorphism of `F` that keeps the valuation, let `k`, `diagGL d₀` and `diagGL d`
lie in the pro-`p` Iwahori subgroup `New.proIwahori`, and let `k⁻¹ * δ * σ k = diagGL (t * d)` and
`a = k * diagGL (t * d₀) * k⁻¹`. Then `a⁻¹ * δ = k * diagGL (d₀⁻¹ * d) * (σ k)⁻¹` lies in
`New.proIwahori`. -/
private lemma inv_mul_mem_proIwahori_of_twisted_conj (hv : ∀ x : F, v (σ x) = v x)
    {t d₀ d : Fin N → Fˣ} {k a δ : GL (Fin N) F} (hk : k ∈ proIwahori)
    (hd₀ : diagGL d₀ ∈ proIwahori) (hd : diagGL d ∈ proIwahori)
    (h_twist : k⁻¹ * δ * k.map σ = diagGL (t * d)) (ha : k * diagGL (t * d₀) * k⁻¹ = a) :
    a⁻¹ * δ ∈ proIwahori := by
  have h_quot : a⁻¹ * δ = k * ((diagGL d₀)⁻¹ * diagGL d) * (k.map σ)⁻¹ := by
    rw [← ha, ← inv_mul_cancel_left (diagGL t) (diagGL d), ← map_mul, ← h_twist, map_mul]
    group
  rw [h_quot]
  exact mul_mem (mul_mem hk (mul_mem (inv_mem hd₀) hd))
    (inv_mem ((map_mem_proIwahori_iff_of_isometry hv).mpr hk))

variable (σ p) in
/-- The polynomial `z` over `F` matches the double cosets `K' s K'` over `F'` and `K t K` over `F`
at the polynomial `P`. Here `K`, `K'` are the pro-`p` Iwahori subgroups `New.proIwahori`, the
double cosets are `New.iwahoriDoubleCoset`, twisted norms (`New.twistedNorm`) are taken with the
endomorphism `σ` of `F` and length `p`, and `ι : F' →+* F`. In the last two fields `γ` has
characteristic polynomial `P` and `a = z γ`. -/
structure IsIwahoriMatchingPolynomial (ι : F' →+* F) (s : Fin N → F'ˣ) (t : Fin N → Fˣ)
    (P z : F[X]) : Prop where
  /-- The twisted norm `z * σ z * ⋯ * σ ^ (p - 1) z` is `X` modulo `P`. -/
  dvd_twistedNorm_sub_X : P ∣ twistedNorm (Polynomial.map σ) p z - X
  /-- If `γ = ι x` and `γ` is the twisted norm of `a`, then `x ∈ K' s K'` exactly when
  `a ∈ K t K`. -/
  mem_iwahoriDoubleCoset_iff : ∀ γ a : GL (Fin N) F, γ.val.charpoly = P → a.val = aeval γ.val z →
    ∀ x : GL (Fin N) F', x.map ι = γ → twistedNorm (GeneralLinearGroup.map σ) p a = γ →
      (x ∈ iwahoriDoubleCoset s ↔ a ∈ iwahoriDoubleCoset t)
  /-- Every `δ ∈ K t K` with twisted norm `γ` has `a⁻¹ * δ ∈ K`, so it lies in the coset `a K`. -/
  inv_mul_mem_proIwahori : ∀ γ a : GL (Fin N) F, γ.val.charpoly = P → a.val = aeval γ.val z →
    ∀ δ ∈ iwahoriDoubleCoset t, twistedNorm (GeneralLinearGroup.map σ) p δ = γ →
      a⁻¹ * δ ∈ proIwahori

/-- Matching at pro-`p` Iwahori level. Let `σ` be a continuous endomorphism of `F` that keeps the
valuation, with `σ ^ p = 1` and `p > 0`. Let `ι : F' →+* F` be a map whose image holds the points
fixed by `σ` (`h_range`), along which `v` restricts to a valuation equivalent to that of `F'`
(`h_val`), and such that every `x` with `v (ι x - 1) < 1` has `ι x = ∏ i < p, σ ^ i y` for a unit
`y` with `v (y - 1) < 1` (`h_norms`). Let `t` over `F` and `s` over `F'` have strictly increasing
valuations, with `ι (diagGL s)` the twisted norm (`New.twistedNorm`) of `diagGL t`. Let `P` be the
characteristic polynomial of `ι x` for `x` in `K' s K'`, or of the twisted norm of a point of
`K t K` (`New.iwahoriDoubleCoset`, with `K`, `K'` the groups `New.proIwahori`). Then some polynomial
`z` matches the two double cosets at `P` (`New.IsIwahoriMatchingPolynomial`): its twisted norm is
`X` modulo `P`, and for `γ` with characteristic polynomial `P` and `a = z γ`, (a) if `γ = ι x` is
the twisted norm of `a`, then `x ∈ K' s K' ↔ a ∈ K t K`; (b) every `δ ∈ K t K` with twisted norm `γ`
lies in `a K`. -/
lemma proIwahori_doubleCoset_match [CompactSpace 𝒪[F]]
    (hv : ∀ x : F, v (σ x) = v x) (hσ : σ ^ p = 1) (hp : 0 < p)
    (hσ_cont : Continuous σ) {ι : F' →+* F}
    (h_range : ∀ x : F, σ x = x → x ∈ ι.range) (h_val : (v.comap ι).IsEquiv v)
    (h_norms : ∀ x : F', v (ι x - 1) < 1 → ∃ y : Fˣ,
      v (y.val - 1) < 1 ∧ ∏ i ∈ range p, (σ ^ i) y = ι x)
    {t : Fin N → Fˣ} {s : Fin N → F'ˣ} (ht_mono : StrictMono fun i : Fin N ↦ v (t i).val)
    (hs_mono : StrictMono fun i : Fin N ↦ v (s i).val)
    (hs_norm : (diagGL s).map ι = twistedNorm (GeneralLinearGroup.map σ) p (diagGL t)) (P : F[X])
    (hP : P ∈ (fun γ : GL (Fin N) F ↦ γ.val.charpoly) ''
      (GeneralLinearGroup.map ι '' iwahoriDoubleCoset s ∪
        twistedNorm (GeneralLinearGroup.map σ) p '' iwahoriDoubleCoset t)) :
    ∃ z : F[X], IsIwahoriMatchingPolynomial σ p ι s t P z := by
  -- Points of `iwahoriDoubleCoset s` and norms from `iwahoriDoubleCoset t` are conjugate under
  -- `proIwahori` to diagonal matrices `ν d`, the norms of `diagGL (t * d)` with
  -- `diagGL d ∈ proIwahori`. The entries `ρ d i` of `ν d` are told apart by their valuations, so
  -- `P` determines them, and `z` interpolates from the entries of `ν d₀` to those of `t * d₀`.
  let ν (d : Fin N → Fˣ) : GL (Fin N) F := twistedNorm (.map σ) p (diagGL (t * d))
  let ρ (d : Fin N → Fˣ) (i : Fin N) : F := ∏ l ∈ range p, (σ ^ l) ((t * d) i)
  have hν (d : Fin N → Fˣ) : ν d = diagonal (ρ d) := twistedNorm_diagGL (t * d) p
  -- A norm `γ` of `δ ∈ K t K` is conjugated to `ν d` by the `k` that twists `δ` to `t * d`.
  have h_of_norm {γ δ : GL (Fin N) F} (hδ : δ ∈ iwahoriDoubleCoset t)
      (hδ_norm : twistedNorm (.map σ) p δ = γ) : ∃ k ∈ proIwahori, ∃ d : Fin N → Fˣ,
        diagGL d ∈ proIwahori ∧ k⁻¹ * δ * k.map σ = diagGL (t * d) ∧ k⁻¹ * γ * k = ν d := by
    subst hδ_norm
    exact exists_twisted_conj_diag_and_twistedNorm_conj hv hσ hp hσ_cont ht_mono hδ
  -- Conjugation keeps the characteristic polynomial, so `P` is that of some `ν d₀`.
  obtain ⟨γ₀, hγ₀_mem, rfl⟩ := hP
  obtain ⟨k₀, -, d₀, hd₀, h_conj₀⟩ : ∃ k ∈ proIwahori, ∃ d : Fin N → Fˣ, diagGL d ∈ proIwahori ∧
      k⁻¹ * γ₀ * k = ν d := by
    rcases hγ₀_mem with ⟨x, hx, rfl⟩ | ⟨δ, hδ, rfl⟩
    · exact exists_conj_map_eq_twistedNorm_diagGL h_val h_norms hs_mono hs_norm hx
    · obtain ⟨k, hk, d, hd, -, h_norm⟩ := h_of_norm hδ rfl
      exact ⟨k, hk, d, hd, h_norm⟩
  have hP : γ₀.val.charpoly = (diagonal (ρ d₀)).charpoly := by
    simp only [← hν, ← h_conj₀, Units.val_mul, coe_units_inv, charpoly_units_conj']
  have h_inj {d : Fin N → Fˣ} (hd : diagGL d ∈ proIwahori) :
      ∀ i l : Fin N, ρ d i = ρ d₀ l → i = l :=
    eq_of_prod_ringHom_pow_apply_eq hv hp ht_mono hd hd₀
  obtain ⟨z, hz⟩ : ∃ z : F[X], ∀ i : Fin N, z.eval (ρ d₀ i) = (t * d₀) i :=
    (exists_eval_eq_iff (ρ d₀) _).mpr fun i j h_eq ↦ by rw [h_inj hd₀ i j h_eq]
  -- If `k` conjugates `γ` to `ν d`, then `k` conjugates `a = z γ` to
  -- `z (ν d₀) = diagGL (t * d₀)`.
  have h_root {γ a : GL (Fin N) F} (hγ : γ.val.charpoly = (diagonal (ρ d₀)).charpoly)
      (ha : a.val = aeval γ.val z) {d : Fin N → Fˣ} (k : GL (Fin N) F)
      (hd : diagGL d ∈ proIwahori) (h_conj : k⁻¹ * γ * k = ν d) :
      k * diagGL (t * d₀) * k⁻¹ = a := by
    have h_diag : (k⁻¹ * γ * k).val = diagonal (ρ d) := by rw [h_conj, hν]
    rw [Units.ext_iff, ha, aeval_eq_conj_diagonal_eval hγ h_diag (h_inj hd) z, funext hz,
      Units.val_mul, Units.val_mul, coe_diagGL]
  simp only [hP]
  refine ⟨z, charpoly_diagonal_dvd_twistedNorm_sub_X hσ (h_inj hd₀) (fun i ↦ rfl) hz,
    ?_, fun γ a hγ ha δ hδ hδ_norm ↦ ?_⟩
  · rintro _ a hγ ha x rfl ha_norm
    refine ⟨fun hx_mem ↦ ?_, fun ha_mem ↦ ?_⟩
    · -- (a), left to right: `a = k * diagGL t * (diagGL d₀ * k⁻¹)`.
      obtain ⟨k, hk, d, hd, h_conj⟩ :=
        exists_conj_map_eq_twistedNorm_diagGL h_val h_norms hs_mono hs_norm hx_mem
      refine mem_doubleCoset.mpr ⟨k, hk, diagGL d₀ * k⁻¹, mul_mem hd₀ (inv_mem hk), ?_⟩
      simp only [← h_root hγ ha k hd h_conj, map_mul, mul_assoc]
    · -- (a), right to left.
      obtain ⟨k, hk, d, hd, h_twist, h_norm⟩ := h_of_norm ha_mem ha_norm
      exact mem_iwahoriDoubleCoset_of_conj_map_eq_twistedNorm hv h_range h_val hs_norm hk hd
        h_twist (h_root hγ ha k hd h_norm) h_norm
  · -- (b): `δ` lies in the coset `a K`.
    obtain ⟨k, hk, d, hd, h_twist, h_norm⟩ := h_of_norm hδ hδ_norm
    exact inv_mul_mem_proIwahori_of_twisted_conj hv hk hd₀ hd h_twist (h_root hγ ha k hd h_norm)

end IwahoriMatching

/-!
## Base change of Iwahori eigenforms at a place with one place above

Base change of Iwahori eigenforms along a step `E'/E` (`New.IsStep E' μ`), at a split place `w` of
`E` where `μ` is trivial and that has exactly one place `u` of `E'` above it, also split. `N` is the
local norm from `(LocField u)ˣ` to `(LocField w)ˣ`.

`New.proIwahori` is the pro-`p` Iwahori subgroup; `New.dominantTorus` the diagonal `t` with
non-decreasing absolute values; `New.IsIwahoriEigen ρ ξ f` says that `f ≠ 0` is fixed by
`New.proIwahori` and that the average of `ρ t f` over it is `ξ t • f` for dominant `t`. For a family
`θ` of `r` characters, `New.torusChar θ` is the character `t ↦ ∏ i, θ i (t i) * |t i| ^ (r - 1 - i)`
of the diagonal torus.
-/

section BaseChangeEigenchar

open Matrix Polynomial Valued Finset Patching

variable {E E' : Type} [Field E] [CMType E] [Field E'] [Algebra E E'] [CMTypeOver E E'] {m : Type _}
  {μ : (𝔸f E)ˣ →* ℂˣ} [Fintype m] [DecidableEq m] {u : FinPlace E'} [hμ : IsStep E' μ]
  {hw : (u.below E).IsSplit} (hu : u.IsSplit)

/-- At a place `u` of `E'` fixed by `τ`, the component at `u` of the `i`-th iterate of `τ` on
finite adeles is the `i`-th iterate of the local action `locMap τ hs` of `τ` on the completion at
`u`, applied to the component at `u`. -/
lemma iterate_adeleMap_apply {τ : Gal(E'/E)} (hs : u.comap τ = u) (i : ℕ) (x : 𝔸f E') :
    (adeleMap τ)^[i] x u = (locMap (τ : E' →+* E') hs)^[i] (x u) :=
  (Function.Semiconj.iterate_right (f := fun x : 𝔸f E' ↦ x u) (adeleMap_apply _ hs) i).eq x

/-- Local norms are onto the `1`-units at a place with one place above. Let `E'/E` be a step, `u`
the only place of `E'` above `w = u.below E` (`h_unique`), and `τ ≠ 1` fix `u`. Then every `x` at
`w` with `v (x - 1) < 1` is a norm `∏ i < [E' : E], (σ ^ i) y` of a unit `y` at `u` with
`v (y - 1) < 1`, where `σ = locMap τ hs` is the action of `τ` on the completion at `u`. -/
lemma exists_local_norm_eq
    (h_unique : ∀ u' : FinPlace E', FinPlace.below E u' = u.below E ↔ u' = u)
    {μ : (𝔸f E)ˣ →* ℂˣ} [IsStep E' μ] {τ : Gal(E'/E)} (hτ : τ ≠ 1)
    (hs : u.comap τ = u) (x : LocField (u.below E))
    (hx : v (locMap (algebraMap E E') rfl x - 1 : LocField u) < 1) :
    ∃ y : (LocField u)ˣ,
      v (y.val - 1) < 1 ∧
      ∏ i ∈ range (Module.finrank E E'), (locMap (τ : E' →+* E') hs ^ i) y =
        locMap (algebraMap E E') rfl x := by
  -- The integral adele `a` that is `x - 1` at `u` and `0` elsewhere is fixed by `τ` and reduces to
  -- `0` at every place, so `τ` is tame at level `a`; then `1 + a` is a norm of some `z ≡ 1`.
  obtain ⟨C, -, h_tame⟩ := exists_isTameAtLevel_intAdeleMap hτ
  set ι : LocField (u.below E) →+* LocField u := locMap (algebraMap E E') rfl
  let a : Ô E' :=
    ⟨singleAdele u (ι x - 1), by simpa +contextual [mem_Ô, ← and_forall_ne u] using hx.le⟩
  have ha_red : ∀ o : FinPlace E', reduceAt o a = 0 := by
    simp +contextual [hx, a, ← and_forall_ne u]
  -- `a` comes from the adele of `E` that is `x - 1` at `w`, as `u` is the only place above `w`
  have ha_range : a.val ∈ (finAdeleIncl E E').range := by
    refine ⟨singleAdele _ (x - 1), ?_⟩
    simp +contextual [DFunLike.ext_iff, ← and_forall_ne u, a, ι, h_unique, adeleMap_apply]
  have ha_fixed : intAdeleMap (τ : E' →+* E') a = a :=
    Subtype.ext (mem_range_finAdeleIncl_iff.mp ha_range τ)
  have h_unit : IsUnit (1 + a) := by
    simp [v.map_one_add_of_lt, ← reduceAt_eq_zero, ha_red]
  obtain ⟨z, hz_one, -, hz⟩ := (h_tame a ha_fixed fun o _ _ ↦
    ha_red o).exists_prod_range_pow_apply_eq
    (.inr isProfiniteRing_intAdeles) h_unit (by simp [ha_fixed]) (by simp)
  refine ⟨z.map ((evalAt u).domRestrict (Ô E')).toMonoidHom, ?_, ?_⟩
  · -- `z ≡ 1` modulo `a`, and `a` reduces to `0` at `u`
    have h_red : reduceAt u a ∣ reduceAt u ((z : Ô E') - 1) := map_dvd (reduceAt u) hz_one
    rw [ha_red u, zero_dvd_iff, reduceAt_eq_zero] at h_red
    simpa using h_red
  · -- read the norm equation `∏ (τ ^ i) z = 1 + a` at `u`
    simpa [iterate_adeleMap_apply hs, a] using congrArg (fun b : Ô E' ↦ evalAt u (b : 𝔸f E')) hz

include hμ in
/-- At a place `u` of `E'` fixed by `τ`, the local action `locMap τ hs` of `τ` on the completion
at `u` has order dividing `[E' : E]`. -/
private lemma locMap_pow_finrank_eq_one {τ : Gal(E'/E)} (hs : u.comap τ = u) :
    locMap (τ : E' →+* E') hs ^ Module.finrank E E' = 1 := by
  -- Read `adeleMap τ ^ [E' : E] = 1` at `u` on the adele that is `x` at `u` and `0` elsewhere.
  refine RingHom.ext fun x ↦ ?_
  simpa [iterate_adeleMap_apply hs] using congrArg
    (fun φ : 𝔸f E' →+* 𝔸f E' ↦ φ (singleAdele u x) u) (adeleMap_pow_finrank_eq_one (σ := τ))

include hμ in
/-- Fixed points of the local action come from below. Let `E'/E` be a step (so Galois of prime
degree), `u` the only place of `E'` above `w = u.below E` (`h_unique`), and `τ ≠ 1` fix `u`. Then
every `x` in the completion at `u` fixed by the local action `locMap τ hs` of `τ` is the image of an
element of the completion at `w`. -/
private lemma mem_range_locMap_of_locMap_eq_self
    (h_unique : ∀ u' : FinPlace E', FinPlace.below E u' = u.below E ↔ u' = u) {τ : Gal(E'/E)}
    (hτ : τ ≠ 1) (hs : u.comap τ = u) {x : LocField u} (hx : locMap (τ : E' →+* E') hs x = x) :
    x ∈ (locMap (algebraMap E E') rfl : LocField (u.below E) →+* LocField u).range := by
  -- The adele that is `x` at `u` and `0` elsewhere is fixed by `τ`, as `τ` fixes `u` and moves
  -- no other place onto `u`. So it comes from a finite adele `y` of `E`, and `x` is the image of
  -- the component of `y` at `w`.
  have h_single : adeleMap (τ : E' →+* E') (singleAdele u x) = singleAdele u x := by
    ext1 o
    obtain rfl | ho := eq_or_ne o u
    · simp [hx, hs, adeleMap_apply]
    · have h_comap_ne : FinPlace.comap (τ : E' →+* E') o ≠ u := by
        rwa [Ne, ← h_unique, below_comap, h_unique]
      simp [h_comap_ne, ho, adeleMap_apply]
  obtain ⟨y, hy⟩ : singleAdele u x ∈ (finAdeleIncl E E').range :=
    mem_range_finAdeleIncl_of_adeleMap_eq hτ h_single
  exact ⟨y (u.below E), by simp_all [← adeleMap_apply]⟩

include hμ in
/-- The local norm as a product of conjugates. At a place `u` of `E'` fixed by `τ ≠ 1`, along a step
`E'/E`, the local norm of `y`, mapped into the completion at `u`, is the product of the conjugates
`(σ ^ i) y`, `i < [E' : E]`, where `σ = locMap τ hs`. -/
private lemma locMap_localNorm_eq_prod {τ : Gal(E'/E)} (hτ : τ ≠ 1) (hs : u.comap τ = u)
    (y : (LocField u)ˣ) :
    locMap (algebraMap E E') rfl (localNorm E u y : LocField (u.below E)) =
      ∏ i ∈ range (Module.finrank E E'), (locMap (τ : E' →+* E') hs ^ i) (y : LocField u) := by
  -- The local norm is the component at `w` of the adelic norm of the idele `y` at `u`, and the
  -- adelic norm is the product of the Galois conjugates, which are the powers of `τ`.
  have h_unfold : (localNorm E u y : LocField (u.below E)) =
      adeleNorm E E' (locIdele u y : 𝔸f E') (u.below E) := rfl
  rw [h_unfold, ← adeleMap_apply, finAdeleIncl_adeleNorm, ← evalAt_apply, map_prod (evalAt u),
    prod_range, ← (bijective_pow_of_ne_one_of_prime_finrank hτ).prod_comp]
  simp [← adeleMap_gal_pow, iterate_adeleMap_apply hs]

include hμ in
/-- Cocycles split at pro-`p` Iwahori level at a place `u` fixed by `τ ≠ 1`, along a step `E'/E`.
Let `ρ` be a retraction of `embedAtSplit hu` at the places above `u.below E` and its conjugate
(`New.IsLocalRetraction`) that carries `galoisGf τ` to the entrywise action of `σ = locMap τ hs`.
Then at the level of the `δ` with `ρ δ ∈ proIwahori`, every `galoisGf τ`-cocycle is a coboundary on
those places (`New.CocyclesSplit`). -/
private lemma cocyclesSplit_comap_proIwahori {τ : Gal(E'/E)} (hτ : τ ≠ 1) (hs : u.comap τ = u)
    {ρ : Gf E' m →* GL (Fin (Fintype.card m)) (LocField u)}
    (hρ_retr : IsLocalRetraction (embedAtSplit hu) ρ (placesAbove E' {u.below E}))
    (hρ_gal : ∀ δ : Gf E' m, ρ (galoisGf τ δ) = (ρ δ).map (locMap (τ : E' →+* E') hs)) :
    CocyclesSplit (Module.finrank E E') (idem (placesAbove E' {u.below E})) (proIwahori.comap ρ)
      (galoisGf τ) := by
  -- Tameness at level `0` gives an integral adele `c` of trace `1`, so the component of `c` at `u`
  -- has `σ`-trace `1`, and a cocycle at `u` is a coboundary `t` there
  -- (`exists_coboundary_proIwahori`). Then `embedAtSplit hu t` splits the cocycle.
  intro δ hδ h_cocycle
  set σ : LocField u →+* LocField u := locMap (τ : E' →+* E') hs
  obtain ⟨C, -, h_tame⟩ := exists_isTameAtLevel_intAdeleMap hτ
  obtain ⟨-, ⟨c, hc_dvd⟩, -⟩ := h_tame 0 (by simp) (by simp)
  have hc_sum : ∑ i ∈ range (Module.finrank E E'), (intAdeleMap (τ : E' →+* E') ^ i) c = 1 := by
    rwa [zero_dvd_iff, sub_eq_zero] at hc_dvd
  have h_trace : ∑ i ∈ range (Module.finrank E E'), (σ ^ i) (c.val u) = 1 := by
    simpa [iterate_adeleMap_apply hs] using congrArg (fun b : Ô E' ↦ evalAt u (b : 𝔸f E')) hc_sum
  have hδ_norm : twistedNorm (.map σ) (Module.finrank E E') (ρ δ) = 1 := by
    rw [← map_twistedNorm ρ hρ_gal, h_cocycle, map_one]
  obtain ⟨t, ht, ht_eq⟩ : ∃ t ∈ proIwahori, ρ δ * t.map σ = t :=
    exists_coboundary_proIwahori (v_locMap_eq_of_surjective _ hs τ.surjective)
      (locMap_pow_finrank_eq_one hs) (mem_Ô.mp c.prop u) h_trace hδ hδ_norm
  obtain ⟨h_supp, h_retract, h_ker⟩ := hρ_retr
  refine ⟨embedAtSplit hu t, ?_, ?_, ?_⟩
  · -- `ρ` retracts `embedAtSplit hu`, so the component at `u` is `t ∈ proIwahori`
    rwa [Subgroup.mem_comap, h_retract]
  · -- `embedAtSplit hu t` is `1` off the places above `w`
    rw [← idem_compl, idem_smul_eq_iff_mem_trivialOn]
    simpa [Gf.trivialOn, Gf.supportedOn, Subgroup.mem_iInf] using h_supp t
  · -- above `w`, being trivial means lying in the kernel of `ρ`, and `t⁻¹ * ρ δ * σ t = 1`
    rw [idem_smul_eq_iff_mem_trivialOn, ← h_ker, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      hρ_gal, h_retract, mul_assoc, ht_eq, inv_mul_cancel]

/-- At a place `u` of `E'` fixed by `τ`, the twisted norm under `τ` of the adelic polynomial
`1 + idem {u} • (y - 1)`, which is `y` at `u` and `1` elsewhere, read at `u`, is the twisted norm
under the local action `locMap τ hs` of `y` read at `u`. -/
private lemma map_evalAt_twistedNorm_one_add_idem_smul {τ : Gal(E'/E)} (hs : u.comap τ = u)
    (p : ℕ) (y : (𝔸f E')[X]) :
    (twistedNorm (.map (adeleMap (τ : E' →+* E'))) p (1 + idem {u} • (y - 1))).map (evalAt u) =
      twistedNorm (.map (locMap (τ : E' →+* E') hs)) p (y.map (evalAt u)) := by
  -- Both sides are products of conjugates; compare them factor by factor and coefficient by
  -- coefficient.
  simp only [twistedNorm_map_eq_prod, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  ext k
  simp [iterate_adeleMap_apply hs]

/-- The indicators of `K N(t) K` (through `r`) and of `K t K` (through `ρ`) are a matching pair
above `w = u.below E` (`New.IsMatchingPairAbove`), for `t` with strictly increasing `v (t i)`. Here
`K = proIwahori`, `N(t) = localNorm E u ∘ t`, and `ρ`, `r` are the components at `u` and `w` of the
adelic groups `Gf E' m` and `Gf E m` (`baseChangeGf` maps `Gf E m` into `Gf E' m`), renumbered: `ρ`
carries `galoisGf τ` to `locMap τ hs`, keeps characteristic polynomials, and sends a base change to
`r` followed by the inclusion of the completion at `w`. -/
private lemma isMatchingPairAbove_proIwahori
    (h_unique : ∀ u' : FinPlace E', FinPlace.below E u' = u.below E ↔ u' = u)
    (hμ_loc : ∀ x : (LocField (FinPlace.below E u))ˣ, μ (locIdele (u.below E) x) = 1)
    (hw : (u.below E).IsSplit) {τ : Gal(E'/E)} (hτ : τ ≠ 1) (hs : u.comap τ = u)
    {ρ : Gf E' m →* GL (Fin (Fintype.card m)) (LocField u)}
    {r : Gf E m →* GL (Fin (Fintype.card m)) (LocField (u.below E))}
    (hρ_gal : ∀ δ : Gf E' m, ρ (galoisGf τ δ) = (ρ δ).map (locMap (τ : E' →+* E') hs))
    (hρ_val : ∀ g : Gf E' m, (ρ g).val =
      reindexAlgEquiv (LocField u) (LocField u) (Fintype.equivFin m) (g.atPlace u).val)
    (hρ_charpoly :
      ∀ g : Gf E' m, (ρ g).val.charpoly = (↑↑g : Matrix m m (𝔸f E')).charpoly.map (evalAt u))
    (hρ_baseChange : ∀ x : Gf E m, ρ (baseChangeGf x) = (r x).map (locMap (algebraMap E E') rfl))
    {t : Fin (Fintype.card m) → (LocField u)ˣ}
    (ht : StrictMono fun i : Fin (Fintype.card m) ↦ v (t i : LocField u)) :
    IsMatchingPairAbove (n := m) τ μ {u.below E} (proIwahori.comap ρ)
      ((iwahoriDoubleCoset (localNorm E u ∘ t)).indicator 1 ∘ r)
      ((iwahoriDoubleCoset t).indicator 1 ∘ ρ) := by
  -- At `u`, `τ` acts by an isometry `σ` of order dividing `[E' : E]` whose fixed points come from
  -- the completion at `w`, and the norm of `t` is `N(t)`. So `proIwahori_doubleCoset_match` gives a
  -- local polynomial `z`; its lift `1 + idem {u} • (y - 1)` is a root (`isNormRoot_of_one_side`).
  classical
  set σ : LocField u →+* LocField u := locMap (τ : E' →+* E') hs
  set ι : LocField (u.below E) →+* LocField u := locMap (algebraMap E E') rfl
  have hσ_v (x : LocField u) : v (σ x) = v x := v_locMap_eq_of_surjective _ hs τ.surjective x
  refine ⟨?_, ?_⟩
  · -- The indicator of `iwahoriDoubleCoset t` is invariant under twisted conjugation by
    -- `proIwahori`.
    simp +contextual [hρ_gal, hσ_v, map_mem_proIwahori_iff_of_isometry,
      (isHeckeFunction_doubleCoset isOpen_proIwahori _).2]
  · rintro _ ⟨g, hg, rfl⟩ -
    have hNt_mono : StrictMono fun i ↦ v ((localNorm E u ∘ t) i : LocField (u.below E)) := by
      simpa [StrictMono, ← toNormedField.norm_lt_iff] using ht
    have h_Nm : (diagGL (localNorm E u ∘ t)).map ι =
        twistedNorm (.map σ) (Module.finrank E E') (diagGL t) :=
      Units.ext (by simp [ι, σ, locMap_localNorm_eq_prod hτ hs])
    -- At `u`, the element `g` comes from the double coset of `N(t)` or is a norm from that of `t`.
    have hg_mem : ρ g ∈ .map ι '' iwahoriDoubleCoset (localNorm E u ∘ t) ∪
        twistedNorm (.map σ) (Module.finrank E E') '' iwahoriDoubleCoset t := by
      rcases hg with ⟨x, hx, rfl⟩ | ⟨δ, hδ, rfl⟩
      · exact Or.inl ⟨r x, Set.mem_of_indicator_ne_zero hx, (hρ_baseChange x).symm⟩
      · exact Or.inr ⟨ρ δ, Set.mem_of_indicator_ne_zero hδ, (map_twistedNorm ρ hρ_gal _ δ).symm⟩
    -- So there is a polynomial `z` over `LocField u` of norm `X` modulo the characteristic
    -- polynomial of `ρ g`, such that `γ ↦ z(γ)` matches the two double cosets.
    obtain ⟨z, hz_dvd, hz_iff, hz_coset⟩ :=
      proIwahori_doubleCoset_match hσ_v (locMap_pow_finrank_eq_one hs) hμ.out.pos (by fun_prop)
        (fun x hx ↦ mem_range_locMap_of_locMap_eq_self h_unique hτ hs hx)
        (isEquiv_comap_locMap (algebraMap E E') rfl) (exists_local_norm_eq h_unique hτ hs) ht
        hNt_mono h_Nm _ ⟨ρ g, hg_mem, hρ_charpoly g⟩
    -- Lift `z` to an adelic `y`; `1 + idem {u} • (y - 1)` is `y` at `u` and `1` elsewhere.
    obtain ⟨y, rfl⟩ := map_surjective (evalAt u) (fun x ↦ ⟨singleAdele u x, by simp⟩) z
    have h_dvd : (↑↑g : Matrix m m (𝔸f E')).charpoly.map (evalAt u) ∣
        (twistedNorm (.map (adeleMap τ)) (Module.finrank E E') (1 + idem {u} • (y - 1))).map
          (evalAt u) - X := by
      rwa [map_evalAt_twistedNorm_one_add_idem_smul hs]
    have hz_off : ∀ u' : FinPlace E', u'.below E ∉ ({u.below E} : Set (FinPlace E)) →
        (1 + idem {u} • (y - 1)).map (evalAt u') = 1 := by simp_all
    -- A root at `u` alone is a root above `w` and its conjugate (`h_root`), and the unitary `a`
    -- that it attaches to `γ` has component `y(γ)` at `u` (`h_comp`).
    obtain ⟨h_root, h_comp⟩ :=
      hμ.isNormRoot_of_one_side (n := m) (T := {u.below E}) rfl (by simpa using hμ_loc)
        (by simpa using hw) hz_off (by simpa [h_unique] using h_dvd)
    refine ⟨1 + idem {u} • (y - 1), h_root, fun γ a hγ ha ↦ ?_⟩
    have ha_u : (ρ a).val = aeval (ρ γ).val (y.map (evalAt u)) := by
      rw [hρ_val a, hρ_val γ, aeval_algHom_apply, h_comp γ a ha u rfl]
      simp
    have hγ_u : (ρ γ).val.charpoly = (↑↑g : Matrix m m (𝔸f E')).charpoly.map (evalAt u) := by
      rw [hρ_charpoly, hγ]
    have h_norm_u (b : Gf E' m) (hb : twistedNorm (galoisGf τ) (Module.finrank E E') b = γ) :
        twistedNorm (.map σ) (Module.finrank E E') (ρ b) = ρ γ := by
      rw [← map_twistedNorm ρ hρ_gal, hb]
    refine ⟨fun x hx hNm ↦ ?_, fun δ hδ_norm hδ_ne ↦ ?_⟩
    · -- (a): `x` is in the double coset of `N(t)` at `w` iff `a` is in that of `t` at `u`
      exact if_congr
        (hz_iff _ _ hγ_u ha_u _ (by rw [← hx, hρ_baseChange]) (h_norm_u a hNm)) rfl rfl
    · -- (b): a point `δ` of the double coset of `t` of norm `γ` lies in `a * proIwahori`
      simpa using hz_coset _ _ hγ_u ha_u _ (Set.mem_of_indicator_ne_zero hδ_ne)
        (h_norm_u δ hδ_norm)

/-- Matching local data at a place with one place above. Let `E'/E` be a step, `w = u.below E` split
(`hw`) with `μ` trivial at `w` (`hμ_loc`), and `u` the only place above `w` (`h_unique`), split
(`hu`). Then the indicators of `K N(t) K` at `w` and `K' t K'` at `u`, with `K`, `K'` the pro-`p`
Iwahori subgroups and `N(t) = localNorm E u ∘ t`, are matching local data (`New.IsLocalMatching`)
for the dominant `t` whose valuations `v (t i)` increase strictly. -/
lemma isLocalMatching_proIwahori
    (h_unique : ∀ u' : FinPlace E', FinPlace.below E u' = u.below E ↔ u' = u)
    (hμ_loc : ∀ x : (LocField (FinPlace.below E u))ˣ, μ (locIdele (u.below E) x) = 1) :
    IsLocalMatching (n := m) μ {u.below E} (embedAtSplit hw) (embedAtSplit hu) proIwahori proIwahori
      {t : dominantTorus | StrictMono fun i : Fin (Fintype.card m) ↦ v (t.val i).val}
      (fun t : dominantTorus ↦ (iwahoriDoubleCoset (localNorm E u ∘ t)).indicator 1)
      fun t : dominantTorus ↦ (iwahoriDoubleCoset t.val).indicator 1 := by
  -- Everything is read at `u`, where some `τ ≠ 1` acts by an isometry of order dividing `[E' : E]`
  -- whose fixed points come from the completion at `w`. The local results
  -- `cocyclesSplit_comap_proIwahori` and `isMatchingPairAbove_proIwahori` then give the splitting
  -- of cocycles and the matching of the two double cosets.
  let ε : m ≃ Fin (Fintype.card m) := Fintype.equivFin m
  -- `ρ` and `r` are the components at `u` and at `w`, renumbered; they retract the embeddings.
  set ρ : Gf E' m →* GL (Fin (Fintype.card m)) (LocField u) :=
    (reindexGL ε).toMonoidHom.comp (Gf.atPlace u)
  set r : Gf E m →* GL (Fin (Fintype.card m)) (LocField (u.below E)) :=
    (reindexGL ε).toMonoidHom.comp (Gf.atPlace (u.below E))
  obtain ⟨h_retr_w, h_retr_u, h_level⟩ := isLocalRetraction_ofSplitPlace m h_unique hu hw
  have hρ_retr : IsLocalRetraction (embedAtSplit hu) ρ (placesAbove E' {u.below E}) := by
    simp_all [IsLocalRetraction, ρ, ε]
  have hr_retr : IsLocalRetraction (embedAtSplit hw) r {u.below E} := by
    simp_all [IsLocalRetraction, r, ε]
  obtain ⟨τ, hτ⟩ := hμ.exists_gal_ne_one (E := E) (E' := E')
  have hs : u.comap τ = u := (h_unique _).mp (below_comap τ u)
  -- `ρ` carries `galoisGf τ` to the entrywise action of `τ` at `u`, and a base change to `r`
  -- followed by the inclusion of the completion at `w`.
  have hρ_gal (δ : Gf E' m) : ρ (galoisGf τ δ) = (ρ δ).map (locMap (τ : E' →+* E') hs) :=
    congrArg (reindexGL ε) (atPlace_galoisGf τ δ hs)
  have hρ_charpoly (g : Gf E' m) :
      (ρ g).val.charpoly = (↑↑g : Matrix m m (𝔸f E')).charpoly.map (evalAt u) :=
    (charpoly_reindex ε (g.atPlace u).val).trans (charpoly_map _ (evalAt u))
  have hρ_baseChange (x : Gf E m) :
      ρ (baseChangeGf x) = (r x).map (locMap (algebraMap E E') rfl) := rfl
  have h_stable (k : Gf E' m) : ρ (galoisGf τ k) ∈ proIwahori ↔ ρ k ∈ proIwahori := by
    rw [hρ_gal]
    exact map_mem_proIwahori_iff_of_isometry (v_locMap_eq_of_surjective _ hs τ.surjective)
  -- The component at `u` of the base change of `g` is the component at `w`, mapped into the
  -- completion at `u`.
  have h_baseChange :
      (Subgroup.comap ρ proIwahori).comap baseChangeGf = Subgroup.comap r proIwahori := by
    ext g
    simp only [Subgroup.mem_comap, hρ_baseChange]
    exact map_mem_proIwahori_iff_of_isEquiv (isEquiv_comap_locMap (algebraMap E E') rfl)
  -- `ρ` is continuous, as renumbering the entries of a matrix is, and `proIwahori` is open
  have h_open : (Subgroup.comap ρ proIwahori).IsOpen := by
    have h_reindex : Continuous fun M : Matrix m m (LocField u) ↦ M.submatrix ε.symm ε.symm := by
      fun_prop
    exact isOpen_proIwahori.preimage (.comp (.units_map _ h_reindex) (by fun_prop))
  have h_le_level : Subgroup.comap ρ proIwahori ≤ localLevel m (placesAbove E' {u.below E}) := by
    rintro g ⟨hg_int, -⟩
    simpa [h_level, mem_intGL, reindex_equiv ε.symm, ρ] using hg_int
  -- Both indicators are bi-invariant, as double cosets of the open group `proIwahori`.
  exact ⟨τ, hτ, r, ρ, ⟨fun t ↦ ⟨isHeckeFunction_doubleCoset isOpen_proIwahori _,
      isHeckeFunction_doubleCoset isOpen_proIwahori _⟩, hr_retr, hρ_retr, Set.finite_singleton _,
      h_stable⟩,
    h_baseChange, h_open, Subgroup.comap ρ proIwahori, ⟨le_rfl, h_le_level⟩,
    cocyclesSplit_comap_proIwahori hu hτ hs hρ_retr hρ_gal, fun t ht ↦
      isMatchingPairAbove_proIwahori h_unique hμ_loc hw hτ hs hρ_gal (fun _ ↦ rfl) hρ_charpoly
        hρ_baseChange ht⟩

/-- The operators of dominant double cosets multiply like the torus. Let `ρ` be a smooth
representation of `GL_N` over the completion of a number field at `o`, and `s`, `t` elements of
`New.dominantTorus`. On vectors `x` fixed by `New.proIwahori`, applying the operator of the double
coset of `t` and then that of `s` is applying that of `s * t`. -/
private lemma heckeFun_iwahoriDoubleCoset_mul {F : Type} [Field F] [NumberField F] {o : FinPlace F}
    {N : ℕ} (ρ : Rep ℂ (GL (Fin N) (LocField o))) [IsSmoothRep ρ.ρ] {s t : Fin N → (LocField o)ˣ}
    (hs : s ∈ dominantTorus) (ht : t ∈ dominantTorus) (x : ρ)
    (hx : x ∈ levelSpace ρ.ρ proIwahori) :
    heckeFun ρ.ρ proIwahori ((iwahoriDoubleCoset s).indicator 1)
        (heckeFun ρ.ρ proIwahori ((iwahoriDoubleCoset t).indicator 1) x) =
      heckeFun ρ.ρ proIwahori ((iwahoriDoubleCoset (s * t)).indicator 1) x := by
  -- Each operator is `iwahoriDegree` times the mean of a translate; the means multiply by
  -- `compactMean_diagGL_compactMean_diagGL`, and the degrees multiply.
  have h_deg : iwahoriDegree t * iwahoriDegree s = iwahoriDegree (s * t) := by
    simp [prod_mul_distrib, div_mul_div_comm, mul_comm]
  simp only [hs, ht, hx, mul_mem, heckeFun_iwahoriDoubleCoset_eq_iwahoriDegree_smul, map_smul,
    compactMean_mem_levelSpace, compactMean_diagGL_compactMean_diagGL, smul_smul, h_deg]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
attribute [-simp] mem_levelSpace exists_const MonoidHom.coe_comp in
/-- Base change keeps an Iwahori eigencharacter. Let `E'/E` be a step with `E'` containing a
primitive `5040`-th root of unity (`HasPrimitiveRoot5040`). Let `w = u.below E` be split (`hw`) with
`μ` trivial at `w` (`hμ_loc`), and let `u` be the only place above `w` (`h_unique`), split (`hu`).
If `f`, an element of `localFormRep (stdSpace E m) κ hw` (the forms of weight `κ`, as a
representation of `GL` at `w`), is an Iwahori eigenvector at `w` (`New.IsIwahoriEigen`) with
character `torusChar θ`, some form `f'` over `E'` is (a) an eigenform, (b) a weak base change of `f`
off `w` and its conjugate, and (c) an Iwahori eigenvector at `u` with character
`torusChar (θ i ∘ N)`, `N = localNorm E u`. -/
lemma exists_baseChange_isIwahoriEigen
    (h_unique : ∀ u' : FinPlace E', FinPlace.below E u' = u.below E ↔ u' = u)
    (hμ_loc : ∀ x : (LocField (FinPlace.below E u))ˣ, μ (locIdele (u.below E) x) = 1)
    [HasPrimitiveRoot5040 E'] {κ : Weight E} {f : localFormRep (stdSpace E m) κ hw}
    {θ : Fin (Fintype.card m) → (LocField (u.below E))ˣ →* ℂˣ}
    (hf : IsIwahoriEigen (localFormRep (stdSpace E m) κ hw) (torusChar θ) f) :
    ∃ f' : (stdSpace E' m).forms κ.baseChange, ∃ P : FinPlace E' → ℂ[X],
      -- (a) `f'` is an eigenform
      IsEigenform f'.val P ∧
      -- (b) it is a weak base change of `f` away from the place below `u`
      IsWeakBaseChange μ {u.below E} f.val f'.val ∧
      -- (c) at `u` its characters are those of `f` composed with the local norm
      IsIwahoriEigen (localFormRep (stdSpace E' m) κ.baseChange hu)
        (torusChar fun i : Fin (Fintype.card m) ↦ (θ i).comp (localNorm E u)) f' := by
  -- Apply `exists_isWeakBaseChange_of_matching` to the double cosets of
  -- `isLocalMatching_proIwahori`. For dominant `t`, the operator of the double coset of `t` is
  -- `iwahoriDegree t` times the operator of `IsIwahoriEigen`
  -- (`heckeFun_iwahoriDoubleCoset_eq_iwahoriDegree_smul`), and the local norm keeps absolute
  -- values. Any strictly dominant `t₀` serves as the distinguished index.
  obtain ⟨hf_ne, hf_level, hf_eigen⟩ := hf
  obtain ⟨t₀, ht₀, -⟩ :=
    exists_iwahoriHeckeHom_injective (localFormRep (stdSpace E' m) κ.baseChange hu)
      (v_uniformizer u)
  have h_dom (n : ℕ) (t : Fin n → (LocField u)ˣ) :
      localNorm E u ∘ t ∈ dominantTorus ↔ t ∈ dominantTorus := by
    simp [dominantTorus, Monotone, ← toNormedField.norm_le_iff]
  refine (exists_isWeakBaseChange_of_matching f
    (isLocalMatching_proIwahori (hw := hw) hu h_unique hμ_loc) id
    (fun a ↦ iwahoriDegree a.val * torusChar θ (localNorm E u ∘ a)) ⟨t₀, ht₀.monotone⟩ ht₀
    ?comm ?stable ?trace).imp ?eigen
  case comm =>
    -- the operators of dominant elements multiply like the torus, which is commutative
    intro s t
    have hNs : localNorm E u ∘ s.val ∈ dominantTorus := (h_dom _ s.val).mpr s.prop
    have hNt : localNorm E u ∘ t.val ∈ dominantTorus := (h_dom _ t.val).mpr t.prop
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · rw [heckeFun_iwahoriDoubleCoset_mul (localFormRep (stdSpace E m) κ hw) hNs hNt x hx,
        heckeFun_iwahoriDoubleCoset_mul (localFormRep (stdSpace E m) κ hw) hNt hNs x hx, mul_comm]
    · rw [heckeFun_iwahoriDoubleCoset_mul (localFormRep (stdSpace E' m) κ.baseChange hu) s.prop
          t.prop x hx,
        heckeFun_iwahoriDoubleCoset_mul (localFormRep (stdSpace E' m) κ.baseChange hu) t.prop
          s.prop x hx, mul_comm]
  case stable =>
    -- dominant times strictly dominant is strictly dominant
    intro s t ht
    refine ⟨s * t, ?_, fun x hx ↦ ?_,
      heckeFun_iwahoriDoubleCoset_mul (localFormRep (stdSpace E' m) κ.baseChange hu) s.prop t.prop⟩
    · simpa [Pi.mul_def] using s.prop.mul_strictMono ht (by simp [pos_iff_ne_zero]) (by simp)
    · rw [id_eq, heckeFun_iwahoriDoubleCoset_mul (localFormRep (stdSpace E m) κ hw)
        ((h_dom _ s.val).mpr s.prop) ((h_dom _ t.val).mpr t.prop) x hx]
      simp [Function.comp_def, Pi.mul_def]
  case trace =>
    -- The space contains `f ≠ 0`, and the operator has one non-zero generalised eigenvalue on it.
    intro W hfW _ h_maps
    refine trace_restrict_ne_zero (c := iwahoriDegree t₀ * (torusChar θ (localNorm E u ∘ t₀) : ℂ))
      (by simp [prod_ne_zero_iff]) (fun h0 ↦ ?_) (fun x hx ↦ ?_) h_maps
    · -- `f` lies in the space, being fixed by `proIwahori` and an eigenvector of each operator;
      -- so the space is not `⊥`, as `f ≠ 0`
      apply hf_ne
      rw [← Submodule.mem_bot ℂ, ← h0, Submodule.mem_inf, mem_heckeGenEigenspace]
      refine ⟨⟨hf_level, fun a ↦ ?_⟩, hfW⟩
      rw [Module.End.mem_maxGenEigenspace]
      exact ⟨1, by simp [a.prop, h_dom, hf_level, hf_eigen, mul_smul]⟩
    · exact (mem_heckeGenEigenspace.mp (Submodule.mem_inf.mp hx).1).2 _
  case eigen =>
    -- Cancel `iwahoriDegree t ≠ 0`; the character `torusChar θ (localNorm E u ∘ ·)` is that of the
    -- characters `(θ i).comp (localNorm E u)`.
    rintro f' ⟨P, ⟨hf'_ne, hf'_poly⟩, h_same, ⟨h_fixed, h_val⟩, -⟩
    refine ⟨P, ⟨hf'_ne, hf'_poly⟩, h_same, ne_of_apply_ne Subtype.val hf'_ne, h_fixed, ?_⟩
    simpa [h_fixed, mul_smul, prod_eq_zero_iff, torusChar, Pi.monoidHomMulEquiv,
      MonoidHom.comp_apply, coe_normAbsChar_locField] using h_val

end BaseChangeEigenchar

end New
end
end

/-!
# Local-global compatibility at split places for Iwahori eigencharacters and parahoric types

Let `r` be an `ℓ`-adic Galois representation attached to an eigenform on a definite unitary group
over a CM field `E`, and let `w` be a split place. Level information on the form at `w` gives
polynomials that kill geometric Frobenius and inertia elements under `r`, in the sense of
`New.GaloisRep.PolyKillsAt`. At pro-`p` Iwahori level, with eigencharacter `New.torusChar ξ`, the
characters `ξ i` are tamely ramified and, when sorted, give the roots of such polynomials. For `w`
not above `ℓ`, when a parahoric subgroup acts by scalars there are analogous polynomials for the
Frobenius and inertia matrices. For the stabiliser in `GL_N(𝒪_w)` of a line modulo `w`, the Hecke
operator of `diag (ϖ, 1, …, 1)` acts like Frobenius on the image of `T - 1`, for the matrix `T` of
an inertia element, in the sense of an identity between traces. Here `p` is the residue
characteristic of `w`.

## Main definitions and results

* `New.GaloisRep.Attached.local_global_of_eigencharacter`: the main result, for `ξ i` sorted by size
  at a uniformiser.
* `New.Patching.IsParahoricCompatible`: commuting matrices `F`, `T` are killed by polynomials read
  off given scalars and an exponent that is not zero on a given vector.
* `New.Patching.isParahoricCompatible_galRep`: the Frobenius and inertia matrices have this property
  for a non-zero pro-`p` Iwahori fixed form on which a parahoric subgroup acts by scalars that tell
  its blocks apart.
* `New.Patching.hecke_eq_frob_on_parahoricEigenspace`: for the stabiliser in `GL_N(𝒪_w)` of a line
  modulo `w`, acting by a scalar character that is not of order dividing `N !` at the unit, the
  Hecke operator of `diag (ϖ, 1, …, 1)` acts like Frobenius on the image of `T - 1`, with `T` the
  inertia matrix, in the sense of an identity between traces.

Notions from other files:
* `New.GaloisRep.PolyKillsAt r A s P`: `P (r s) = 0` if `ℓ` is a unit at `A`; above `ℓ`, for every
  Weil pair `(s, k)`, `r` is potentially crystalline and `P` kills `New.Period.linearFrob`.
* `New.IsFrob A q σ`: `σ` stabilises `A` and acts as `x ↦ x ^ q` on its residue field.
* `New.Patching.localFormRep V κ hw`: the representation of `GL_N(E_w)`, with `N` the cardinality
  of `n`, on the forms of weight `κ` on `V` at the split place `w`.
* `New.IsIwahoriEigen ρ ξ x`: `x ≠ 0` is fixed by the pro-`p` Iwahori subgroup, and
  `U_t x = ξ t • x` for dominant diagonal `t`.
* `New.torusChar θ`: the character `t ↦ ∏ i, θ i (t i) * |t i| ^ (N - 1 - i)` of the diagonal torus
  of `GL_N`.

## Relation to the literature

Known; see `Lib.GaloisRep.LocalGlobal.LabelCompatibility` for sources.
-/

@[expose] public section

/-!
## Compatibility for a sorted Iwahori eigencharacter

Let `f` be an eigenform on the standard definite unitary group over the CM field `E`, `r` an
`ℓ`-adic Galois representation attached to it (`New.GaloisRep.Attached`), `w` a split place and `A`
a place of `Ω` above `w`. Suppose that at `w` the form is an eigenvector at the pro-`p` Iwahori
level (`New.IsIwahoriEigen`) for the torus character `New.torusChar ξ`, that is
`t ↦ ∏ i, ξ i (t i) * |t i| ^ (N - 1 - i)` with `N` the cardinality of `n`.
-/

namespace New

open Polynomial Valued Subgroup WithZero QuotientGroup Period Patching Fintype ComplexOrder Ideal
  MonoidHom Set Finite Algebra QZChar Int

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E n : Type} [Field E] [CMType E]
  {w : FinPlace E} [Fintype n] [DecidableEq n]
  {κ : Weight E} {P : FinPlace E → ℂ[X]} {ξ : Fin (card n) → (LocField w)ˣ →* ℂˣ}
  {hw : Star.star w ≠ w} {f : (stdSpace E n).forms κ}

/-- Let `f` be a pro-`p` Iwahori eigenvector at `w` with eigencharacter `torusChar ξ`. Then the
absolute value and the characters `ξ i` are trivial on the `y` congruent to `1` modulo `w`. -/
lemma IsIwahoriEigen.apply_eq_one_of_principal_unit
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    {y : (LocField w)ˣ} (hy : v (y.val - 1) < 1) :
    normAbsChar.prod (MonoidHom.pi ξ) y = 1 := by
  obtain ⟨hf_ne, hf_fixed, hU⟩ := hf_iwahori
  have hy_val : v y.val = 1 := by simpa using v.map_one_add_of_lt hy
  -- The diagonal matrix `t` with `y` at `i` is dominant and lies in the pro-`p` Iwahori subgroup,
  -- so `U_t` is the identity on `f` and its eigenvalue is `1`.
  have h_torus_one (i : Fin (card n)) : (torusChar ξ (Pi.mulSingle i y)).val = 1 := by
    have h_dom : Pi.mulSingle i y ∈ dominantTorus := by
      simp [dominantTorus, Monotone, apply_ite, hy_val, Pi.mulSingle_apply]
    have h_mem : diagGL (Pi.mulSingle i y) ∈ proIwahori :=
      diagGL_mem_proIwahori.2 fun j ↦ by rcases eq_or_ne j i with rfl | hj <;> simp [*]
    have h_smul : (torusChar ξ (Pi.mulSingle i y)).val • f = f := by
      rw [← hU _ h_dom, compactMean_apply h_mem, compactMean_eq_self _ hf_fixed]
    exact smul_left_injective ℂ hf_ne (h_smul.trans (one_smul ℂ f).symm)
  simpa [normAbsChar, hy_val, funext_iff] using h_torus_one

/-- Let `f` be a pro-`p` Iwahori eigenvector at `w` with eigencharacter `torusChar ξ`. Then the
absolute value and the characters `ξ i` kill the `(q - 1)`-th power of every local unit, where
`q = w.q` is the size of the residue field. -/
lemma IsIwahoriEigen.char_pow_q_sub_one_eq_one
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    (y : (LocField w)ˣ) (hy : v y.val = 1) :
    normAbsChar.prod (MonoidHom.pi ξ) (y ^ (w.q - 1)) = 1 := by
  -- Fermat's little theorem in the residue field: `y ^ (w.q - 1)` is `1` modulo `w`,
  -- so `IsIwahoriEigen.apply_eq_one_of_principal_unit` applies to it.
  let a : (ResField w)ˣ :=
    .mk0 ⟦⟨y.val, hy.le⟩⟧ (mt residue_eq_iff_valuation_sub_lt_one.1 (by simp [hy]))
  have h_pow : (a : ResField w) ^ (w.q - 1) = 1 := by
    rw [← card_ResField]
    exact algebraMap_pow_card_pred_eq_one a
  exact hf_iwahori.apply_eq_one_of_principal_unit (residue_eq_iff_valuation_sub_lt_one.1 h_pow)

omit [PadicIso ℓ] [CMType E] in
/-- Let `s`, `φ` lie in the decomposition group of a place `A` above `w`, with `φ` a Frobenius. If
`∏ (X - a i)` kills `φ⁻¹`, with `a i ≠ 0`, and `∏ (X - α i * a i ^ m)` kills `s * φ⁻¹ ^ m` for all
`m > 0`, then `∏ (X - α i)` kills `s`. Here "kills" is `New.GaloisRep.PolyKillsAt` for `r`:
vanishing at the matrix away from `ℓ`, at the linear Frobenius above `ℓ`. -/
lemma GaloisRep.PolyKillsAt.of_mul_frob_pow [EmbeddedNumberField E] {r : GalRep ℓ E n}
    {A : ClosurePlace} {N : ℕ} {α a : Fin N → PadicAlgCl ℓ}
    {s φ : decompGroup Gal(Ω/E) A} (hA : IsPlaceOver A w) (hφ : IsFrob A w.q φ.val)
    (ha : ∀ i : Fin N, a i ≠ 0) (hφa : PolyKillsAt r A (φ⁻¹).val (∏ i : Fin N, (X - C (a i))))
    (hpow : ∀ m > (0 : ℕ),
      PolyKillsAt r A (s * φ⁻¹ ^ m).val (∏ i : Fin N, (X - C (α i * a i ^ m)))) :
    PolyKillsAt r A s.val (∏ i : Fin N, (X - C (α i))) := by
  -- Both clauses are `eval₂_prod_eq_zero_of_mul_pow`, the same statement for two elements of a
  -- ring: for the matrices `r s` and `r φ⁻¹` away from `ℓ`, and for `linearFrob` at `s` and at
  -- `φ⁻¹` above `ℓ`.
  refine ⟨fun hℓ ↦ ?_, ?_⟩
  · refine eval₂_prod_eq_zero_of_mul_pow (Algebra.commutes · (r s).val)
      (Algebra.commutes · (r φ⁻¹.val).val) (hφa.1 hℓ) ha fun m hm ↦ ?_
    change aeval ((r s).val * (r φ⁻¹.val).val ^ m) (∏ i : Fin N, (X - C (α i * a i ^ m))) = 0
    simpa using (hpow m hm).1 hℓ
  intro L _ d hs
  -- Above `ℓ` we have `w.q = ℓ ^ deg`, and `φ⁻¹` is a Weil element of degree `deg`.
  have hℓ_lt : A.valuation ℓ < 1 := by
    rw [show A = (intQpBar ℓ).comap L.e from L.inducesPlace.1.1.symm]
    exact valuation_comap_intQpBar_lt_one L.e
  obtain ⟨deg, hq, -⟩ := w.exists_q_eq_pow (hA.valuation_natCast_lt_one_iff.mp hℓ_lt)
  have hφW : IsWeilPair (L.toGp φ⁻¹) deg := by simpa [IsWeilPair, L.isFrob_iff, ← hq]
  obtain ⟨hpcr, hφ_kill⟩ := hφa.2 hφW
  refine ⟨hpcr, eval₂_prod_eq_zero_of_mul_pow (commute_coeffEnd_linearFrob hpcr hs)
    (commute_coeffEnd_linearFrob hpcr hφW) hφ_kill ha fun m hm ↦ ?_⟩
  -- `linearFrob` is multiplicative on Weil pairs.
  rw [← linearFrob_pow hpcr hφW, ← linearFrob_mul hpcr hs (hφW.pow m)]
  exact ((hpow m hm).2 (hs.mul (hφW.pow m))).2

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let the eigenform `f` for the system `P` of Hecke polynomials be a pro-`p` Iwahori eigenvector
at `w` with eigencharacter `torusChar ξ`. If the `ξ i` are unramified and `‖ξ i ϖ‖` is antitone in
`i` for a uniformiser `ϖ`, then some eigenform for the same system `P` is spherical at `w` with
Hecke roots `ξ i ϖ` (`New.HasHeckePolyAt`). -/
lemma IsIwahoriEigen.exists_hasHeckePolyAt
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E] {ϖ : (LocField w)ˣ} (he : IsEigenform f.val P)
    (hϖ : v ϖ.val = WithZero.exp (-1))
    (hunr : ∀ y : (LocField w)ˣ, v y.val = 1 → ∀ i : Fin (card n), (ξ i y).val = 1)
    (hξ_antitone : Antitone fun i : Fin (card n) ↦ ‖(ξ i ϖ).val‖) :
    ∃ g : (stdSpace E n).forms κ,
      IsEigenform g.val P ∧
      HasHeckePolyAt g.val w hw (∏ i : Fin (card n), (X - C (ξ i ϖ).val)) := by
  -- `f` gives an exponent `(torusChar ξ, B u)` with `u` in the span of the translates of `f`, for
  -- an invariant scalar product `B`. The form is the mean `g` of `u` over `K = GL_N(𝒪_w)`: it is
  -- not zero by `IsExponent.eq_zero_of_eq_zero_on_spherical`, and Satake's formula
  -- `IsExponent.apply_partialHecke` gives its Hecke eigenvalues.
  let ρ : Rep.{0, 0, 0} ℂ (GL (Fin (card n)) (LocField w)) := localFormRep (stdSpace E n) κ hw
  obtain ⟨B, hB⟩ : ∃ B : ρ →ₗ⋆[ℂ] ρ →ₗ[ℂ] ℂ, IsUnitary ρ.ρ B := ⟨_, isUnitary_localFormRep⟩
  obtain ⟨u, hu_mem, hu_ne, hexp⟩ := hf_iwahori.exists_isExponent hB self_mem_cyclicSpan
  let K : Subgroup (GL (Fin (card n)) (LocField w)) := localIntGL (Fin (card n)) w
  let S : Submodule ℂ ρ := levelSpace ρ.ρ K
  let g : (stdSpace E n).forms κ := compactMean ρ.ρ K u
  have hg : g ∈ S := compactMean_mem_levelSpace u
  have B_g (y : ρ) (hy : y ∈ S) : B g y = B u y := by
    rw [hB.compactMean_adjoint, compactMean_eq_self y hy]
  have hg_ne : g ≠ 0 := fun hzero ↦ hu_ne <|
    hexp.eq_zero_of_eq_zero_on_spherical hϖ hunr hξ_antitone fun y hy ↦ by
      simp [← B_g y hy, hzero]
  -- The Hecke eigenvalues are `e_j (ξ i ϖ) / q ^ (j (j - 1) / 2)`, with `e_j` elementary symmetric.
  let roots : Multiset ℂ := List.ofFn fun i : Fin (card n) ↦ (ξ i ϖ).val
  let t (j : ℕ) : ℂ := roots.esymm j / w.q ^ j.choose 2
  refine ⟨g, he.of_mem_cyclicSpan (by simpa using compactMean_mem_cyclicSpan 1 hu_mem) hg_ne,
    hasHeckePolyAt_iff_localFormRep.mpr ⟨hg, t, ?_, fun j ↦ ?_⟩⟩
  · -- Vieta's formula
    rw [show ∏ i : Fin (card n), (X - C (ξ i ϖ).val) = (roots.map (X - C ·)).prod by
      simp [roots, List.map_ofFn, Fin.prod_ofFn, Function.comp_def],
      Multiset.prod_X_sub_X_eq_sum_esymm]
    simp [roots, t, heckePoly, mul_div_cancel₀, mul_assoc, (zero_lt_one.trans w.one_lt_q).ne']
  -- Let `T` be the `j`-th Hecke operator and `T'` its adjoint, which commutes with `T` on spherical
  -- vectors. Satake's formula says that `B g (T y) = t j * B g y` for spherical `y`.
  let T : Module.End ℂ ρ := heckeGL ρ.ρ j
  let c : GL (Fin (card n)) (LocField w) → ℂ := (basicDoubleCoset (Fin (card n)) w j).indicator 1
  let T' : Module.End ℂ ρ := heckeFun ρ.ρ K fun a ↦ starRingEnd ℂ (c a⁻¹)
  have hbi : IsHeckeFunction K c := isHeckeFunction_basicDoubleCoset j
  have hbi' : IsHeckeFunction K _ := (hbi.heckeFun_adjoint B hg hB.map_map_eq hg).1
  have adjoint (y : ρ) (hy : y ∈ S) : B (T g) y = B g (T' y) :=
    (hbi.heckeFun_adjoint B hg hB.map_map_eq hy).2
  have satake (y : ρ) (hy : y ∈ S) : B g (T y) = t j * B g y := by
    rw [B_g (T y) (hbi.heckeFun_mem hy), B_g y hy,
      show T = partialHecke ρ.ρ 0 j from partialHecke_zero_eq_heckeGL.symm]
    exact hexp.apply_partialHecke hϖ hy bot_le j
  have normal : B (T g) (T g) = t j * B (T g) g := by
    rw [adjoint (T g) (hbi.heckeFun_mem hg), adjoint _ hg, ← satake (T' g) (hbi'.heckeFun_mem hg)]
    exact congrArg _ (hbi.heckeFun_comm hbi' hg).symm
  -- Hence `T g - t j • g` is orthogonal to `T g` and to `g`, so to itself.
  by_contra hne
  refine (hB.pos _ (sub_ne_zero.mpr hne)).ne' ?_
  change B (T g - t j • g) (T g - t j • g) = 0
  simp [normal, satake g hg]

/-- Let `f` be a pro-`p` Iwahori eigenvector at `w` with eigencharacter `torusChar ξ`. If
`‖ξ i (uniformizer w)‖` is antitone in `i`, so is `‖ξ i x‖` for `x` of order `k ≥ 0`. -/
lemma IsIwahoriEigen.antitone_norm
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E]
    (hξ_antitone : Antitone fun i : Fin (card n) ↦ ‖(ξ i (uniformizer w)).val‖)
    {x : (LocField w)ˣ} {k : ℕ} (hx_val : v x.val = WithZero.exp (-k : ℤ)) :
    Antitone fun i : Fin (card n) ↦ ‖(ξ i x).val‖ := by
  intro i j hij
  -- `x / uniformizer w ^ k` is a unit, so `ξ i` kills its `(q - 1)`-th power.
  have h_unit : v (x / uniformizer w ^ k).val = 1 := by simp [hx_val]
  have h_killed : MonoidHom.pi ξ ((x / uniformizer w ^ k) ^ (w.q - 1)) = 1 :=
    congrArg Prod.snd (hf_iwahori.char_pow_q_sub_one_eq_one _ h_unit)
  have pow_eq : ∀ i : Fin (card n),
      (ξ i x).val ^ (w.q - 1) = (ξ i (uniformizer w)).val ^ (k * (w.q - 1)) := by
    simpa [div_pow, div_eq_iff, ← pow_mul, funext_iff, Units.ext_iff] using h_killed
  refine le_of_pow_le_pow_left₀ w.q_sub_one_pos.ne' (norm_nonneg _) ?_
  simpa [← norm_pow, pow_eq] using pow_le_pow_left₀ (norm_nonneg _) (hξ_antitone hij) _

/-- Let `f` be a pro-`p` Iwahori eigenvector at `w` with eigencharacter `torusChar ξ`. If `x` has
order `k > 0`, the `y` with `(|y|, ξ y)` a power of `(|x|, ξ x)` form a subgroup of finite index. -/
lemma IsIwahoriEigen.finiteIndex_comap_zpowers
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E] {x : (LocField w)ˣ} {k : ℕ}
    (hx_val : v x.val = WithZero.exp (-k : ℤ)) (hk : 0 < k) :
    ((zpowers (normAbsChar.prod (MonoidHom.pi ξ) x)).comap
      (normAbsChar.prod (MonoidHom.pi ξ))).FiniteIndex := by
  -- The subgroup contains the `k * (q - 1)`-th powers, which have finite index.
  have : NeZero (k * (w.q - 1)) := ⟨(mul_pos hk w.q_sub_one_pos).ne'⟩
  have : (powMonoidHom (α := (LocField w)ˣ) (k * (w.q - 1))).range.FiniteIndex :=
    ⟨(index_pow_local_le _ w).1⟩
  refine finiteIndex_of_le (H := (powMonoidHom (k * (w.q - 1))).range)
    (range_subset_iff.mpr fun y ↦ ⟨-(v y.val).log * (w.q - 1), ?_⟩)
  -- `x ^ (v y).log * y ^ k` is a unit, so its `(q - 1)`-th power is killed.
  have hunit : v (x ^ (v y.val).log * y ^ k).val = 1 := by
    rw [← exp_log (x := v (x ^ (v y.val).log * y ^ k).val) (v.ne_zero_iff.2 (Units.ne_zero _))]
    simp [hx_val, mul_comm]
  simpa [mul_zpow, zpow_mul, ← zpow_natCast, inv_eq_iff_mul_eq_one] using
    hf_iwahori.char_pow_q_sub_one_eq_one _ hunit

/-- Let `f` be a pro-`p` Iwahori eigenvector at `w` with eigencharacter `torusChar ξ`, and let `A`
be a place above `w`. If `y / x` is a unit and `x`, `y` have the same local Artin symbol at `A`,
then the absolute value and the `ξ i` agree at `x` and `y`. -/
lemma IsIwahoriEigen.eq_of_localArtin_eq
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E] {A : ClosurePlace} (hA : IsPlaceOver A w) {x y : (LocField w)ˣ}
    (hunit : v (y / x).val = 1) (hart : localArtin Gal(Ω/E) A w y = localArtin Gal(Ω/E) A w x) :
    normAbsChar.prod (MonoidHom.pi ξ) y = normAbsChar.prod (MonoidHom.pi ξ) x := by
  -- Take a uniformiser `π` in `E` and `z` with `z ^ (q - 1) = π`. The symbol of the unit `y / x` is
  -- trivial, so by the tame symbol `y / x` is congruent to `z / z = 1`.
  obtain ⟨π, hπ, -⟩ := hA.exists_uniformizer Gal(Ω/E)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω π) w.q_sub_one_pos
  have hz_ne : z ≠ 0 := ne_zero_pow w.q_sub_one_pos.ne' (by simp [hz])
  have h_symb : localArtin Gal(Ω/E) A w (y / x) = 1 := (div_mem_ker_iff _).mpr hart
  have h_one : v ((y / x).val - 1) < 1 := by
    simpa [hz_ne] using
      hA.valuation_sub_lt_one_iff_of_localArtin_eq (s := 1) (x := 1) (hA.isUniformizer_iff.mpr hπ)
        hunit h_symb hz
  exact (div_mem_ker_iff _).mp (hf_iwahori.apply_eq_one_of_principal_unit h_one)

omit [DecidableEq n] in
/-- Let `ξ i` be characters of the completion at `w` and let `x` have order `k`. If `(|y|, ξ y)` is
a power of `(|x|, ξ x)` for every `y`, then `x` is a uniformiser and the `ξ i` are unramified. -/
lemma IsIwahoriEigen.order_eq_one_and_unramified [EmbeddedNumberField E] {x : (LocField w)ˣ}
    {k : ℕ} (hx_val : v x.val = WithZero.exp (-k : ℤ))
    (hgen : ∀ y : (LocField w)ˣ,
      normAbsChar.prod (MonoidHom.pi ξ) y ∈ zpowers (normAbsChar.prod (MonoidHom.pi ξ) x)) :
    k = 1 ∧
    ∀ y : (LocField w)ˣ, v y.val = 1 → ∀ i : Fin (card n), (ξ i y).val = 1 := by
  -- Compare absolute values through the injectivity of `a ↦ q ^ a`.
  have hq_inj {a b : ℤ} : (w.q : ℂ) ^ a = w.q ^ b ↔ a = b :=
    (zpow_right_strictMono₀ (by simp : (1 : ℂ) < w.q)).injective.eq_iff
  have hpow (y : (LocField w)ˣ) :
      ∃ a : ℤ, -(k * a) = (v y.val).log ∧ ∀ i : Fin (card n), (ξ i x).val ^ a = ξ i y := by
    -- `zpow_neg` would move the sign out of the exponent that `hq_inj` compares.
    simpa [hx_val, -zpow_neg, hq_inj, mem_zpowers_iff, ← zpow_mul, Units.ext_iff,
      coe_normAbsChar_locField, norm_locField_eq_q_zpow, funext_iff] using hgen y
  obtain rfl : k = 1 := by
    obtain ⟨a, ha, -⟩ := hpow (uniformizer w)
    exact_mod_cast eq_one_of_dvd_one k.cast_nonneg ⟨a, by simpa [eq_comm] using ha⟩
  refine ⟨rfl, fun y hy i ↦ ?_⟩
  obtain ⟨a, ha, hξa⟩ := hpow y
  obtain rfl : a = 0 := by simpa [hy] using ha
  simp [← hξa]

variable [Nonempty n] [WeilData E]

/-- If a prime `p` divides the finite index of a subgroup `D` of a commutative group `G`, there is a
non-trivial character `χ` of `G` with values in `ℚ/ℤ` that is killed by `p` and trivial on `D`. -/
lemma exists_char_trivial_of_prime_dvd_index {G : Type} [CommGroup G] (D : Subgroup G)
    [D.FiniteIndex] {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ D.index) :
    ∃ (χ : G →* Multiplicative QZ) (x₀ : G),
      χ x₀ ≠ 1 ∧ (∀ y : G, χ y ^ p = 1) ∧ ∀ y ∈ D, χ y = 1 := by
  -- The dual of `G ⧸ D` has as many elements as `G ⧸ D`, so it has an element `ψ` of order `p`.
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ψ, hψ⟩ :=
    exists_prime_addOrderOf_dvd_card' (G := Additive (G ⧸ D) →+ QZ) p (by rwa [card_hom_QZ])
  obtain ⟨hψp, ⟨x₀⟩, hψ₀⟩ : (∀ a : G ⧸ D, p • ψ (Additive.ofMul a) = 0) ∧
      ∃ a : G ⧸ D, ψ (Additive.ofMul a) ≠ 0 := by
    simpa [addOrderOf_eq_prime_iff, DFunLike.ext_iff] using hψ
  refine ⟨ψ.toMultiplicativeRight.comp (mk' D), x₀, hψ₀, fun y ↦ hψp y, fun y hy ↦ ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (eq_one_iff y).mpr hy, map_one]

/-- If a character `χ` of `G` is trivial on the subgroup `D` of finite index and on the image of
`N : G' →* G` but not at `x₀`, then the preimage of `D` under `N` has smaller index than `D`. -/
lemma index_comap_lt_of_char_ne_one {G G' M : Type*} [CommGroup G] [Group G'] [Group M]
    {D : Subgroup G} [D.FiniteIndex] {N : G' →* G} {χ : G →* M} {x₀ : G} (hχ₀ : χ x₀ ≠ 1)
    (hχD : ∀ y ∈ D, χ y = 1) (hχN : ∀ z : G', χ (N z) = 1) :
    (D.comap N).index < D.index := by
  -- The class of `x₀` modulo `D` is not in the image of `G'`.
  rw [← ker_mk' D, comap_ker, index_ker, ker_mk']
  refine card_subtype_lt (x := (x₀ : G ⧸ D)) fun ⟨z, hz⟩ ↦ hχ₀ ?_
  have h_mem : (N z)⁻¹ * x₀ ∈ D := QuotientGroup.eq.1 hz
  simpa [hχN] using hχD _ h_mem

/-- The unramified case of `New.GaloisRep.Attached.local_global_of_eigencharacter`. Let `r` be
attached to the Hecke polynomials `P` of the eigenform `f` on the standard space over the CM field
`E`, where `f` is a pro-`p` Iwahori eigenvector at the split place `w` for `torusChar ξ`, each `ξ i`
is trivial on units, and `‖ξ i ϖ‖` is antitone in `i` for a uniformiser `ϖ`. If `A` lies above `w`
and `s⁻¹` is a Frobenius at `A`, then `r` is of finite type at `A` (trivial on inertia near `1` if
`ℓ` is a unit at `A`, and potentially crystalline), its Hodge–Tate jumps at `A` are
`jumps κ (card n)`, and `∏ i, (X - ιℓ (ξ i ϖ))` kills `r(s)` at `A` in the sense of
`New.GaloisRep.PolyKillsAt`. -/
lemma GaloisRep.Attached.local_global_of_eigencharacter_of_unramified
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E] {r : GalRep ℓ E n} {A : ClosurePlace} (he : IsEigenform f.val P)
    (hr : Attached P r) (hA : IsPlaceOver A w) {s : Gal(Ω/E)} (hs_frob : IsFrob A w.q s⁻¹)
    {ϖ : (LocField w)ˣ} (hϖ : v ϖ.val = WithZero.exp (-1))
    (hunr : ∀ y : (LocField w)ˣ, v y.val = 1 → ∀ i : Fin (card n), (ξ i y).val = 1)
    (hξ_antitone : Antitone fun i : Fin (card n) ↦ ‖(ξ i ϖ).val‖) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (card n)) ∧
    PolyKillsAt r A s (∏ i : Fin (card n), (X - C (ιℓ (ξ i ϖ)))) := by
  -- By `sphericalCompat_std` at a spherical form `g` for `P`, `r` is unramified or crystalline at
  -- `A`, has the jumps of `κ`, and the Hecke polynomial kills `s`.
  obtain ⟨g, hg, hgw⟩ : ∃ g : (stdSpace E n).forms κ, IsEigenform g.val P ∧
      HasHeckePolyAt g.val w hw (∏ i : Fin (card n), (X - C (ξ i ϖ).val)) :=
    hf_iwahori.exists_hasHeckePolyAt he hϖ hunr hξ_antitone
  obtain ⟨hgood, hjump, hpoly⟩ : IsCompatibleAt g.val (card n) w r A :=
    (sphericalCompat_std w g.property hg).2 hr hgw.1 A hA
  refine ⟨(isGoodAt_iff.1 hgood).1, hjump, ?_⟩
  simpa [Polynomial.map_prod] using hpoly hw _ hgw s hs_frob

/-- The case `k > 0` of `New.GaloisRep.Attached.local_global_of_eigencharacter`, with the `ξ i`
sorted at `x`. Let `r` be attached to the eigenform `f`, a pro-`p` Iwahori eigenvector for
`torusChar ξ` at the split place `w` (`star w ≠ w`). Let `A` lie above `w`, let `s⁻¹` act as the
`q ^ k`-th power map on the residue field of `A`, and let `x`, of order `k`, have the class of `s`
as local Artin symbol. Then `r` is of finite type at `A`: it is trivial on inertia near `1` if `ℓ`
is a unit at `A`, and it is potentially crystalline along every embedding inducing `A`. It also has
the jumps of `κ`, and `∏ i, (X - ιℓ (ξ i x))` kills `s` (that is, kills `r s` if `ℓ` is a unit at
`A`). -/
lemma GaloisRep.Attached.local_global_of_eigencharacter_of_pos
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E] {r : GalRep ℓ E n} {A : ClosurePlace} (he : IsEigenform f.val P)
    (hr : Attached P r) (hA : IsPlaceOver A w) (s : decompGroup Gal(Ω/E) A)
    (x : (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)ˣ) (k : ℕ)
    (hs_frob : IsFrob A (w.q ^ k) s.val⁻¹) (hx_artin : localArtin Gal(Ω/E) A w x = s)
    (hx_val : v x.val = WithZero.exp (-k : ℤ)) (hk_pos : 0 < k)
    (hξ_antitone : Antitone fun i : Fin (card n) ↦ ‖(ξ i x).val‖) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (card n)) ∧
    PolyKillsAt r A s.val (∏ i : Fin (card n), (X - C (ιℓ (ξ i x)))) := by
  -- Induct on the index of the group `D` of the `y` with `(|y|, ξ y)` a power of `(|x|, ξ x)`.
  -- Index one forces `k = 1` and `ξ` unramified: the spherical case. Otherwise base change to a
  -- cyclic extension of prime degree in which `x` is a norm lowers the index.
  let D : Subgroup (LocField w)ˣ :=
    (zpowers (normAbsChar.prod (.pi ξ) x)).comap (normAbsChar.prod (.pi ξ))
  induction hidx : D.index using Nat.strong_induction_on generalizing E k with
  | _ idx ih => ?_
  have : D.FiniteIndex := hf_iwahori.finiteIndex_comap_zpowers hx_val hk_pos
  by_cases h_index : D.index = 1
  · obtain ⟨rfl, hunr⟩ := IsIwahoriEigen.order_eq_one_and_unramified hx_val
      ((eq_top_iff' D).1 (index_eq_one.1 h_index))
    rw [pow_one] at hs_frob
    exact hr.local_global_of_eigencharacter_of_unramified hf_iwahori he hA hs_frob hx_val hunr
      hξ_antitone
  -- Duality for the finite group `(LocField w)ˣ ⧸ D` gives `χ` of prime order that is trivial on
  -- `D`.
  obtain ⟨p, hp, hp_dvd⟩ := D.index.exists_prime_and_dvd h_index
  obtain ⟨χ, x₀, hχ₀, hχp, hχD⟩ := exists_char_trivial_of_prime_dvd_index D hp hp_dvd
  have h_tame (y : (LocField w)ˣ) (hy : v y.val = 1) : χ (y ^ (w.q - 1)) = 1 :=
    hχD _ (by simp [D, Subgroup.mem_comap, hf_iwahori.char_pow_q_sub_one_eq_one y hy, one_mem])
  -- As `χ` is tame, Grunwald's theorem gives a Galois character `μ` such that the field
  -- `stepField μ` cut out by `symmetrize μ` has degree `p` and one place `u` above `w`. Under the
  -- Artin map at `w`, `μ` is trivial (`hμw`) and `symmetrize μ` is `χ` (`hμχ`).
  obtain ⟨μ, u, ⟨_inst⟩, _hstep, -, hu, hbelow, hAu, hμw, hμχ⟩ :=
    exists_step_of_local_char hw hA hp χ hχ₀ hχp h_tame
  obtain rfl : u.below E = w := (hbelow u).2 rfl
  -- Base change `f` to `f'`, with eigencharacter `ξ i ∘ N` for the local norm `N`. What holds at
  -- `A` for its representation `r'` descends to `r`.
  let N : (LocField u)ˣ →* (LocField (u.below E))ˣ := localNorm E u
  obtain ⟨f', P', he', hsame, hf'_iwahori⟩ :=
    exists_baseChange_isIwahoriEigen hu hbelow (by simp [*]) hf_iwahori
  obtain ⟨r', hr'⟩ := (sphericalCompat_std u f'.property he').1
  have h_down : DescendsAt μ r' r A := hsame.descendsAt hr' he' he hr A
  -- As `χ x = 1`, `x` is a norm: the residue degree `e` divides `k`, and `s` fixes the step.
  have hx_ker : abelianLift (symmetrize μ) (artinAt Gal(Ω/E) (u.below E) x) = 1 :=
    (hμχ x).trans (hχD x (mem_zpowers _))
  let e : ℕ := u.asIdeal.inertiaDeg (NumberField.RingOfIntegers E)
  have hq : (u.below E).q ^ e = u.q := absNorm_pow_inertiaDeg ..
  have v_norm (z : (LocField u)ˣ) : v (N z).val = v z.val ^ e := v_localNorm hq z
  obtain ⟨k', rfl⟩ : e ∣ k := by
    obtain ⟨z, rfl⟩ := exists_localNorm_of_abelianLift_artinAt hx_ker
    have h_val : WithZero.exp (-k : ℤ) = v z.val ^ e := hx_val.symm.trans (v_norm z)
    exact ofNat_dvd.1 (dvd_neg.1 ⟨(v z.val).log, by simpa using congrArg WithZero.log h_val⟩)
  rw [pow_mul, hq] at hs_frob
  have h_artin : artinAt Gal(Ω/E) (u.below E) x = s.val :=
    hA.artinAt_eq_of_localArtin_eq hx_artin
  have hs_sym : s.val ∈ ker (symmetrize μ) := (h_artin ▸ hx_ker :)
  have hs_μ : s.val ∈ ker μ := (h_artin ▸ hμw x :)
  let s' : Gal(Ω/stepField μ) := (stepField μ).fixingSubgroupEquiv ⟨s, fun z ↦ z.2 ⟨s, hs_sym⟩⟩
  have hs'_frob : IsFrob A (u.q ^ k') s'⁻¹ := hs_frob
  -- Take `y` in the completion at `u` of order `k'` with symbol `s'`. Then `N y` and `x` have the
  -- same symbol and the same order.
  obtain ⟨y, hy_val, hy_artin⟩ := hAu.exists_localArtin_eq hs'_frob k'
  have hart : localArtin Gal(Ω/E) A (u.below E) (N y) = s :=
    (hAu.localArtin_localNorm (Γ := Gal(Ω/stepField μ))
      (AlgEquiv.restrictScalarsHom E)).localArtin_localNorm hy_artin
  have hNy : normAbsChar.prod (.pi ξ) (N y) = normAbsChar.prod (.pi ξ) x :=
    hf_iwahori.eq_of_localArtin_eq hA (by simp [v_norm, hx_val, hy_val]) (hart.trans hx_artin.symm)
  have hξy (i : Fin (card n)) : ξ i (N y) = ξ i x := congrFun (congrArg Prod.snd hNy) i
  simp_rw [← hξy] at hξ_antitone ⊢
  -- The group for `(f', y)` is `D.comap N`, as `N` keeps the absolute value. Its index is smaller:
  -- `χ` kills norms and `D` but not `x₀`.
  have hpull : normAbsChar.prod (.pi fun i ↦ (ξ i).comp N) = (normAbsChar.prod (.pi ξ)).comp N :=
    MonoidHom.ext fun z ↦ Prod.ext (by ext; simp [N, coe_normAbsChar_locField, norm_localNorm]) rfl
  have hχN (z : (LocField u)ˣ) : χ (N z) = 1 :=
    (hμχ _).symm.trans
      (abelianLift_artinAt_eq_one_of_mem_closure (L := stepField μ) adeleNorm_mem_closure)
  have hlt : (D.comap N).index < idx := (index_comap_lt_of_char_ne_one hχ₀ hχD hχN).trans_eq hidx
  obtain ⟨hfin, hjump, hpoly⟩ :
      IsFiniteTypeAt r' A ∧ HasJumpsAt r' A (jumps κ.baseChange (card n)) ∧
        PolyKillsAt r' A s' (∏ i : Fin (card n), (X - C (ιℓ (ξ i (N y))))) := by
    refine ih _ hlt hf'_iwahori he' hr' hAu ⟨s', _⟩ y k' hs'_frob hy_artin hy_val
      (Nat.pos_of_mul_pos_left hk_pos) hξ_antitone ?_
    rw [hpull, MonoidHom.comp_apply, hNy, ← Subgroup.comap_comap]
  exact ⟨h_down.isFiniteTypeAt hfin, h_down.hasJumpsAt _ hjump,
    h_down.polyKillsAt ⟨s, hs_sym, hs_μ⟩ _ hpoly⟩

/-- Local-global compatibility at a split place with a sorted pro-`p` Iwahori eigencharacter. Let
`r` be attached to the eigenform `f`, which at the split place `w` is a pro-`p` Iwahori eigenvector
for `New.torusChar ξ`, with `‖ξ i ϖ‖` antitone in `i` for the uniformiser `ϖ = New.uniformizer w`.
Let `A` lie above `w`, let `s⁻¹` act as the `q ^ k`-th power map on the residue field of `A`, and
let `x`, of order `k`, have the class of `s` as local Artin symbol. Then (a) `r` is of finite type
at `A` (`New.GaloisRep.IsFiniteTypeAt`: trivial on inertia near `1` away from `ℓ`, potentially
crystalline above `ℓ`), (b) it has the Hodge–Tate jumps of `κ`, and (c)
`∏ i, (X - ιℓ (ξ i x))` kills `s` (`New.GaloisRep.PolyKillsAt`). Parts (a) and (b) do not involve
`s`, `x`, `k`; they stand here because one induction proves all three. Here `q = w.q` is the size
of the residue field at `w` and `ιℓ` is the fixed isomorphism of `ℂ` with `ℚ̄_ℓ`. -/
lemma GaloisRep.Attached.local_global_of_eigencharacter
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E] {r : GalRep ℓ E n} {A : ClosurePlace} (he : IsEigenform f.val P)
    (hr : Attached P r) (hξ_antitone : Antitone fun i : Fin (card n) ↦ ‖(ξ i (uniformizer w)).val‖)
    (hA : IsPlaceOver A w) (s : decompGroup Gal(Ω/E) A)
    (x : (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)ˣ) (k : ℕ)
    (hs_frob : IsFrob A (w.q ^ k) s.val⁻¹) (hx_artin : localArtin Gal(Ω/E) A w x = s)
    (hx_val : v x.val = WithZero.exp (-k : ℤ)) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (card n)) ∧
    PolyKillsAt r A s.val (∏ i : Fin (card n), (X - C (ιℓ (ξ i x)))) := by
  obtain hk_pos | rfl : 0 < k ∨ k = 0 := k.eq_zero_or_pos.symm
  · exact hr.local_global_of_eigencharacter_of_pos hf_iwahori he hA s x k hs_frob hx_artin hx_val
      hk_pos (hf_iwahori.antitone_norm hξ_antitone hx_val)
  -- For `k = 0`, multiply `s` by positive powers of the symbol `φ⁻¹` of the uniformiser.
  obtain ⟨φ, hφ, hϖ⟩ : ∃ φ : decompGroup Gal(Ω/E) A,
      IsFrob A w.q φ.val ∧ localArtin Gal(Ω/E) A w (uniformizer w) = ↑φ⁻¹ :=
    hA.exists_isFrob_localArtin_eq_inv (Γ := Gal(Ω/E)) (v_uniformizer w)
  obtain ⟨hfin, hjump, hφ_kill⟩ : IsFiniteTypeAt r A ∧ HasJumpsAt r A (jumps κ (card n)) ∧
      PolyKillsAt r A (φ⁻¹).val (∏ i : Fin (card n), (X - C (ιℓ (ξ i (uniformizer w))))) :=
    hr.local_global_of_eigencharacter_of_pos hf_iwahori he hA φ⁻¹ (uniformizer w) 1 (by simpa) hϖ
      (by simp) one_pos hξ_antitone
  refine ⟨hfin, hjump, .of_mul_frob_pow hA hφ (by simp) hφ_kill fun m hm ↦ ?_⟩
  have h_frob : IsFrob A (w.q ^ m) (s * φ⁻¹ ^ m).val⁻¹ := by
    simpa using (hφ.pow m).mul_iff.2 hs_frob
  have h_art : localArtin Gal(Ω/E) A w (x * uniformizer w ^ m) = ↑(s * φ⁻¹ ^ m) := by
    simp [hx_artin, hϖ]
  have h_val : v (x * uniformizer w ^ m).val = WithZero.exp (-m : ℤ) := by simp [hx_val]
  obtain ⟨-, -, h_kill⟩ := hr.local_global_of_eigencharacter_of_pos hf_iwahori he hA _ _ m h_frob
    h_art h_val hm (hf_iwahori.antitone_norm hξ_antitone h_val)
  simpa using h_kill

end New

/-!
## Frobenius and inertia for parahoric types

At a finite place `w ≠ w̄` of `E` not above `ℓ`, the action of `GL_N(E_w)`, with `N` the cardinality
of `n`, on a form `y` of an isotypic space `x` (`New.Patching.localFormRep`) is compared with the
Galois representation `x.galRep` attached to `x`. A place `A` of the algebraic closure above `w` is
fixed. `New.proIwahori` is the pro-`p` Iwahori subgroup and `ιℓ : ℂ ≃+* ℚ̄_ℓ`.
-/

section TypeFrobenius

open NumberField Matrix Polynomial Finset Valued Pi Nat Algebra Fintype

namespace New.Patching

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
  {E n : Type} [Field E] [CMType E] [Algebra E Ω] [Fintype n] [DecidableEq n] [Nonempty n]
  {V : Space E n 1} {κ : Weight E} [V.IsStd] [WeilData E]
  {w : FinPlace E} {hw : star w ≠ w} {A : ClosurePlace}
  {ϖ u : (LocField w)ˣ} {s τ : decompGroup Gal(Ω/E) A} {x : Isotypic V κ} {y : V.forms κ}

/-- `IsParahoricCompatible ρ z ϖ d F T` says that the matrices `F`, `T` behave as those of a
geometric Frobenius that comes from `ϖ` and of an inertia element, as seen by the vector `z` of `ρ`:
they commute, `T` is killed by every polynomial that vanishes at all `ιℓ (d i)`, and there are
characters `θ i`, with an exponent functional that is not zero on `z`, such that
`∏ i, (X - ιℓ (θ i ϖ * d i ^ b))` kills `F * T ^ b` for every natural number `b`. -/
structure IsParahoricCompatible {E : Type} [Field E] [NumberField E] {w : FinPlace E}
    {N : ℕ} (ρ : Rep ℂ (GL (Fin N) (LocField w))) [IsSmoothRep ρ.ρ]
    (z : ρ) (ϖ : (LocField w)ˣ) (d : Fin N → ℂ) (F T : Matrix n n (PadicAlgCl ℓ)) : Prop where
  /-- Every polynomial that vanishes at all `ιℓ (d i)` kills `T`. -/
  aeval_inertia_eq_zero :
    ∀ p : (PadicAlgCl ℓ)[X], (∀ i : Fin N, p.IsRoot (ιℓ (d i))) → aeval T p = 0
  /-- `F` and `T` commute. -/
  commute : Commute F T
  /-- There are characters `θ i` such that some exponent `l` for the torus character of `θ`
  (`New.IsExponent`) is not zero on `z`, and `∏ i, (X - ιℓ (θ i ϖ * d i ^ b))` kills `F * T ^ b`
  for all `b`. -/
  exists_characters : ∃ θ : Fin N → (LocField w)ˣ →* ℂˣ,
    (∃ l : ρ →ₗ[ℂ] ℂ, IsExponent ρ (torusChar θ) l ∧ l z ≠ 0) ∧
    ∀ b : ℕ, aeval (F * T ^ b) (∏ i : Fin N, (X - C (ιℓ (θ i ϖ * d i ^ b)))) = 0

/-- Let `A` lie above `w ∤ ℓ`. Let the local Artin map send the uniformiser `ϖ` to `s`, the inverse
of a Frobenius element, and the unit `u` to the inertia element `τ`. Let `y ≠ 0` in the isotypic
space `x` be fixed by the pro-`p` Iwahori subgroup at `w`, let the parahoric subgroup with blocks
`f` act on `y` by scalars `c`, and write `d i` for the scalar of the diagonal matrix with `u` in
slot `i` and `1` elsewhere. Assume that slots with the same `d` lie in one block. Then the matrices
`F` of `s` and `T` of `τ` commute, and `T` is killed by every polynomial that vanishes at all
`ιℓ (d i)`. Also, there are characters `θ i` and an exponent for `New.torusChar θ` (a linear
functional as in `New.IsExponent`) that is not zero on `y`, such that
`∏ i, (X - ιℓ (θ i ϖ * d i ^ b))` kills `F * T ^ b` for every natural number `b`
(`New.Patching.IsParahoricCompatible`). -/
lemma isParahoricCompatible_galRep (hA : IsPlaceOver A w) (hϖ : v ϖ.val = WithZero.exp (-1))
    (hϖ_artin : localArtin Gal(Ω/E) A w ϖ = s) (hs_frob : IsFrob A w.q s.val⁻¹)
    (hu : v u.val = 1) (hu_artin : localArtin Gal(Ω/E) A w u = τ)
    (hτ : τ.val ∈ inertiaGroup Gal(Ω/E) A) (hℓ : (ℓ : 𝓞 E) ∉ w.asIdeal) (hy : y ∈ x.val)
    (hy_ne : y ≠ 0) (f : ℕ → ℕ) {c : GL (Fin (card n)) (LocField w) → ℂ}
    (hy_type : y ∈ parahoricEigenspace (localFormRep V κ hw) f c)
    (h_blocks : ∀ i k : Fin (card n),
      c (diagGL (mulSingle i u)) = c (diagGL (mulSingle k u)) → f i = f k) :
    IsParahoricCompatible (localFormRep V κ hw) y ϖ
      (fun i : Fin (Fintype.card n) ↦ c (diagGL (mulSingle i u))) (x.galRep s).val
      (x.galRep τ).val := by
  -- `exists_sorted_isIwahoriEigen_of_diagGL_smul` gives characters `θ` with an exponent and, for a
  -- sorted rearrangement of them, an eigenvector `z` in the system `x`; local-global compatibility
  -- at `z` gives the polynomials.
  cases Space.IsStd.eq_stdSpace V
  let ρ := localFormRep (stdSpace E n) κ hw
  obtain ⟨y_fixed, h_par⟩ := hy_type
  have hℓ_unit : A.valuation ℓ = 1 := hA.valuation_natCast_eq_one_iff.2 hℓ
  -- a permutation that keeps the `d i` keeps the blocks, so its matrix is in the parahoric group
  have h_perm (σ : Equiv.Perm (Fin (card n)))
      (hσ : ∀ i, c (diagGL (mulSingle i u)) = c (diagGL (mulSingle (σ i) u))) :
      permGL σ ∈ blockParahoric (F := LocField w) f := by
    refine ⟨permGL_mem_intGL σ, fun i j hij ↦ ?_⟩
    rw [h_blocks j (σ j) (hσ j)] at hij
    simp [σ.symm_apply_eq, Fin.ext_iff, ne_of_apply_ne f hij.ne']
  obtain ⟨θ, h_exp, hθ, σ, h_anti, z, z_mem, z_eig⟩ :
      ∃ θ : Fin (card n) → (LocField w)ˣ →* ℂˣ,
        (∃ l : ρ →ₗ[ℂ] ℂ, IsExponent ρ (torusChar θ) l ∧ l y ≠ 0) ∧
        (∀ i (ε : (LocField w)ˣ), v ε.val = 1 → θ i ε = c (diagGL (mulSingle i ε))) ∧
        ∃ σ : Equiv.Perm (Fin (card n)), Antitone ((fun i ↦ ‖(θ i (uniformizer w) : ℂ)‖) ∘ σ) ∧
          ∃ z ∈ cyclicSpan ρ.ρ y, IsIwahoriEigen ρ (torusChar (θ ∘ σ)) z :=
    exists_sorted_isIwahoriEigen_of_diagGL_smul (v_uniformizer w) y_fixed
      (fun t ht ↦ h_par _ ⟨ht, fun i j hij ↦ by simp [Fin.ext_iff, ne_of_apply_ne f hij.ne']⟩)
      (fun σ hσ ↦ ⟨c (permGL σ), h_par _ (h_perm σ fun i ↦ hσ i u hu)⟩) isUnitary_localFormRep hy_ne
  have z_form : IsEigenform z.val x.heckePolyAt :=
    (x.isEigenform hy hy_ne).of_mem_cyclicSpan z_mem z_eig.ne_zero
  -- if `g⁻¹` acts as the `w.q ^ k`-th power on the residue field and `g` is the local Artin symbol
  -- of `ε`, of order `k`, then `∏ i, (X - ιℓ (θ (σ i) ε))` kills `g`
  have h_poly (g : decompGroup Gal(Ω/E) A) (ε : (LocField w)ˣ) (k : ℕ)
      (hg : IsFrob A (w.q ^ k) g.val⁻¹) (h_art : localArtin Gal(Ω/E) A w ε = g)
      (hε : v ε.val = WithZero.exp (-(k : ℤ))) : GaloisRep.IsFiniteTypeAt x.galRep A ∧
      GaloisRep.PolyKillsAt x.galRep A g.val (∏ i, (X - C (ιℓ (θ (σ i) ε)))) :=
    ((x.attached_galRep hy hy_ne).local_global_of_eigencharacter z_eig z_form h_anti hA g ε k
      hg h_art hε).imp_right And.right
  -- inertia has finite image, so an inertial `g` that comes from a unit `ε` is semisimple, with
  -- eigenvalues among the `ιℓ (θ i ε)`
  have h_inertia (g : decompGroup Gal(Ω/E) A) (ε : (LocField w)ˣ)
      (hg : g.val ∈ inertiaGroup Gal(Ω/E) A) (h_art : localArtin Gal(Ω/E) A w ε = g)
      (hε : v ε.val = 1) (p : (PadicAlgCl ℓ)[X]) (hp : ∀ i, p.IsRoot (ιℓ (θ (σ i) ε))) :
      aeval (x.galRep g).val p = 0 := by
    obtain ⟨h_fin, h_kill⟩ := h_poly g ε 0 (inv_mem hg) h_art hε
    exact h_fin.aeval_eq_zero_of_roots hℓ_unit hg h_kill p
      (by simpa [eval_prod, prod_eq_zero_iff, sub_eq_zero] using hp)
  refine ⟨fun p hp ↦ ?_, ?_, θ, h_exp, fun b ↦ ?_⟩
  · exact h_inertia τ u hτ hu_artin hu p fun i ↦ by simpa only [hθ _ u hu] using hp (σ i)
  · -- the commutator of `s` and `τ` is inertial and comes from the unit `1`
    have h_conj : IsFrob A 1 (s.val * τ.val * s.val⁻¹) := by
      convert IsFrob.conj hτ s.val
      exact s.prop.symm
    have h_comm : aeval (x.galRep (s * τ / s / τ)).val (X - 1 : (PadicAlgCl ℓ)[X]) = 0 :=
      h_inertia (s * τ / s / τ) 1 (div_mem h_conj hτ) (by simp) (by simp) (X - 1) (by simp)
    simpa [commute_iff_eq, div_eq_iff_eq_mul, Units.ext_iff, sub_eq_zero] using h_comm
  · -- `s * τ ^ b` is a geometric Frobenius that comes from `ϖ * u ^ b`
    have h_frob : IsFrob A (w.q ^ 1) (s * τ ^ b).val⁻¹ := by
      simpa using (zpow_mem hτ (-b)).mul_iff.2 hs_frob
    obtain ⟨-, h_kill, -⟩ :=
      h_poly (s * τ ^ b) (ϖ * u ^ b) 1 h_frob (by simp [hϖ_artin, hu_artin]) (by simp [hϖ, hu])
    rw [← Equiv.prod_comp σ]
    simpa [hθ _ u hu] using h_kill hℓ_unit

omit [Nonempty n] in
/-- Let `F` and `T` commute, let `T` be semisimple with eigenvalues among `d 0, 1, …, 1`, where
`d 0 ≠ 0` and `d 0 ^ N ! ≠ 1`, and let `∏ i, (X - α i * d i ^ b)` kill `F * T ^ b` for every `b`,
with all `α i ≠ 0`. Then `F * (T - 1) = α 0 • (T - 1)`: `F` is the scalar `α 0` on the image of
`T - 1`. -/
lemma mul_sub_one_eq_smul_sub_one {k : Type*} {N : ℕ} [Field k] [NeZero N] {F T : Matrix n n k}
    {α d : Fin N → k} (hd : ∀ i : Fin N, i ≠ 0 → d i = 1) (hd_ne : d 0 ≠ 0) (hζ : d 0 ^ N ! ≠ 1)
    (hα : ∀ i : Fin N, α i ≠ 0) (hFT : Commute F T)
    (hT : ∀ p : k[X], (∀ i : Fin N, p.IsRoot (d i)) → aeval T p = 0)
    (hF : ∀ b : ℕ, aeval (F * T ^ b) (∏ i : Fin N, (X - C (α i * d i ^ b))) = 0) :
    F * (T - 1) = α 0 • (T - 1) := by
  -- Put `ζ = d 0` and `q = ∏_{i ≠ 0} (X - α i)`. On the image of `T - 1` the matrix `T` acts as
  -- `ζ`, so `hF` gives `∑ i, (ζ ^ b) ^ i • (q.coeff i • F ^ i * (F - α 0) * (T - 1)) = 0`. The
  -- `ζ ^ b` are distinct, so every coefficient is zero (Vandermonde); `i = 0` is the claim.
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  let q : k[X] := ∏ i : Fin N, (X - C (α i.succ))
  have hq_zero : q.coeff 0 ≠ 0 := by simp [q, hα, coeff_zero_prod, prod_eq_zero_iff]
  -- `(T - 1) * T = ζ • (T - 1)`, because `(X - 1) * (X - ζ)` vanishes at every `d i`
  have hT_semi : SemiconjBy (T - 1) T (d 0 • 1) := by
    have h_roots (i : Fin (N + 1)) : ((X - 1) * (X - C (d 0))).IsRoot (d i) := by
      by_cases hi : i = 0 <;> simp [hi, hd]
    simpa [SemiconjBy, mul_sub (T - 1), sub_eq_zero, algebraMap_eq_smul_one] using hT _ h_roots
  have h_semi (b : ℕ) : SemiconjBy (T - 1) (F * T ^ b) (d 0 ^ b • F) := by
    simpa [_root_.smul_pow] using
      (hFT.sub_right (.one_right F)).symm.semiconjBy.mul_right (hT_semi.pow_right b)
  -- moving `T - 1` across `hF b` replaces `F * T ^ b` by `ζ ^ b • F`; the factor for `i = 0` is
  -- `ζ ^ b • (F - α 0)`, and `ζ ^ b ≠ 0` cancels
  have h_sum (b : ℕ) : ∑ i : Fin (N + 1),
      (d 0 ^ b) ^ i.val • (q.coeff i • F ^ i.val * (F - α 0 • 1) * (T - 1)) = 0 := by
    have h_prod : ∏ i, (X - C (α i * d i ^ b)) = q * (X - C (α 0 * d 0 ^ b)) := by
      simp [Fin.prod_univ_succ, hd, q, mul_comm]
    have h_move : aeval (d 0 ^ b • F) q * (d 0 ^ b • (F - α 0 • 1)) * (T - 1) = 0 := by
      rw [← mul_zero (T - 1), ← hF b, aeval_semiconj (h_semi b), h_prod, map_mul]
      simp [smul_sub, _root_.smul_pow, smul_smul, mul_comm, algebraMap_eq_smul_one]
    rw [aeval_eq_sum_range, show q.natDegree = N by simp [q], sum_range] at h_move
    simpa [hd_ne, sum_mul, _root_.smul_pow, ← smul_sum, smul_comm (q.coeff _)] using h_move
  -- `ζ ^ i = ζ ^ j` with `i < j ≤ N` gives `ζ ^ (j - i) = 1`, and `j - i` divides `(N + 1)!`
  have h_inj : Function.Injective fun b : Fin (N + 1) ↦ d 0 ^ b.val := by
    refine .of_lt_imp_ne fun i j hij (h_eq : d 0 ^ i.val = d 0 ^ j.val) ↦ hζ ?_
    have h_pow : d 0 ^ (j.val - i.val) = 1 := by simp [pow_sub₀ _ hd_ne hij.le, ← h_eq, hd_ne]
    exact orderOf_dvd_iff_pow_eq_one.1
      ((orderOf_dvd_of_pow_eq_one h_pow).trans (dvd_factorial (by lia) (by lia)))
  have h_zero : q.coeff 0 • F ^ 0 * (F - α 0 • 1) * (T - 1) = 0 := by
    ext r c
    refine congrFun (eq_zero_of_forall_index_sum_pow_mul_eq_zero h_inj (v := fun i ↦
      (q.coeff i • F ^ i.val * (F - α 0 • 1) * (T - 1)) r c) fun b ↦ ?_) 0
    simpa [Matrix.sum_apply] using congrFun₂ (h_sum b) r c
  simpa [hq_zero, sub_mul, sub_eq_zero] using h_zero

/-- Let `A` lie above `w ∤ ℓ`. Let the local Artin map send the uniformiser `ϖ` to `s`, the inverse
of a Frobenius element, and the unit `u` to the inertia element `τ`. Let `y` in the isotypic space
`x` be fixed by the pro-`p` Iwahori subgroup at `w`, and let the stabiliser in `GL_N(𝒪_w)` of the
first coordinate line modulo `w` act on `y` by `χ` of the top left entry
(`New.Patching.parahoricEigenspace`), where `χ u ≠ 0` and `χ u ^ (card n)! ≠ 1`. Let `U` be the
Hecke operator of `diag (ϖ, 1, …, 1)`, `F` the matrix of `s` and `T` that of `τ` minus `1`. Then
`tr (T M) • G(U) y = tr (G(F) T M) • y` through `ιℓ`, for every complex polynomial `G` and every
matrix `M`: `U` acts like `F` on the image of `T`. -/
lemma hecke_eq_frob_on_parahoricEigenspace (hA : IsPlaceOver A w)
    (hϖ : v ϖ.val = WithZero.exp (-1)) (hϖ_artin : localArtin Gal(Ω/E) A w ϖ = s)
    (hs_frob : IsFrob A w.q s.val⁻¹) (hu : v u.val = 1)
    (hu_artin : localArtin Gal(Ω/E) A w u = τ) (hτ : τ.val ∈ inertiaGroup Gal(Ω/E) A)
    (hℓ : (ℓ : 𝓞 E) ∉ w.asIdeal) (hy : y ∈ x.val) (χ : LocField w → ℂ) (hχ : χ u ≠ 0)
    (hζ : χ u ^ (card n)! ≠ 1) (G : ℂ[X]) {M : Matrix n n (PadicAlgCl ℓ)}
    (hy_type : y ∈ parahoricEigenspace (localFormRep V κ hw) (min 1)
      (χ ∘ fun g : GL (Fin (card n)) (LocField w) ↦ g 0 0)) :
    let U := heckeCoset (localFormRep V κ hw).ρ proIwahori (diagGL (mulSingle 0 ϖ))
    let F := (x.galRep s).val
    let T := (x.galRep τ).val - 1
    ιℓ.symm (T * M).trace • aeval U G y =
      ιℓ.symm (aeval F (G.map ιℓ.toRingHom) * T * M).trace • y := by
  intro U F T
  let ρ := localFormRep V κ hw
  let S : Submodule ℂ (V.forms κ) := x.val ⊓ parahoricEigenspace ρ (min 1) (χ ∘ fun g ↦ g 0 0)
  -- Degree one. If the difference `z` of the two sides is not zero, `isParahoricCompatible_galRep`
  -- gives it an exponent `l` with characters `θ` and `l z ≠ 0`. But both `U` (seen by `l`) and `F`
  -- (on the image of `T`) act by `θ 0 ϖ`, so `l z = 0`.
  have degree_one (B : Matrix n n (PadicAlgCl ℓ)) :
      ιℓ.symm (B * T * M).trace • U y = ιℓ.symm (B * F * T * M).trace • y := by
    let z := ιℓ.symm (B * T * M).trace • U y - ιℓ.symm (B * F * T * M).trace • y
    refine eq_of_sub_eq_zero (by_contra fun z_ne : z ≠ 0 ↦ ?_)
    have Uy_mem : U y ∈ S := ⟨x.map_mem (heckeFun_mem_localGroupAlgebra hw _) hy,
      parahoricEigenspace_mem_invtSubmodule ρ hϖ hy_type⟩
    obtain ⟨hz, z_type⟩ : z ∈ S := sub_mem (S.smul_mem _ Uy_mem) (S.smul_mem _ ⟨hy, hy_type⟩)
    have χ_one : χ 1 = 1 :=
      smul_left_injective ℂ z_ne (by simpa using (z_type.2 1 (one_mem _)).symm)
    -- the unit `u` gives `χ u ≠ 1` in slot `0` and `1` in the others: it separates the two blocks
    have χ_ne : χ u ≠ 1 := fun h ↦ hζ (by rw [h, one_pow])
    have χ_slot (i : Fin (card n)) : χ (diagGL (mulSingle i u) 0 0) = 1 ↔ i ≠ 0 := by
      by_cases hi : i = 0 <;> simp [hi, χ_ne, χ_one, eq_comm]
    have blocks (i k : Fin (card n))
        (h_eq : χ (diagGL (mulSingle i u) 0 0) = χ (diagGL (mulSingle k u) 0 0)) :
        min 1 i.val = min 1 k.val := by
      have h_iff : i ≠ 0 ↔ k ≠ 0 := by rw [← χ_slot, ← χ_slot, h_eq]
      grind [Fin.val_ne_zero_iff]
    obtain ⟨τ_roots, comm, θ, ⟨l, hl, lz_ne⟩, sτ_roots⟩ :
        IsParahoricCompatible ρ z ϖ (fun i ↦ χ (diagGL (mulSingle i u) 0 0)) F (x.galRep τ).val :=
      isParahoricCompatible_galRep hA hϖ hϖ_artin hs_frob hu hu_artin hτ hℓ hz z_ne _ z_type blocks
    have l_U : l (U y) = θ 0 ϖ * l y := by
      -- `U y` is `w.q ^ (card n - 1)` times the mean over `proIwahori` of
      -- `ρ (diag (ϖ, 1, …, 1)) y`, and this degree cancels the modulus factor in `torusChar`
      obtain ⟨dominant, U_eq⟩ : mulSingle 0 ϖ ∈ dominantTorus ∧ U y = (w.q : ℂ) ^ (card n - 1) •
          compactMean ρ.ρ proIwahori (ρ.ρ (diagGL (mulSingle 0 ϖ)) y) :=
        heckeCoset_mulSingle_zero_eq hϖ hy_type.1
      have l_diag : l (ρ.ρ (diagGL (mulSingle 0 ϖ)) y) = torusChar θ (mulSingle 0 ϖ) * l y := by
        simpa only [compactMean_eq_self (ρ := ρ.ρ) y hy_type.1] using hl dominant y
      rw [U_eq, map_smul, hl.apply_compactMean, l_diag]
      simp [coe_normAbsChar_locField, norm_locField_eq_q_zpow, hϖ, field]
      exact mul_div_cancel_left₀ _
          (pow_ne_zero _ (by exact_mod_cast (zero_lt_one.trans w.one_lt_q).ne'))
    have F_mul_T : F * T = ιℓ (θ 0 ϖ) • T :=
      mul_sub_one_eq_smul_sub_one (α := fun i ↦ ιℓ (θ i ϖ))
        (fun i hi ↦ by simp only [(χ_slot i).2 hi, map_one])
        (by simpa using hχ) (by simpa using (ιℓ.injective.ne_iff' (map_one ιℓ)).2 hζ) (by simp)
        comm τ_roots (by simpa only [map_mul, map_pow] using sτ_roots)
    exact lz_ne (by simp [z, l_U, mul_assoc B F T, F_mul_T, mul_left_comm, mul_assoc])
  -- Horner induction on `G`: the step from `p` to `p * X` applies `U` and uses degree one
  induction G using recOnHorner with
  | M0 => simp
  | MC p a _ _ ih => simp [ih, add_mul, add_smul, smul_smul, mul_comm, algebraMap_eq_smul_one]
  | MX p _ ih =>
    nth_rw 1 [← X_mul]
    simpa [degree_one] using congrArg U ih

end New.Patching

end TypeFrobenius
