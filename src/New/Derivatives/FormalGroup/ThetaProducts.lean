module

import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import TauCeti.RingTheory.MvPowerSeries.Derivative
import TauCeti.RingTheory.MvPowerSeries.Dvd
public import Lib.General.Algebra.IntegralPowerSeries
import Lib.General.Algebra.SeriesBounds
public import Lib.General.Algebra.SeriesCongruences
import Mathlib.RingTheory.PiTensorProduct
import TauCeti.NumberTheory.Padics.Complex.Basic
public import Lib.CM.FormalGroup.PrimeNotation
public import Lib.CM.Integrality.LogTheta
public import Lib.CM.FormalGroup.FormalParameter
import Lib.CM.GoodReduction
import Lib.CM.Integrality.IsogenyIntegrality
import Mathlib.Algebra.Order.Star.Int
import TauCeti.RingTheory.PowerSeries.Dvd
import TauCeti.RingTheory.PowerSeries.Rescale
import Mathlib.Algebra.Order.Star.Real
public import New.Derivatives.FormalGroup.Resolution
public import New.Derivatives.Vacuum.TightFrames

section
/-!
# Couplings and the normal form

* `New.coupling`, `New.couplingSum`, `New.HasNormalForm`: the couplings `Γ_e` and the normal form
  `F(ϖ z) = W exp (c_ϖ Ξ)` with `W` integral, `c_ϖ = ϖ ^ (p + 1) / p` and
  `Ξ = ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`, for any rule that assigns partners to places.
* `New.HasNormalForm.rescale`: the normal form is kept, with other numbers `λ_{e j}`, under
  `z ↦ α z` with `α` integral.
* `New.HasNormalForm.norm_coeff_subst_le_one`: if `F` has the normal form and `Z` is integral
  without constant term, then `F(ϖ Z)` is integral in degrees at most `B` if the couplings `Γ_e(Z)`
  with `e ∈ S`, `e ≤ log_p B` are divisible by some `π` with `‖c_ϖ π‖ ≤ p ^ (-1 / (p - 1))`.
* `New.HasNormalForm.of_dvd_sub`: it is enough to know the exponent modulo such a `π`.
* `New.dvd_pderiv_couplingSum_sub`: the derivatives of `Ξ` modulo `p`, if `0 ∉ S`. They are not
  needed for the divisibility bound, only for its sharpness.

## Notation

* `valRingCp p` is the valuation ring `𝒪` of `ℂ_[p]`; a series over it is called integral.
* `seriesToCp W` is the series `W` over `𝒪`, seen as a series over `ℂ_[p]`.
* `expSubst g` is the series `exp g`, for `g` without constant term.
* The variables `z_x` are indexed by pairs `x = (τ, i)` in `Φ × c`, for finite types `Φ` and `c`;
  the elements `τ` of `Φ` are called places.
-/

@[expose] public section

open MvPowerSeries WithPiTopology IsLocalRing

namespace New

variable {p : ℕ} [Fact p.Prime] {Φ c : Type} [Fintype Φ] [Fintype c]

/-- The coupling `Γ_e = ∑ z_(τ,i) ^ p ^ e * z_(τ',i)`, summed over all `(τ, i) : Φ × c`, where
`τ' = pr e τ` is the partner of `τ`. -/
noncomputable def coupling (pr : ℕ → Φ → Φ) (e : ℕ) : MvPowerSeries (Φ × c) (valRingCp p) :=
  ∑ x : Φ × c, X x ^ p ^ e * X (pr e x.1, x.2)

/-- The series `Ξ = ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`, where `λ_{e j} = l e j` and `Γ_e` is the
coupling for the partner rule `pr`. -/
noncomputable def couplingSum (S : Set ℕ) (pr : ℕ → Φ → Φ) (l : ℕ → ℕ → valRingCp p) :
    MvPowerSeries (Φ × c) (valRingCp p) :=
  ∑' x : S × ℕ, l x.1 x.2 • coupling pr x.1 ^ p ^ x.2

/-- `F` has the normal form with the given numbers `ϖ` and `λ_{e j} = l e j`:
`F(ϖ z) = W exp (c_ϖ ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j)` with `W` integral and
`c_ϖ = ϖ ^ (p + 1) / p`. -/
def HasNormalForm (S : Set ℕ) (pr : ℕ → Φ → Φ) (ϖ : ℂ_[p]) (l : ℕ → ℕ → valRingCp p)
    (F : MvPowerSeries (Φ × c) ℂ_[p]) : Prop :=
  ∃ W : MvPowerSeries (Φ × c) (valRingCp p),
    F.rescale (fun _ : Φ × c ↦ ϖ) =
      seriesToCp W * expSubst ((ϖ ^ (p + 1) / p) • seriesToCp (couplingSum S pr l))

variable {S : Set ℕ} {pr : ℕ → Φ → Φ} {ϖ : ℂ_[p]} {l : ℕ → ℕ → valRingCp p}
  {F : MvPowerSeries (Φ × c) ℂ_[p]}

/-- A substitution `Z` that is allowed (`HasSubst Z`) commutes with the exponential:
`(exp g)(Z) = exp (g(Z))` if `g(0) = 0`. -/
lemma subst_expSubst {σ τ : Type} {g : MvPowerSeries σ ℂ_[p]} (hg : constantCoeff g = 0)
    {Z : σ → MvPowerSeries τ ℂ_[p]} (hZ : HasSubst Z) :
    (expSubst g).subst Z = expSubst (g.subst Z) :=
  subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg).const hZ _

/-- The coupling after a substitution: `Γ_e(Z) = ∑ Z_(τ,i) ^ p ^ e * Z_(pr e τ, i)`. -/
lemma subst_coupling {τ : Type} {Z : Φ × c → MvPowerSeries τ (valRingCp p)} (hZ : HasSubst Z)
    (e : ℕ) : (coupling pr e : MvPowerSeries (Φ × c) (valRingCp p)).subst Z =
      ∑ x : Φ × c, Z x ^ p ^ e * Z (pr e x.1, x.2) := by
  simp only [coupling, ← coe_substAlgHom hZ, map_sum, map_mul, map_pow, substAlgHom_X]

/-- The coupling `Γ_e` is homogeneous of degree `p ^ e + 1`. -/
lemma rescale_coupling (α : valRingCp p) (e : ℕ) :
    rescale (fun _ : Φ × c ↦ α) (coupling pr e : MvPowerSeries (Φ × c) (valRingCp p)) =
      α ^ (p ^ e + 1) • coupling pr e := by
  rw [rescale_eq_subst, subst_coupling (HasSubst.smul_X _), coupling, Finset.smul_sum]
  simp only [Pi.smul_apply', smul_pow, smul_mul_smul_comm, pow_succ]

/-- The coupling `Γ_e` has order at least `p ^ e + 1`. -/
lemma le_order_coupling (e : ℕ) :
    ((p ^ e + 1 : ℕ) : ℕ∞) ≤ (coupling pr e : MvPowerSeries (Φ × c) (valRingCp p)).order := by
  refine le_order fun d hd ↦ ?_
  rw [coupling, map_sum]
  refine Finset.sum_eq_zero fun x _ ↦ coeff_of_lt_order (hd.trans_le ?_)
  grw [← le_order_mul, ← le_order_pow_of_constantCoeff_eq_zero _ (constantCoeff_X x),
    ← one_le_order_iff_constCoeff_eq_zero.2 (constantCoeff_X _), Nat.cast_succ]

/-- The sum `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j` that defines `couplingSum S pr l` converges, as the
orders of its terms tend to infinity. -/
lemma hasSum_couplingSum :
    HasSum (fun x : S × ℕ ↦ l x.1 x.2 • coupling pr x.1 ^ p ^ x.2)
      (couplingSum S pr l : MvPowerSeries (Φ × c) (valRingCp p)) :=
  (summable_smul_pow_pow (Fact.out : p.Prime).one_lt le_order_coupling S l).hasSum

/-- The series `couplingSum S pr l = ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j` has no constant term. -/
lemma constantCoeff_couplingSum :
    constantCoeff (couplingSum S pr l : MvPowerSeries (Φ × c) (valRingCp p)) = 0 := by
  refine ((hasSum_couplingSum (S := S) (pr := pr) (l := l)).map constantCoeff
    (continuous_constantCoeff _)).unique ?_
  simp [Function.comp_def, coupling, (Fact.out : p.Prime).ne_zero]

/-- A substitution of series `Z_x` without constant term into
`couplingSum S pr l = ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`, where `λ_{e j} = l e j` and
`Γ_e = coupling pr e`, may be carried out term by term. -/
lemma hasSum_subst_couplingSum {τ : Type} {Z : Φ × c → MvPowerSeries τ (valRingCp p)}
    (hZ : ∀ x : Φ × c, constantCoeff (Z x) = 0) :
    HasSum (fun x : S × ℕ ↦ l x.1 x.2 • (coupling (p := p) pr x.1).subst Z ^ p ^ x.2)
      ((couplingSum S pr l).subst Z) := by
  have h_subst : HasSubst Z := hasSubst_of_constantCoeff_zero hZ
  simpa only [Function.comp_def, coe_substAlgHom, subst_smul h_subst, subst_pow h_subst] using
    (hasSum_couplingSum (S := S) (pr := pr) (l := l)).map (substAlgHom h_subst)
      (by simpa only [coe_substAlgHom] using continuous_subst_of_constantCoeff_eq_zero hZ)

/-- Let `Ξ = couplingSum S pr l` be the series `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`. As `Γ_e` is
homogeneous of degree `p ^ e + 1`, the series `Ξ(α z)` is the same sum with `λ_{e j}` multiplied by
`α ^ ((p ^ e + 1) p ^ j)`. -/
lemma rescale_couplingSum (α : valRingCp p) :
    rescale (fun _ : Φ × c ↦ α) (couplingSum S pr l : MvPowerSeries (Φ × c) (valRingCp p)) =
      couplingSum S pr fun e j : ℕ ↦ α ^ ((p ^ e + 1) * p ^ j) * l e j := by
  let Z : Φ × c → MvPowerSeries (Φ × c) (valRingCp p) := (fun _ : Φ × c ↦ α) • X
  have h_term (x : S × ℕ) : l x.1 x.2 • (coupling (p := p) pr x.1).subst Z ^ p ^ x.2 =
      (α ^ ((p ^ (x.1 : ℕ) + 1) * p ^ x.2) * l x.1 x.2) • coupling pr x.1 ^ p ^ x.2 := by
    rw [← rescale_eq_subst, rescale_coupling, smul_pow, smul_smul, ← pow_mul, mul_comm (l _ _)]
  rw [rescale_eq_subst]
  refine (hasSum_subst_couplingSum (Z := Z) fun x ↦ by simp [Z]).unique ?_
  simpa only [h_term] using hasSum_couplingSum (l := fun e j ↦ α ^ ((p ^ e + 1) * p ^ j) * l e j)

/-- If `‖a π‖ ≤ p ^ (-1 / (p - 1))` and the integral series `G` has no constant term and
coefficients divisible by `π` in degrees at most `B`, then `exp (a G)` is integral in these
degrees. -/
lemma norm_coeff_expSubst_smul_le_one {τ : Type} {a : ℂ_[p]} {π : valRingCp p}
    (hπ : ‖a * π‖ ≤ p ^ (-(1 / (p - 1)) : ℝ)) {G : MvPowerSeries τ (valRingCp p)}
    (hG : constantCoeff G = 0) {B : ℕ} (h_dvd : ∀ d : τ →₀ ℕ, d.degree ≤ B → π ∣ coeff d G)
    {m : τ →₀ ℕ} (hm : m.degree ≤ B) : ‖coeff m (expSubst (a • seriesToCp G))‖ ≤ 1 := by
  refine norm_coeff_expSubst_le_one (by simp [hG]) (fun d hd ↦ ?_) hm
  calc ‖coeff d (a • seriesToCp G)‖ = ‖a * (coeff d G : valRingCp p)‖ := rfl
    _ ≤ p ^ (-(1 / (p - 1)) : ℝ) := by
      grw [← hπ, norm_mul, norm_mul, valRingCp.dvd_iff_norm_le.1 (h_dvd d hd)]

/-- To prove that `F` has the normal form `F(ϖ z) = W exp (c_ϖ Ξ₀)`, where `W` is integral,
`c_ϖ = ϖ ^ (p + 1) / p` and `Ξ₀ = couplingSum S pr l`, it is enough to know the exponent modulo a
`π` with `‖c_ϖ π‖ ≤ p ^ (-1 / (p - 1))`: it suffices that `F(ϖ z) = W exp (c_ϖ Ξ)` with `W`, `Ξ`
integral, `Ξ(0) = 0` and `Ξ ≡ Ξ₀` modulo `π`. -/
lemma HasNormalForm.of_dvd_sub {π : valRingCp p}
    (hπ : ‖ϖ ^ (p + 1) / p * π‖ ≤ p ^ (-(1 / (p - 1)) : ℝ))
    {W Ξ : MvPowerSeries (Φ × c) (valRingCp p)} (hΞ : constantCoeff Ξ = 0)
    (h_dvd : C π ∣ Ξ - couplingSum S pr l)
    (hF : F.rescale (fun _ : Φ × c ↦ ϖ) =
      seriesToCp W * expSubst ((ϖ ^ (p + 1) / p) • seriesToCp Ξ)) :
    HasNormalForm S pr ϖ l F := by
  -- The exponential `V` of `c_ϖ` times the difference `G` is integral and is moved into `W`.
  let a : ℂ_[p] := ϖ ^ (p + 1) / p
  set G : MvPowerSeries (Φ × c) (valRingCp p) := Ξ - couplingSum S pr l with hG
  have hG_zero : constantCoeff G = 0 := by simp [hG, hΞ, constantCoeff_couplingSum]
  have h_int (d : Φ × c →₀ ℕ) : ‖coeff d (expSubst (a • seriesToCp G))‖ ≤ 1 :=
    norm_coeff_expSubst_smul_le_one hπ hG_zero
      (fun d' _ ↦ (C_dvd_iff_dvd_coeff _ _).1 h_dvd d') le_rfl
  obtain ⟨V, hV⟩ : ∃ V : MvPowerSeries (Φ × c) (valRingCp p),
      seriesToCp V = expSubst (a • seriesToCp G) := ⟨fun d ↦ ⟨_, h_int d⟩, rfl⟩
  have h_exp : expSubst (a • seriesToCp Ξ) =
      seriesToCp V * expSubst (a • seriesToCp (couplingSum S pr l)) := by
    rw [hV, ← expSubst_add _ (by simp [hG_zero]) (by simp [constantCoeff_couplingSum]), ← smul_add,
      ← map_add, hG, sub_add_cancel]
  exact ⟨W * V, by rw [hF, h_exp, map_mul seriesToCp W V, mul_assoc]⟩

/-- Let `F` have the normal form `F(ϖ z) = W exp (c_ϖ ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j)` with `W`
integral. If the series `Z_x` are integral without constant term, then `F(ϖ Z)` is an integral
series times `exp (c_ϖ ∑_{e ∈ S} ∑_j λ_{e j} Γ_e(Z) ^ p ^ j)`. -/
lemma HasNormalForm.exists_subst_eq_mul_expSubst (hF : HasNormalForm S pr ϖ l F) {τ : Type}
    {Z : Φ × c → MvPowerSeries τ (valRingCp p)} (hZ : ∀ x : Φ × c, constantCoeff (Z x) = 0) :
    ∃ W : MvPowerSeries τ (valRingCp p),
      F.subst (fun x : Φ × c ↦ ϖ • seriesToCp (Z x)) =
        seriesToCp W *
          expSubst ((ϖ ^ (p + 1) / p) • seriesToCp ((couplingSum S pr l).subst Z)) := by
  obtain ⟨W, hW⟩ := hF
  have hZ_subst : HasSubst Z := hasSubst_of_constantCoeff_zero hZ
  have h_subst : HasSubst fun x : Φ × c ↦ seriesToCp (Z x) := hZ_subst.map _
  have h_rescale : F.subst (fun x : Φ × c ↦ ϖ • seriesToCp (Z x)) =
      (F.rescale fun _ ↦ ϖ).subst fun x : Φ × c ↦ seriesToCp (Z x) := by
    rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X _) h_subst]
    simp only [Pi.smul_apply', subst_smul h_subst, subst_X h_subst]
  refine ⟨W.subst Z, ?_⟩
  rw [h_rescale, hW, subst_mul h_subst, subst_expSubst (by simp [constantCoeff_couplingSum])
    h_subst, subst_smul h_subst, map_subst hZ_subst, map_subst hZ_subst]

/-- Let `F` have the normal form `F(ϖ z) = W exp (c_ϖ ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j)` with `W`
integral. Then, for integral `α`, the series `F(α z)` has the normal form with the same `ϖ` and with
`λ_{e j}` multiplied by `α ^ ((p ^ e + 1) p ^ j)`. -/
lemma HasNormalForm.rescale (hF : HasNormalForm S pr ϖ l F) (α : valRingCp p) :
    HasNormalForm S pr ϖ (fun e j : ℕ ↦ α ^ ((p ^ e + 1) * p ^ j) * l e j)
      (F.rescale fun _ : Φ × c ↦ (α : ℂ_[p])) := by
  let Z : Φ × c → MvPowerSeries (Φ × c) (valRingCp p) := (fun _ : Φ × c ↦ α) • X
  have h_subst : (F.rescale fun _ ↦ (α : ℂ_[p])).rescale (fun _ ↦ ϖ) =
      F.subst fun x : Φ × c ↦ ϖ • seriesToCp (Z x) := by
    rw [rescale_rescale, rescale_eq_subst]
    congr! with x
    simp [Z, smul_smul, mul_comm]
  unfold HasNormalForm
  rw [h_subst, ← rescale_couplingSum, rescale_eq_subst _ (couplingSum S pr l)]
  exact hF.exists_subst_eq_mul_expSubst fun x ↦ by simp [Z]

/-- Let `Γ_e = coupling pr e` be the coupling `∑ z_(τ,i) ^ p ^ e * z_(pr e τ, i)`, homogeneous of
degree `p ^ e + 1`. A substitution of series `Z_x` without constant term does not lower orders, so
`Γ_e(Z) ^ p ^ j` has order at least `p ^ e + 1`. -/
lemma le_order_subst_coupling_pow {τ : Type} {Z : Φ × c → MvPowerSeries τ (valRingCp p)}
    (hZ : ∀ x : Φ × c, constantCoeff (Z x) = 0) (e j : ℕ) :
    ((p ^ e + 1 : ℕ) : ℕ∞) ≤ ((coupling (p := p) pr e).subst Z ^ p ^ j).order := by
  calc ((p ^ e + 1 : ℕ) : ℕ∞) ≤ (coupling (p := p) (c := c) pr e).order := le_order_coupling e
    _ ≤ ((coupling (p := p) pr e).subst Z).order := by
      grw [← le_order_subst (hasSubst_of_constantCoeff_zero hZ),
        ← le_iInf fun x ↦ one_le_order_iff_constCoeff_eq_zero.2 (hZ x), one_mul]
    _ ≤ ((coupling (p := p) pr e).subst Z ^ p ^ j).order := by
      grw [← le_order_pow, ← Nat.one_le_pow j p (Fact.out : p.Prime).pos, one_nsmul]

/-- Let `Ξ = couplingSum S pr l` be the series `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`. If the series
`Z_x` have no constant term and `π` divides `Γ_e(Z)` for all `e ∈ S` with `e ≤ log_p B`, then `π`
divides the coefficients of `Ξ(Z)` in degrees at most `B`. -/
lemma dvd_coeff_subst_couplingSum {π : valRingCp p} {τ : Type}
    {Z : Φ × c → MvPowerSeries τ (valRingCp p)} (hZ : ∀ x : Φ × c, constantCoeff (Z x) = 0) {B : ℕ}
    (hΓ : ∀ e ∈ S, e ≤ p.log B →
      C π ∣ (coupling pr e : MvPowerSeries (Φ × c) (valRingCp p)).subst Z)
    {d : τ →₀ ℕ} (hd : d.degree ≤ B) : π ∣ coeff d ((couplingSum S pr l).subst Z) := by
  have hp : p.Prime := Fact.out
  refine dvd_of_hasSum (hasSum_iff_hasSum_coeff.1 (hasSum_subst_couplingSum hZ) d) ?_
  rintro ⟨⟨e, he⟩, j⟩
  set G : MvPowerSeries τ (valRingCp p) := (coupling (p := p) pr e).subst Z ^ p ^ j
  suffices h_dvd : π ∣ coeff d G by simpa only [coeff_smul] using h_dvd.mul_left (l e j)
  obtain h_le | h_lt := le_or_gt e (p.log B)
  · exact (C_dvd_iff_dvd_coeff _ _).1 ((hΓ e he h_le).pow (pow_ne_zero j hp.ne_zero)) d
  · have h_deg : d.degree < p ^ e + 1 :=
      (hd.trans_lt (Nat.lt_pow_of_log_lt hp.one_lt h_lt)).trans (Nat.lt_succ_self _)
    rw [coeff_of_lt_order ((Nat.cast_lt.2 h_deg).trans_le (le_order_subst_coupling_pow hZ e j))]
    exact dvd_zero π

/-- Let `F` have the normal form `F(ϖ z) = W exp (c_ϖ ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j)`. Let
`‖c_ϖ π‖ ≤ p ^ (-1 / (p - 1))`, and let the series `Z_x` be integral without constant term, with `π`
dividing `Γ_e(Z)` for all `e ∈ S` with `e ≤ log_p B`. Then the coefficients of `F(ϖ Z)` in degrees
at most `B` have norm at most `1`. -/
lemma HasNormalForm.norm_coeff_subst_le_one (hF : HasNormalForm S pr ϖ l F) {π : valRingCp p}
    (hπ : ‖ϖ ^ (p + 1) / p * π‖ ≤ p ^ (-(1 / (p - 1)) : ℝ)) {τ : Type}
    {Z : Φ × c → MvPowerSeries τ (valRingCp p)} (hZ : ∀ x : Φ × c, constantCoeff (Z x) = 0) {B : ℕ}
    (hΓ : ∀ e ∈ S, e ≤ p.log B →
      C π ∣ (coupling pr e : MvPowerSeries (Φ × c) (valRingCp p)).subst Z)
    {m : τ →₀ ℕ} (hm : m.degree ≤ B) :
    ‖coeff m (F.subst fun x : Φ × c ↦ ϖ • seriesToCp (Z x))‖ ≤ 1 := by
  classical
  set Ξ : MvPowerSeries τ (valRingCp p) := (couplingSum S pr l).subst Z
  have h_exponent_zero : constantCoeff Ξ = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hZ) hZ constantCoeff_couplingSum
  -- Only couplings of sufficiently small degree can affect the truncated exponential.
  have h_exp_integral (d : τ →₀ ℕ) (hd : d.degree ≤ B) :
      ‖coeff d (expSubst ((ϖ ^ (p + 1) / p) • seriesToCp Ξ))‖ ≤ 1 :=
    norm_coeff_expSubst_smul_le_one hπ h_exponent_zero
      (fun _ hd' ↦ dvd_coeff_subst_couplingSum hZ hΓ hd') hd
  obtain ⟨W, h_factorization⟩ : ∃ W : MvPowerSeries τ (valRingCp p),
      F.subst (fun x : Φ × c ↦ ϖ • seriesToCp (Z x)) =
        seriesToCp W * expSubst ((ϖ ^ (p + 1) / p) • seriesToCp Ξ) :=
          hF.exists_subst_eq_mul_expSubst hZ
  -- The other factor is already integral. Each convolution term uses a coefficient
  -- of the exponential of degree at most B.
  rw [h_factorization, coeff_mul]
  refine sum_mem (S := valRingCp p) fun ⟨d₁, d₂⟩ hd ↦ ?_
  have h_degree_bound : d₂ ≤ m :=
    le_of_add_le_right (Finset.HasAntidiagonal.mem_antidiagonal.1 hd).le
  exact mul_mem (coeff d₁ W).property
    (h_exp_integral d₂ ((Finsupp.degree_mono h_degree_bound).trans hm))

variable [DecidableEq Φ] [DecidableEq c]

open Classical in
/-- The sum of the powers `z_x ^ p ^ e` over the `x = (τ, i)` whose partner `(pr e τ, i)` in the
coupling `Γ_e` is `y`. -/
noncomputable def partnerPowerSum (pr : ℕ → Φ → Φ) (e : ℕ) (y : Φ × c) :
    MvPowerSeries (Φ × c) (valRingCp p) :=
  ∑ x : Φ × c with (pr e x.1, x.2) = y, X x ^ p ^ e

/-- The derivatives of a `p ^ e`-th power vanish modulo `p`, for `e > 0`. -/
lemma dvd_pderiv_pow_pow {σ : Type} (G : MvPowerSeries σ (valRingCp p)) {e : ℕ} (he : e ≠ 0)
    (y : σ) : C (p : valRingCp p) ∣ pderiv y (G ^ p ^ e) := by
  rw [Derivation.leibniz_pow, nsmul_eq_mul, Nat.cast_pow, map_natCast]
  exact (dvd_pow_self _ he).mul_right _

/-- For `e > 0`, only the linear factors of the coupling
`Γ_e = coupling pr e = ∑_{(τ, i)} z_(τ,i) ^ p ^ e * z_(pr e τ, i)` have a derivative modulo `p`:
`∂Γ_e / ∂z_y` is congruent to `partnerPowerSum pr e y`, the sum of the `z_x ^ p ^ e` over the
`x = (τ, i)` whose partner `(pr e τ, i)` is `y`. -/
lemma dvd_pderiv_coupling_sub {e : ℕ} (he : e ≠ 0) (y : Φ × c) :
    C (p : valRingCp p) ∣ pderiv y (coupling pr e) - partnerPowerSum pr e y := by
  classical
  rw [coupling, map_sum, partnerPowerSum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun x _ ↦ ?_
  have h_linear : X x ^ p ^ e * pderiv y (X (pr e x.1, x.2)) =
      if (pr e x.1, x.2) = y then X (R := valRingCp p) x ^ p ^ e else 0 := by
        simp [pderiv_X, Pi.single_apply]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, h_linear, add_sub_cancel_left]
  exact (dvd_pderiv_pow_pow (X x) he y).mul_left _

/-- If `y` is the partner of `x` for `e`, then `z_x ^ p ^ e` has coefficient `1` in
`partnerPowerSum pr e y`. -/
lemma coeff_partnerPowerSum_self (e : ℕ) (x : Φ × c) :
    coeff (.single x (p ^ e)) (partnerPowerSum (p := p) pr e (pr e x.1, x.2)) = 1 := by
  classical
  simp [partnerPowerSum, coeff_X_pow,
    Finsupp.single_left_inj (pow_ne_zero e (Fact.out : p.Prime).ne_zero)]

/-- The only monomials of `partnerPowerSum pr e y` are the `z_x ^ p ^ e` with `y` the partner of
`x` for `e`. -/
lemma exists_single_of_coeff_partnerPowerSum_ne_zero {e : ℕ} {y : Φ × c} {d : Φ × c →₀ ℕ}
    (h_ne : coeff d (partnerPowerSum (p := p) pr e y) ≠ 0) :
    ∃ x : Φ × c, (pr e x.1, x.2) = y ∧ d = .single x (p ^ e) := by
  classical
  rw [partnerPowerSum, map_sum] at h_ne
  obtain ⟨x, hx, h_coeff⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_ne
  exact ⟨x, (Finset.mem_filter.1 hx).2, by simpa [coeff_X_pow] using h_coeff⟩

/-- The series `partnerPowerSum pr e y` has order at least `p ^ e`. -/
lemma le_order_partnerPowerSum (e : ℕ) (y : Φ × c) :
    ((p ^ e : ℕ) : ℕ∞) ≤ (partnerPowerSum (p := p) pr e y).order := by
  refine le_order fun d hd ↦ by_contra fun h_ne ↦ ?_
  obtain ⟨x, -, rfl⟩ := exists_single_of_coeff_partnerPowerSum_ne_zero h_ne
  simp at hd

/-- The sum `∑_{e ∈ S} λ_{e 0} * partnerPowerSum pr e y`, where `λ_{e 0} = l e 0` and
`partnerPowerSum pr e y` is the sum of the `z_x ^ p ^ e` over the `x = (τ, i)` with partner
`(pr e τ, i) = y`, converges, as the term `e` has order at least `p ^ e`. -/
lemma summable_smul_partnerPowerSum (y : Φ × c) :
    Summable fun e : S ↦ l e 0 • partnerPowerSum (p := p) pr e y := by
  refine summable_of_finite_order_le fun n ↦ ?_
  refine ((Set.finite_Iic n).preimage Subtype.val_injective.injOn).subset fun e he ↦ ?_
  have h_le : ((p ^ (e : ℕ) : ℕ) : ℕ∞) ≤ n :=
    ((le_order_partnerPowerSum e y).trans le_order_smul).trans he
  exact (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le.trans (Nat.cast_le.1 h_le)

/-- Let `Ξ = couplingSum S pr l` be the series `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`. If `0 ∉ S`, then
modulo `p` only the linear factors in the terms `j = 0` count in the derivatives:
`∂Ξ / ∂z_y ≡ ∑_{e ∈ S} λ_{e 0} * partnerPowerSum pr e y`. -/
lemma dvd_pderiv_couplingSum_sub (hS : 0 ∉ S) (y : Φ × c) :
    C (p : valRingCp p) ∣
      pderiv y (couplingSum S pr l) - ∑' e : S, l e 0 • partnerPowerSum pr e y := by
  have h_deriv :
      HasSum (fun x : S × ℕ ↦ pderiv y (l x.1 x.2 • coupling pr x.1 ^ p ^ x.2))
        (pderiv y (couplingSum S pr l)) :=
    hasSum_couplingSum.map (pderiv y).toLinearMap (continuous_pderiv y)
  -- The second sum, written over the pairs `(e, j)` with zero terms for `j > 0`.
  have h_main : HasSum (fun x : S × ℕ ↦ if x.2 = 0 then l x.1 0 • partnerPowerSum pr x.1 y else 0)
      (∑' e : S, l e 0 • partnerPowerSum (p := p) pr e y) := by
    refine ((Prod.mk_left_injective 0).hasSum_iff fun x hx ↦ ite_eq_right fun hj : x.2 = 0 ↦
      hx ⟨x.1, Prod.ext rfl hj.symm⟩).1 ?_
    simpa [Function.comp_def] using (summable_smul_partnerPowerSum y).hasSum
  refine C_dvd_of_hasSum (h_deriv.sub h_main) ?_
  rintro ⟨⟨e, he⟩, _ | j⟩
  · simpa [← smul_sub, smul_eq_C_mul, ← mul_sub] using
      (dvd_pderiv_coupling_sub (ne_of_mem_of_not_mem he hS) y).mul_left (C (l e 0))
  · rw [ite_eq_right j.succ_ne_zero, sub_zero, Derivation.map_smul, smul_eq_C_mul]
    exact (dvd_pderiv_pow_pow _ j.succ_ne_zero y).mul_left _

/-- Let `Ξ = couplingSum S pr l` be the series `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`. If `0 ∉ S`, then
modulo the maximal ideal of `valRingCp p` the coefficients of `∂Ξ / ∂z_y` are those of
`∑_{e ∈ S} λ_{e 0} * partnerPowerSum pr e y`. -/
lemma residue_coeff_pderiv_couplingSum_eq (hS : 0 ∉ S) (y : Φ × c) (d : Φ × c →₀ ℕ) :
    residue (valRingCp p) (coeff d (pderiv y (couplingSum S pr l))) =
      residue (valRingCp p) (∑' e : S, l e 0 * coeff d (partnerPowerSum pr e y)) := by
  have h_sum : ∑' e : S, l e 0 * coeff d (partnerPowerSum pr e y) =
      coeff d (∑' e : S, l e 0 • partnerPowerSum pr e y) :=
    (hasSum_iff_hasSum_coeff.1 (summable_smul_partnerPowerSum y).hasSum d).tsum_eq
  obtain ⟨a, ha⟩ : (p : valRingCp p) ∣ coeff d (pderiv y (couplingSum S pr l)) -
      ∑' e : S, l e 0 * coeff d (partnerPowerSum pr e y) := by
    simpa only [h_sum, ← map_sub] using
      (C_dvd_iff_dvd_coeff _ _).1 (dvd_pderiv_couplingSum_sub hS y) d
  rw [sub_eq_iff_eq_add'] at ha
  simp only [ha, map_add, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]

/-- Let `Ξ = couplingSum S pr l` be the series `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`. Let `0 ∉ S` and
`e ∈ S`, and let `y = (pr e τ, i)` be the partner of `x = (τ, i)` for `e`. Modulo the maximal ideal
of `valRingCp p`, the coefficient of the one monomial `z_x ^ p ^ e` in `∂Ξ / ∂z_y` is `λ_{e 0}`. -/
lemma residue_coeff_pderiv_couplingSum (hS : 0 ∉ S) {e : ℕ} (he : e ∈ S) (x : Φ × c) :
    residue (valRingCp p)
        (coeff (.single x (p ^ e)) (pderiv (pr e x.1, x.2) (couplingSum S pr l))) =
      residue (valRingCp p) (l e 0) := by
  have h_zero (e' : S) (h_ne : e' ≠ ⟨e, he⟩) :
      coeff (.single x (p ^ e)) (partnerPowerSum (p := p) pr e' (pr e x.1, x.2)) = 0 := by
    by_contra h_ne_zero
    obtain ⟨x', -, h_eq⟩ := exists_single_of_coeff_partnerPowerSum_ne_zero h_ne_zero
    have h_pow : p ^ (e' : ℕ) = p ^ e := by
      rw [← Finsupp.degree_single x (p ^ e), h_eq, Finsupp.degree_single]
    exact h_ne (Subtype.ext (Nat.pow_right_injective (Fact.out : p.Prime).two_le h_pow))
  rw [residue_coeff_pderiv_couplingSum_eq hS, tsum_eq_single ⟨e, he⟩ fun e' h_ne ↦ by
    simp [h_zero e' h_ne], coeff_partnerPowerSum_self, mul_one]

/-- Let `Ξ = couplingSum S pr l` be the series `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`. If `0 ∉ S`, then
modulo the maximal ideal of `𝒪 = valRingCp p` the series `∂Ξ / ∂z_y` has only monomials
`z_x ^ p ^ e` with `e ∈ S` and `y = (pr e τ, i)` the partner of `x = (τ, i)` for `e`. -/
lemma exists_eq_single_of_residue_coeff_pderiv_ne_zero (hS : 0 ∉ S) {y : Φ × c} {d : Φ × c →₀ ℕ}
    (h_ne : residue (valRingCp p) (coeff d (pderiv y (couplingSum S pr l))) ≠ 0) :
    ∃ e ∈ S, ∃ x : Φ × c, (pr e x.1, x.2) = y ∧ d = .single x (p ^ e) := by
  by_contra h_none
  have h_zero (e : S) : coeff d (partnerPowerSum (p := p) pr e y) = 0 :=
    by_contra fun he ↦ h_none ⟨e, e.property, exists_single_of_coeff_partnerPowerSum_ne_zero he⟩
  simp [residue_coeff_pderiv_couplingSum_eq hS, h_zero] at h_ne

end New
end
end

section
section
/-!
# Frobenius congruence for `θ` and the coefficient of `z ^ (p - 1)` in `x`

Let `d ≡ 7` modulo `8` be a prime, `C` a lattice with complex multiplication by the integers of
`K = ℚ(√-d)`, and `p` a prime that does not split in `K`. This file proves that
`θ(π_p z) / θ(z) ^ q_p` is `1` modulo `π_p` in `𝒪[[y]]`. For `g = -log θ` it follows that
`q_p g(z) - g(π_p z)` lies in `π_p 𝒪[[y]]`. Independently of this congruence, it shows by a
recursion that at an inert prime the coefficient of `z ^ (p - 1)` in `x` is a unit; this is used in
the last step for the exponent on one curve (`New.CMLattice.norm_coeff_exponentSeries_eq_one`).

Notions from other files:
* `chiK d p` is the Legendre symbol `(p / d)`: it is `1`, `-1`, `0` when `p` is split, inert,
  ramified in `K`.
* `π_p = piPrime d p` is `√-d` for `p = d` and `p` otherwise; `q_p = primeNorm d p` is `p ^ 2` for
  inert `p` and `p` otherwise.
* `PadicPlace p` is the choice of a ring homomorphism `ιₚ : ℂ →+* ℂ_[p]`, and `taylorVia ιₚ f` is
  the Taylor series of `f` at `0`, with coefficients sent to `ℂ_[p]` by `ιₚ`.
* `θ`, `x`, `y` are the series of the theta function `C.θ`, of `C.translatedX z = ℘(z + t) - ℘(t)`
  and of `C.translatedY z = (℘'(z + t) - a₁ x(z)) / 2`. Here `t = C.t` is the chosen point of order
  two, the lattice is scaled so that `℘''(t) = 2`, and `a₁ = C.a₁` satisfies `a₁ ^ 2 = 12 ℘(t)`;
  moreover `g = C.negLogTheta = -log θ`.
* `C.integralSeriesRing = 𝒪[[y]]` is the ring of power series in `y` with coefficients in the
  valuation ring `𝒪` of `ℂ_[p]`.

## Main definitions and results

* `New.CMLattice.exists_rescale_theta_eq_pow_mul_one_add_smul`: at a non-split prime `p` the
  quotient `θ(π_p z) / θ(z) ^ q_p` is `1` modulo `π_p` in `𝒪[[y]]`.
* `New.CMLattice.exists_negLogTheta_frobenius_congruence`: `q_p g(z) - g(π_p z) ∈ π_p 𝒪[[y]]` for
  `g = -log θ`.
* `New.CMLattice.norm_coeff_taylorVia_translatedX_eq_one`: at an inert prime `p` the coefficient
  of `z ^ (p - 1)` in the series `x` is a unit.
-/

@[expose] public section

/-!
## The Frobenius congruence for `θ`

The quotient `θ(π_p z) / θ(z) ^ q_p` is a polynomial in `x` of degree less than `q_p / 2`, so the
congruence can be checked below the degree `q_p`, where `π_p g` is integral.
-/

section FrobeniusCongruence

open PowerSeries IsUltrametricDist

namespace New
variable {d p : ℕ} [PrimeSevenModEight d] [Fact p.Prime]

/-- A prime `p` with `chiK d p ≠ 1`, that is, with Legendre symbol `(p / d) ≠ 1`, so that `p` does
not split in `ℚ(√-d)`, is odd (`p ≠ 2`), as `2` splits. -/
lemma ne_two_of_chiK_ne_one (hp : chiK d p ≠ 1) : p ≠ 2 := by
  rintro rfl
  exact hp QuadField.chiK_two

/-- Let `d ≡ 7` modulo `8` be a prime. If the prime `p` does not split in `ℚ(√-d)`, that is
`chiK d p ≠ 1`, then `primeNorm d p`, which is `p ^ 2` or `p`, is odd, since the prime `2`
splits. -/
lemma odd_primeNorm (hp : chiK d p ≠ 1) : Odd (primeNorm d p) := by
  obtain ⟨e, -, h_eq⟩ : ∃ e : ℕ, e ≠ 0 ∧ primeNorm d p = p ^ e := exists_primeNorm_eq_pow d p
  rw [h_eq]
  exact ((Fact.out : p.Prime).odd_of_ne_two (ne_two_of_chiK_ne_one hp)).pow

/-- If `p` is inert in `ℚ(√-d)`, then `p < q_p = primeNorm d p = p ^ 2`. -/
lemma lt_primeNorm_of_chiK_eq_neg_one (hp : chiK d p = -1) : p < primeNorm d p := by
  rw [primeNorm, ite_eq_left hp]
  exact lt_self_pow₀ (Fact.out : p.Prime).one_lt one_lt_two

variable [PadicPlace p]

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that does not split in `ℚ(√-d)`. Then
`|q_p| = |π_p| ^ 2` in `ℂ_[p]`, as `q_p = ± π_p ^ 2`. -/
lemma norm_primeNorm (hp : chiK d p ≠ 1) : ‖(primeNorm d p : ℂ_[p])‖ = ‖ιₚ (piPrime d p)‖ ^ 2 := by
  obtain ⟨rfl, h_ram⟩ | ⟨hd, h_split | h_inert⟩ := chiK_cases d p
  · rw [piPrime, ite_eq_left rfl, ← norm_pow, map_I_mul_sqrt_sq, norm_neg, primeNorm, h_ram,
      ite_eq_right (by norm_num)]
  · exact absurd h_split hp
  · rw [piPrime, ite_eq_right hd, map_natCast, primeNorm, ite_eq_left h_inert, Nat.cast_pow,
      norm_pow]

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that does not split in `ℚ(√-d)`. Then
`|π_p| ≤ p ^ (-1 / (p - 1))` in `ℂ_[p]`, as `p ≥ 3` (the prime `2` splits) and the valuation of
`π_p` is at least `1 / 2`. -/
lemma norm_piPrime_le_rpow (hp : chiK d p ≠ 1) :
    ‖ιₚ (piPrime d p)‖ ≤ p ^ (-(1 / (p - 1)) : ℝ) := by
  have h_three : (3 : ℝ) ≤ p :=
    mod_cast (Fact.out : p.Prime).two_le.lt_of_ne' (ne_two_of_chiK_ne_one hp)
  have h_exponent : 1 / (p - 1 : ℝ) ≤ piPrimeValuation d p :=
    (one_div_le_one_div_of_le two_pos (by linarith)).trans (half_le_piPrimeValuation d p)
  rw [norm_piPrime]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg h_exponent)

/-- Let `d ≡ 7` modulo `8` and `p` be primes. Then `|π_p| ≤ |√-d|` in `ℂ_[p]`, via the homomorphism
`ιₚ : ℂ →+* ℂ_[p]` that `PadicPlace p` chooses. -/
lemma norm_piPrime_le_norm_sqrt_neg : ‖ιₚ (piPrime d p)‖ ≤ ‖ιₚ (.I * √d)‖ := by
  obtain rfl | hd := eq_or_ne p d
  · rw [piPrime, ite_eq_left rfl]
  · have h_sq : ‖ιₚ (.I * √d)‖ ^ 2 = 1 := by
      rw [← norm_pow, map_I_mul_sqrt_sq, norm_neg,
        ((Nat.coprime_primes Fact.out Fact.out).2 hd).norm_natCast_eq_one]
    rw [(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h_sq]
    exact (norm_piPrime_lt_one d).le

/-- Let `d ≡ 7` modulo `8` and `p` be primes. Then `|π_p| ≤ |n|` in `ℂ_[p]` for `0 < n < q_p`. -/
lemma norm_piPrime_le_norm_natCast {n : ℕ} (hn_ne : n ≠ 0) (hn : n < primeNorm d p) :
    ‖ιₚ (piPrime d p)‖ ≤ ‖(n : ℂ_[p])‖ := by
  have hp : p.Prime := Fact.out
  by_cases h_inert : chiK d p = -1
  · have hd : p ≠ d := by
      rintro rfl
      simp [chiK, ZMod.natCast_self] at h_inert
    have hn_lt : n < p ^ 2 := by rwa [primeNorm, ite_eq_left h_inert] at hn
    have h_val : padicValNat p n ≤ 1 := Nat.padicValNat_def ▸
      Nat.le_of_lt_succ ((multiplicity_le_nat_log n).trans_lt (Nat.log_lt_of_lt_pow hn_ne hn_lt))
    rw [piPrime, ite_eq_right hd, map_natCast, norm_p_eq_inv,
      norm_natCast_eq_inv_pow_padicValNat hn_ne]
    exact (pow_one _).symm.trans_le (pow_le_pow_of_le_one (by positivity) p.cast_inv_le_one h_val)
  · have hn_lt : n < p := by rwa [primeNorm, ite_eq_right h_inert] at hn
    rw [(Nat.coprime_of_lt_prime hn_ne hn_lt hp).norm_natCast_eq_one]
    exact (norm_piPrime_lt_one d).le

/-- Let `d ≡ 7` modulo `8` and `p` be primes. Then `|π_p| ≤ |(k + 2) (k + 1)|` in `ℂ_[p]` for
`k + 2 < q_p`, as one of the two factors is prime to `p`. -/
lemma norm_piPrime_le_norm_mul_succ {k : ℕ} (hk : k + 2 < primeNorm d p) :
    ‖ιₚ (piPrime d p)‖ ≤ ‖((k + 2 : ℕ) : ℂ_[p]) * (k + 1 : ℕ)‖ := by
  have hp : p.Prime := Fact.out
  rw [norm_mul]
  by_cases h_dvd : p ∣ k + 1
  · have h_coprime : p.Coprime (k + 2) := hp.coprime_iff_not_dvd.2
      fun h_dvd_succ ↦ hp.not_dvd_one ((Nat.dvd_add_right h_dvd).1 h_dvd_succ)
    rw [h_coprime.norm_natCast_eq_one, one_mul]
    exact norm_piPrime_le_norm_natCast k.succ_ne_zero (by omega)
  · rw [(hp.coprime_iff_not_dvd.2 h_dvd).norm_natCast_eq_one, mul_one]
    exact norm_piPrime_le_norm_natCast (k + 1).succ_ne_zero hk

namespace CMLattice
variable (C : CMLattice d)

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that does not split in `ℚ(√-d)`. Then
`θ(π_p z) = θ(z) ^ q_p * R(x(z))` as power series over `ℂ_[p]`, for a polynomial `R` of degree less
than `q_p / 2`. -/
lemma exists_rescale_theta_eq_pow_mul_aeval (hp : chiK d p ≠ 1) :
    ∃ R : Polynomial ℂ_[p],
      2 * R.natDegree < primeNorm d p ∧
      rescale (ιₚ (piPrime d p)) (taylorVia ιₚ C.θ) =
        taylorVia ιₚ C.θ ^ primeNorm d p * R.aeval (taylorVia ιₚ C.translatedX) := by
  -- `θ(π z)` is an even section of degree `q`, bounded by the `q`-th power of the naive height.
  have h_isog : C.IsIsogeny C.periodPair (piPrime d p) (primeNorm d p) :=
    ⟨C.mul_mem_of_quadInt (piPrime_mem_quadInt d), by rw [piPrime_mul_conj d hp]⟩
  let f : ℂ → ℂ := fun z ↦ C.θ (piPrime d p * z)
  have h_mem : f ∈ C.sections (primeNorm d p) := by
    simpa only [one_mul] using C.comp_mul_mem_sections h_isog C.theta_mem
  have h_le (z : ℂ) : ‖ιₚ (f z)‖ ≤ C.naiveHeight z ^ primeNorm d p :=
    (C.norm_theta_le_naiveHeight _).trans (C.naiveHeight_mul_le h_isog z)
  have h_even : f.Even := fun z ↦ by simp only [f, mul_neg, theta_neg]
  obtain ⟨R, hR⟩ : ∃ R : Polynomial ℂ, C.IsIntegralEvenExpansion (primeNorm d p) f R :=
    C.exists_polynomial_of_even h_mem h_le h_even
  refine ⟨R.map ιₚ, ?_, ?_⟩
  · obtain ⟨k, hk⟩ : Odd (primeNorm d p) := odd_primeNorm hp
    have h_deg : 2 * R.natDegree ≤ primeNorm d p := hR.two_mul_natDegree_le
    grind [Polynomial.natDegree_map]
  · rw [← hR.taylorVia_eq, taylorVia, taylorVia, taylorAtZero_comp_mul, rescale_map]

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that does not split in `ℚ(√-d)`. Then
`|π_p| |g_n| ≤ 1` for the `n`-th coefficient `g_n` of `g` and `n < q_p`. -/
lemma norm_piPrime_mul_coeff_negLogTheta_le_one (hp : chiK d p ≠ 1) {n : ℕ}
    (hn : n < primeNorm d p) : ‖ιₚ (piPrime d p)‖ * ‖coeff n C.negLogTheta‖ ≤ 1 := by
  match n with
  | 0 => simp [constantCoeff_negLogTheta]
  | 1 => simp [coeff_one_negLogTheta]
  | 2 =>
    have h_two : ‖(2 : ℂ_[p])‖ = 1 := mod_cast Nat.Coprime.norm_natCast_eq_one
      ((Nat.coprime_primes Fact.out Nat.prime_two).2 (ne_two_of_chiK_ne_one hp)) ℂ_[p]
    have h_sqrt : ‖ιₚ (.I * √d)‖ * ‖coeff 2 C.negLogTheta‖ ≤ 1 := by
      simpa only [norm_mul, h_two, one_mul] using C.norm_sqrt_mul_coeff_two_negLogTheta_le_one
    exact (mul_le_mul_of_nonneg_right norm_piPrime_le_norm_sqrt_neg (norm_nonneg _)).trans h_sqrt
  | k + 3 =>
    -- Compare the coefficients of `z ^ (k + 1)` in `g'' = g''(0) + x`.
    have h_coeff : ((k + 1 + 2 : ℕ) : ℂ_[p]) * (k + 1 + 1 : ℕ) * coeff (k + 3) C.negLogTheta =
        coeff (k + 1) (taylorVia ιₚ C.translatedX) := by
      have h_coeff_eq : coeff (k + 1) (d⁄dX (d⁄dX C.negLogTheta)) =
          coeff (k + 1) (taylorVia ιₚ C.translatedX) := by
        rw [C.derivative_derivative_negLogTheta, map_add, coeff_succ_C, zero_add]
      rw [← h_coeff_eq, coeff_derivative, coeff_derivative]
      push_cast
      ring
    calc ‖ιₚ (piPrime d p)‖ * ‖coeff (k + 3) C.negLogTheta‖
        ≤ ‖((k + 1 + 2 : ℕ) : ℂ_[p]) * (k + 1 + 1 : ℕ)‖ * ‖coeff (k + 3) C.negLogTheta‖ :=
          mul_le_mul_of_nonneg_right (norm_piPrime_le_norm_mul_succ hn) (norm_nonneg _)
      _ = ‖coeff (k + 1) (taylorVia ιₚ C.translatedX)‖ := by rw [← norm_mul, h_coeff]
      _ ≤ 1 := C.norm_coeff_le_one_of_lt C.taylorVia_translatedX_mem_integralSeriesRing (by omega)

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that does not split in `ℚ(√-d)`. For `n < q_p`
the `n`-th coefficient `(q_p - π_p ^ n) g_n` of `q_p g(z) - g(π_p z)` has norm at most `|π_p|`. -/
lemma norm_coeff_smul_negLogTheta_sub_rescale_le (hp : chiK d p ≠ 1) {n : ℕ}
    (hn : n < primeNorm d p) :
    ‖coeff n ((primeNorm d p : ℂ_[p]) • C.negLogTheta -
      rescale (ιₚ (piPrime d p)) C.negLogTheta)‖ ≤ ‖ιₚ (piPrime d p)‖ := by
  rw [map_sub, coeff_smul, coeff_rescale, smul_eq_mul, ← sub_mul, norm_mul]
  match n with
  | 0 => simp [constantCoeff_negLogTheta]
  | 1 => simp [coeff_one_negLogTheta]
  | k + 2 =>
    have h_bound : ‖ιₚ (piPrime d p)‖ * ‖coeff (k + 2) C.negLogTheta‖ ≤ 1 :=
      C.norm_piPrime_mul_coeff_negLogTheta_le_one hp hn
    set π : ℂ_[p] := ιₚ (piPrime d p)
    have h_factor : ‖(primeNorm d p : ℂ_[p]) - π ^ (k + 2)‖ ≤ ‖π‖ ^ 2 := by
      rw [sub_eq_add_neg]
      refine (norm_add_le_max _ _).trans (max_le (norm_primeNorm hp).le ?_)
      rw [norm_neg, norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg π) (norm_piPrime_lt_one d).le (Nat.le_add_left 2 k)
    calc ‖(primeNorm d p : ℂ_[p]) - π ^ (k + 2)‖ * ‖coeff (k + 2) C.negLogTheta‖
        ≤ ‖π‖ ^ 2 * ‖coeff (k + 2) C.negLogTheta‖ := by gcongr
      _ = ‖π‖ * (‖π‖ * ‖coeff (k + 2) C.negLogTheta‖) := by ring
      _ ≤ ‖π‖ := mul_le_of_le_one_right (norm_nonneg π) h_bound

/-- The Frobenius congruence. Let `d ≡ 7` modulo `8` be a prime and `p` a prime that does not split
in `ℚ(√-d)`. The Taylor series of `θ` at `0`, mapped by the chosen `ιₚ : ℂ →+* ℂ_[p]`, satisfies
`θ(π_p z) = θ(z) ^ q_p * (1 + π_p H)` for some `H ∈ 𝒪[[y]]`. -/
lemma exists_rescale_theta_eq_pow_mul_one_add_smul (hp : chiK d p ≠ 1) :
    ∃ H : ℂ_[p]⟦X⟧, H ∈ C.integralSeriesRing ∧
      rescale (ιₚ (piPrime d p)) (taylorVia ιₚ C.θ) =
        taylorVia ιₚ C.θ ^ primeNorm d p * (1 + ιₚ (piPrime d p) • H) := by
  set π : ℂ_[p] := ιₚ (piPrime d p)
  set x : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedX
  obtain ⟨R, h_degree_bound, h_theta_factorization⟩ : ∃ R : Polynomial ℂ_[p],
      2 * R.natDegree < primeNorm d p ∧
      rescale π (taylorVia ιₚ C.θ) = taylorVia ιₚ C.θ ^ primeNorm d p * R.aeval x :=
    C.exists_rescale_theta_eq_pow_mul_aeval hp
  have hx : x ∈ C.integralSeriesRing := C.taylorVia_translatedX_mem_integralSeriesRing
  -- `R(x) = exp (q g(z) - g(π z))` is `1` modulo `π` below the degree `q`.
  have h_low_series_coeff (n : ℕ) (hn : n < primeNorm d p) : ‖coeff n ((R - 1).aeval x)‖ ≤ ‖π‖ := by
    rw [map_sub, map_one, ← C.expSubst_smul_negLogTheta_sub_rescale_eq h_theta_factorization]
    exact norm_coeff_expSubst_sub_one_le (norm_piPrime_le_rpow hp)
      (constantCoeff_smul_sub_rescale C.constantCoeff_negLogTheta _ _)
      (fun k hk ↦ C.norm_coeff_smul_negLogTheta_sub_rescale_le hp hk) hn
  -- Recover the polynomial coefficients from the low series coefficients using `x = z² + ⋯`.
  -- Since `2 * R.natDegree < q`, this accounts for every coefficient of `R - 1`.
  have h_polynomial_coeff (i : ℕ) (hi : 2 * i < primeNorm d p) : ‖(R - 1).coeff i‖ ≤ ‖π‖ :=
    norm_coeff_le_of_aeval C.X_sq_dvd_taylorVia_translatedX C.coeff_two_taylorVia_translatedX
      (fun k hk ↦ C.norm_coeff_le_one_of_lt hx hk) h_low_series_coeff hi
  have h_sub_degree_bound : (R - 1).natDegree ≤ R.natDegree := by simpa using R.natDegree_sub_le 1
  -- The quotient polynomial now has integral coefficients, so evaluation at the integral series
  -- `x` gives an integral series in all degrees.
  refine ⟨π⁻¹ • (R - 1).aeval x, ?_, ?_⟩
  · rw [Polynomial.aeval_eq_sum_range, Finset.smul_sum]
    refine sum_mem fun i hi ↦ ?_
    rw [smul_smul]
    refine C.isSeriesGenerator_translatedY.smul_mem ?_ (pow_mem hx i)
    rw [norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (h_polynomial_coeff i (by grind)) (norm_nonneg π)
  · rw [smul_inv_smul₀ ((map_ne_zero ιₚ).2 (piPrime_ne_zero d)), map_sub, map_one, add_sub_cancel,
      h_theta_factorization]

/-- The logarithm of the Frobenius congruence. Let `d ≡ 7` modulo `8` be a prime and `p` a prime
that does not split in `ℚ(√-d)`. Then `q_p g(z) - g(π_p z) = π_p H` for some `H ∈ 𝒪[[y]]`. -/
lemma exists_negLogTheta_frobenius_congruence (hp : chiK d p ≠ 1) :
    ∃ H : ℂ_[p]⟦X⟧, H ∈ C.integralSeriesRing ∧
      (primeNorm d p : ℂ_[p]) • C.negLogTheta - rescale (ιₚ (piPrime d p)) C.negLogTheta =
        ιₚ (piPrime d p) • H := by
  set π : ℂ_[p] := ιₚ (piPrime d p)
  obtain ⟨H, hH, h_theta_congruence⟩ : ∃ H : ℂ_[p]⟦X⟧, H ∈ C.integralSeriesRing ∧
      rescale π (taylorVia ιₚ C.θ) = taylorVia ιₚ C.θ ^ primeNorm d p * (1 + π • H) :=
    C.exists_rescale_theta_eq_pow_mul_one_add_smul hp
  have hπ : π ≠ 0 := (map_ne_zero ιₚ).2 (piPrime_ne_zero d)
  let G : ℂ_[p]⟦X⟧ := π⁻¹ • ((primeNorm d p : ℂ_[p]) • C.negLogTheta - rescale π C.negLogTheta)
  have h_log_factorization :
      π • G = (primeNorm d p : ℂ_[p]) • C.negLogTheta - rescale π C.negLogTheta :=
    smul_inv_smul₀ hπ _
  have h_log_constant_zero : constantCoeff G = 0 := by
    rw [constantCoeff_smul, constantCoeff_smul_sub_rescale C.constantCoeff_negLogTheta, smul_zero]
  have h_exp_congruence : expSubst (π • G) = 1 + π • H := by
    rw [h_log_factorization, C.expSubst_smul_negLogTheta_sub_rescale_eq h_theta_congruence]
  exact ⟨G, C.isSeriesGenerator_translatedY.mem_of_expSubst_smul_eq hπ (norm_piPrime_le_rpow hp)
    h_log_constant_zero hH h_exp_congruence, h_log_factorization.symm⟩

end CMLattice

end New

end FrobeniusCongruence

/-!
## The coefficient of `z ^ (p - 1)` in `x` at an inert prime

The numbers `h_n = [z ^ (p - 1)] x ^ n` satisfy a three-term recursion modulo `p` that leads from
`h_0 = 0` and `h_1` to `h_((p - 1) / 2) = 1`.
-/

section SupersingularCoeff

open PowerSeries IsUltrametricDist

namespace New.CMLattice

section Derivatives
variable {d : ℕ} (C : CMLattice d)
variable {K : Type*} [Field K] [CharZero K] (ι : ℂ →+* K)

/-- `x'² = 4 x³ + a₁² x² + 4 x` for the Taylor series `x` of `℘(z + t) - ℘(t)`, with coefficients
mapped to `K` by `ι`. -/
lemma derivative_taylorVia_translatedX_sq :
    d⁄dX (taylorVia ι C.translatedX) ^ 2 = 4 * taylorVia ι C.translatedX ^ 3 +
      .C (ι C.a₁) ^ 2 * taylorVia ι C.translatedX ^ 2 + 4 * taylorVia ι C.translatedX := by
  rw [derivative_taylorVia_translatedX]
  linear_combination 4 * C.taylorVia_curve_eq ι

/-- `x'' = 6 x² + a₁² x + 2` for the Taylor series `x` of `℘(z + t) - ℘(t)`, with coefficients
mapped to `K` by `ι`. -/
lemma derivative_derivative_taylorVia_translatedX :
    d⁄dX (d⁄dX (taylorVia ι C.translatedX)) = 6 * taylorVia ι C.translatedX ^ 2 +
      .C (ι C.a₁) ^ 2 * taylorVia ι C.translatedX + 2 := by
  have h_deriv : d⁄dX (d⁄dX (taylorVia ι C.translatedX)) =
      2 * d⁄dX (taylorVia ι C.translatedY) +
        .C (ι C.a₁) * d⁄dX (taylorVia ι C.translatedX) := by
    conv_lhs => rw [derivative_taylorVia_translatedX]
    simp [two_mul, Derivation.leibniz]
  rw [h_deriv, derivative_taylorVia_translatedY, derivative_taylorVia_translatedX]
  ring

/-- `(xⁿ x')' = (4 n + 6) xⁿ⁺² + (n + 1) a₁² xⁿ⁺¹ + (4 n + 2) xⁿ` for the Taylor series `x` of
`℘(z + t) - ℘(t)`, with coefficients mapped to `K` by `ι`. -/
lemma derivative_pow_mul_derivative_taylorVia_translatedX (n : ℕ) :
    d⁄dX (taylorVia ι C.translatedX ^ n * d⁄dX (taylorVia ι C.translatedX)) =
      (4 * n + 6 : K) • taylorVia ι C.translatedX ^ (n + 2) +
      ((n + 1) * ι C.a₁ ^ 2 : K) • taylorVia ι C.translatedX ^ (n + 1) +
      (4 * n + 2 : K) • taylorVia ι C.translatedX ^ n := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, derivative_derivative_taylorVia_translatedX]
  simp only [smul_eq_C_mul, smul_eq_mul, nsmul_eq_mul, map_add, map_mul, map_pow, map_ofNat,
    map_natCast, map_one]
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.add_sub_cancel]
    push_cast
    linear_combination
      (n + 1) * taylorVia ι C.translatedX ^ n * C.derivative_taylorVia_translatedX_sq ι

end Derivatives

variable {d : ℕ} (C : CMLattice d) [PrimeSevenModEight d]
variable {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that is inert in `ℚ(√-d)`. The numbers
`h_n = [z ^ (p - 1)] x ^ n` satisfy a recursion modulo the maximal ideal: `(4 n + 6)
h_(n + 2) + (n + 1) a₁² h_(n + 1) + (4 n + 2) h_n` has norm less than `1`. -/
lemma norm_coeff_pow_taylorVia_translatedX_recursion_lt_one (hp : chiK d p = -1) (n : ℕ) :
    ‖(4 * n + 6) * coeff (p - 1) (taylorVia ιₚ C.translatedX ^ (n + 2)) +
      (n + 1) * ιₚ C.a₁ ^ 2 * coeff (p - 1) (taylorVia ιₚ C.translatedX ^ (n + 1)) +
      (4 * n + 2) * coeff (p - 1) (taylorVia ιₚ C.translatedX ^ n)‖ < 1 := by
  -- This is the coefficient of `z ^ (p - 1)` in `(xⁿ x')'`, so `p` times an integral number.
  set x : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedX with hx
  have hx_mem : x ∈ C.integralSeriesRing := C.taylorVia_translatedX_mem_integralSeriesRing
  have h_int : ‖coeff p (x ^ n * d⁄dX x)‖ ≤ 1 := C.norm_coeff_le_one_of_lt
    (mul_mem (pow_mem hx_mem n) (C.derivative_mem_integralSeriesRing hx_mem))
    (lt_primeNorm_of_chiK_eq_neg_one hp)
  have h_deriv : coeff (p - 1) (d⁄dX (x ^ n * d⁄dX x)) =
      coeff p (x ^ n * d⁄dX x) * (p : ℂ_[p]) := by
    rw [coeff_derivative, ← Nat.cast_add_one, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  calc _ = ‖coeff (p - 1) (d⁄dX (x ^ n * d⁄dX x))‖ := by
        simp only [hx, C.derivative_pow_mul_derivative_taylorVia_translatedX ιₚ n, map_add,
          coeff_smul, smul_eq_mul]
    _ = ‖coeff p (x ^ n * d⁄dX x)‖ * ‖(p : ℂ_[p])‖ := by rw [h_deriv, norm_mul]
    _ < 1 := (mul_le_of_le_one_left (norm_nonneg _) h_int).trans_lt (PadicComplex.norm_p_lt_one p)

omit [PrimeSevenModEight d] in
/-- The coefficient of `z ^ (2 m)` in `x ^ m` is `1`, as the Taylor series `x` of
`℘(z + t) - ℘(t)`, mapped by `ιₚ : ℂ →+* ℂ_[p]`, is `z² + ⋯`. Here `t = C.t` is the chosen point of
order two, with `℘''(t) = 2`. -/
lemma coeff_two_mul_taylorVia_translatedX_pow (m : ℕ) :
    coeff (2 * m) (taylorVia ιₚ C.translatedX ^ m) = (1 : ℂ_[p]) := by
  obtain ⟨u, hu⟩ : X ^ 2 ∣ taylorVia ιₚ C.translatedX := C.X_sq_dvd_taylorVia_translatedX
  have hu_one : constantCoeff u = 1 := by
    simpa [hu, coeff_X_pow_mul'] using C.coeff_two_taylorVia_translatedX (p := p)
  simp [hu, mul_pow, ← pow_mul, coeff_X_pow_mul', hu_one]

/-- Let `d ≡ 7` modulo `8` be a prime and `p = 2 m + 1` a prime that is inert in `ℚ(√-d)`. If the
coefficient of `z ^ (p - 1)` in `x` has norm less than `1`, then so does that in `x ^ n` for every
`n ≤ m`, by the recursion for these coefficients. -/
lemma norm_coeff_pow_taylorVia_translatedX_lt_one (hp : chiK d p = -1) {m : ℕ}
    (hp_eq : p = 2 * m + 1) (h_lt : ‖coeff (p - 1) (taylorVia ιₚ C.translatedX)‖ < 1)
    {n : ℕ} (hn : n ≤ m) :
    ‖coeff (p - 1) (taylorVia ιₚ C.translatedX ^ n)‖ < 1 := by
  have hp_prime : p.Prime := Fact.out
  induction n using Nat.twoStepInduction with
  | zero => simp [coeff_one, Nat.sub_ne_zero_of_lt hp_prime.one_lt]
  | one => simpa only [pow_one] using h_lt
  | more n ih₀ ih₁ =>
    set c₀ : ℂ_[p] := coeff (p - 1) (taylorVia ιₚ C.translatedX ^ n)
    set c₁ : ℂ_[p] := coeff (p - 1) (taylorVia ιₚ C.translatedX ^ (n + 1))
    set c₂ : ℂ_[p] := coeff (p - 1) (taylorVia ιₚ C.translatedX ^ (n + 2))
    have h_recursion_small :
        ‖(4 * n + 6) * c₂ + (n + 1) * ιₚ C.a₁ ^ 2 * c₁ + (4 * n + 2) * c₀‖ < 1 :=
      C.norm_coeff_pow_taylorVia_translatedX_recursion_lt_one hp n
    -- `4 n + 6 = 2 (2 n + 3)` with `p` odd and `2 n + 3 < p`.
    have h_coprime : p.Coprime (2 * (2 * n + 3)) :=
      .mul_right (Nat.coprime_two_right.2 ⟨m, hp_eq⟩)
        (Nat.coprime_of_lt_prime (Nat.succ_ne_zero _) (by omega) hp_prime)
    have h_leading_unit : ‖(4 * n + 6 : ℂ_[p])‖ = 1 := by
      rw [← h_coprime.norm_natCast_eq_one ℂ_[p]]
      norm_num [mul_add, ← mul_assoc]
    have h_factor₁ : ‖(n + 1) * ιₚ C.a₁ ^ 2‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      refine (mul_le_of_le_one_left (by positivity) ?_).trans
        (pow_le_one₀ (norm_nonneg _) C.norm_a₁_le_one)
      exact_mod_cast norm_natCast_le_one ℂ_[p] (n + 1)
    have h_previous_terms_small : ‖(n + 1) * ιₚ C.a₁ ^ 2 * c₁ + (4 * n + 2) * c₀‖ < 1 :=
      norm_lt_one_of_eq_mul_add_mul h_factor₁ (mod_cast norm_natCast_le_one ℂ_[p] (4 * n + 2))
        rfl (ih₁ (by omega)) (ih₀ (by omega))
    -- The leading coefficient is a unit, so the recursion propagates strict smallness to `c₂`.
    calc ‖c₂‖ = ‖(4 * n + 6) * c₂‖ := by rw [norm_mul, h_leading_unit, one_mul]
      _ = ‖((4 * n + 6) * c₂ + (n + 1) * ιₚ C.a₁ ^ 2 * c₁ + (4 * n + 2) * c₀) +
            -((n + 1) * ιₚ C.a₁ ^ 2 * c₁ + (4 * n + 2) * c₀)‖ := by ring_nf
      _ < 1 := (norm_add_le_max _ _).trans_lt (max_lt h_recursion_small (by rwa [norm_neg]))

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that is inert in `ℚ(√-d)`. The coefficient of
`z ^ (p - 1)` in the Taylor series `x` of `℘(z + t) - ℘(t)`, mapped by `ιₚ : ℂ →+* ℂ_[p]`, has norm
`1`. -/
lemma norm_coeff_taylorVia_translatedX_eq_one (hp : chiK d p = -1) :
    ‖coeff (p - 1) (taylorVia ιₚ C.translatedX)‖ = 1 := by
  -- If this coefficient is not a unit, neither is that in `x ^ m` for `p = 2 m + 1`, which is `1`.
  obtain ⟨m, hp_eq⟩ : Odd p :=
    (Fact.out : p.Prime).odd_of_ne_two (ne_two_of_chiK_ne_one (by simp [hp] : chiK d p ≠ 1))
  have h_le : ‖coeff (p - 1) (taylorVia ιₚ C.translatedX)‖ ≤ 1 :=
    C.norm_coeff_le_one_of_lt C.taylorVia_translatedX_mem_integralSeriesRing
      ((Nat.sub_le p 1).trans_lt (lt_primeNorm_of_chiK_eq_neg_one hp))
  refine h_le.eq_of_not_lt fun h_lt ↦ ?_
  have h_last : ‖coeff (p - 1) (taylorVia ιₚ C.translatedX ^ m)‖ < 1 :=
    C.norm_coeff_pow_taylorVia_translatedX_lt_one hp hp_eq h_lt le_rfl
  simp [show p - 1 = 2 * m by omega, C.coeff_two_mul_taylorVia_translatedX_pow m] at h_last

end New.CMLattice

end SupersingularCoeff
end
end

/-!
# The exponent on one curve

Let `d ≡ 7` mod `8` be a prime (`PrimeSevenModEight d`), let `p` be a prime that does not split in
`ℚ(√-d)`, and let `𝒪` (`valRingCp p`) be the ring of integers of `ℂ_p`; a series is integral if its
coefficients lie in `𝒪`.

* `New.CMLattice.exists_exponent_tsum`: for some `ϖ` of valuation `ρ_p` the series `θ(ϖ z)` is
  integral up to one exponential `exp (c_ϖ Ξ₁)`, where `c_ϖ = ϖ ^ (p + 1) / p`, the series `Ξ₁` is
  integral, and modulo `π_p` it has only terms `(z ^ p ^ e * z) ^ p ^ j` with `e ∈ I_p°`
  (`partnerExponents d p`: the odd numbers, and all numbers if `p = d`).

The proof has four steps.

1. Averaging `ζ ^ (-p - 1) g(ζ z)` over the `(q_p - 1)`-th roots of unity `ζ` replaces `g = -log θ`
   by its part `g^♭` in the degrees `≡ p + 1` mod `q_p - 1`.
2. The Frobenius congruence gives a functional equation for `Ξ₁ = -g^♭(ϖ z) / c_ϖ`.
3. The equation is solved degree by degree. With `Y = T(ϖ z) / ϖ ≡ ∑_j z ^ q_p ^ j` and a number
   `λ ∈ 𝒪` one has `Ξ₁ ≡ λ Y ^ (p + 1)` for inert `p` and `Ξ₁ ≡ λ (Y ^ 2 - z ^ 2 / 2)` for `p = d`.
   The coefficients of the terms are `λ` in the first case, and `λ / 2`, `λ` or `2 λ` in the second.
4. For inert `p` the coefficient of `z ^ (p + 1)` in `Ξ₁` is a unit, and so is `λ`.

Notions from other files:
* `chiK d p` is the Legendre symbol `(p / d)`; the prime `p` is non-split if `chiK d p ≠ 1`.
* `q_p = primeNorm d p` is the norm of a prime above `p`, `π_p = piPrime d p` is `√-d` if `p = d`
  and `p` otherwise, and `ρ_p = varpiValuation d p` is `v(π_p) / (q_p - 1)` with `v(p) = 1`.
* `C : CMLattice d` is a lattice in `ℂ` that is stable under the ring of integers of `ℚ(√-d)`, with
  a chosen point `t` of order two.
* `taylorVia ιₚ C.θ` is the Taylor series over `ℂ_p` of the theta function `θ` of `C`, along the
  embedding `ιₚ : ℂ →+* ℂ_[p]` fixed by `PadicPlace p`, and `C.negLogTheta` is `g = -log θ`.
* `C.integralSeriesRing` is the ring `𝒪[[y]] = 𝒪[[T]]`, where `y` is the Taylor series of
  `C.translatedY` and `T = C.formalParam` is the formal parameter.

## Relation to the literature

Earlier bounds for one curve at inert primes, which are not used: Bannai–Kobayashi, Algebraic theta
functions and the p-adic interpolation of Eisenstein–Kronecker numbers (first arXiv version, Theorem
4.1); Bannai–Kobayashi, Integral structures on p-adic Fourier theory; Bannai–Kobayashi–Yasuda, The
radius of convergence of the p-adic sigma function; Fujiwara, On divisibilities of special values of
real analytic Eisenstein series.
-/

@[expose] public section

open PowerSeries Finset

namespace New

/-- The least positive degree `i₀ ≡ p + 1` mod `q_p - 1` at a non-split prime: `2` if `p = d`, and
`p + 1` if `p` is inert. -/
def leastFlatDegree (d p : ℕ) : ℕ := if p = d then 2 else p + 1

lemma leastFlatDegree_pos (d p : ℕ) : 0 < leastFlatDegree d p := by
  grind [leastFlatDegree]

/-- Let `G` be a series over the ring of integers `𝒪 = valRingCp p` of `ℂ_p`, read over `ℂ_p` by
`seriesToCp`, and let `i < m`. The part `congruencePart m i` of `G` in the degrees `≡ i` mod `m` is
`l X ^ i + X ^ (i + m) H` with `l ∈ 𝒪` and `H ∈ 𝒪[[X]]`. -/
lemma exists_congruencePart_eq_smul_X_pow_add {p : ℕ} [Fact p.Prime] {m i : ℕ} (hi : i < m)
    (G : (valRingCp p)⟦X⟧) :
    ∃ (l : valRingCp p) (H : (valRingCp p)⟦X⟧),
      congruencePart m i (seriesToCp G) = (l : ℂ_[p]) • X ^ i + X ^ (i + m) * seriesToCp H := by
  refine ⟨coeff i G, mk fun k ↦ if i + m + k ≡ i [MOD m] then coeff (i + m + k) G else 0, ?_⟩
  ext n
  simp only [congruencePart, coeff_mk, map_add, coeff_smul, coeff_X_pow, coeff_X_pow_mul',
    coeff_seriesToCp, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h_large : i + m ≤ n
  · -- From the degree `i + m` on the part agrees with the shifted series.
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h_large
    rw [ite_eq_right (by omega : i + m + k ≠ i), ite_eq_left h_large, Nat.add_sub_cancel_left,
      zero_add]
    split_ifs <;> rfl
  · -- Below the degree `i + m` only the degree `i` is congruent to `i`.
    have h_iff : n ≡ i [MOD m] ↔ n = i :=
      ⟨fun h ↦ h.eq_of_abs_lt (abs_lt.2 (by omega)), fun h ↦ by rw [h]⟩
    simp only [h_iff, ite_eq_right h_large, add_zero]
    split_ifs with h_eq <;> simp [h_eq]

/-- A number of norm `p ^ r` is not zero. -/
lemma ne_zero_of_norm_eq_rpow {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} {r : ℝ}
    (hx : ‖x‖ = (p : ℝ) ^ r) : x ≠ 0 := by
  rw [← norm_pos_iff, hx]
  exact Real.rpow_pos_of_pos (Nat.cast_pos.2 (Fact.out : p.Prime).pos) _

/-- Let `𝒪 = valRingCp p` be the ring of integers of `ℂ_p`. A series `F` over `ℂ_p` whose
coefficients are congruent modulo `π ∈ 𝒪` to those of an integral series `G` comes from an integral
series `Ξ` by `seriesToCp`, and `Ξ ≡ G` modulo `π`. -/
lemma exists_seriesToCp_eq_and_C_dvd_sub {p : ℕ} [Fact p.Prime] {π : valRingCp p} {F : ℂ_[p]⟦X⟧}
    {G : (valRingCp p)⟦X⟧} (h : ∀ n : ℕ, ‖coeff n F - (coeff n G).val‖ ≤ ‖π.val‖) :
    ∃ Ξ : (valRingCp p)⟦X⟧, seriesToCp Ξ = F ∧ C π ∣ Ξ - G := by
  obtain ⟨D, hD⟩ : ∃ D : (valRingCp p)⟦X⟧, seriesToCp D = F - seriesToCp G :=
    mem_range_seriesToCp.2 fun n ↦ (h n).trans π.property
  refine ⟨D + G, by rw [map_add, hD, sub_add_cancel], ?_⟩
  rw [add_sub_cancel_right]
  refine (C_dvd_iff_dvd_coeff _ _).2 fun n ↦ valRingCp.dvd_iff_norm_le.2 ?_
  rw [← coeff_seriesToCp, hD]
  exact h n

section Numbers
variable {p : ℕ} [Fact p.Prime] {d : ℕ} [PrimeSevenModEight d]

/-- For a prime `d ≡ 7` mod `8` the Legendre symbol `chiK d p = (p / d)` vanishes at `p = d`. -/
lemma chiK_eq_zero_of_ramified (hd : p = d) : chiK d p = 0 :=
  (chiK_cases d p).elim (·.2) fun h ↦ absurd hd h.1

/-- Let `d ≡ 7` mod `8` be a prime. A prime `p` with Legendre symbol `chiK d p = (p / d) ≠ 1` is
ramified in `ℚ(√-d)`, with norm `q_p = primeNorm d p = p`, or inert, with `(p / d) = -1` and
`q_p = p²`. -/
lemma ramified_or_inert (hp : chiK d p ≠ 1) :
    p = d ∧ primeNorm d p = p ∨ p ≠ d ∧ chiK d p = -1 ∧ primeNorm d p = p ^ 2 := by
  rcases chiK_cases d p with ⟨hd, h_zero⟩ | ⟨hd, h_split | h_inert⟩
  · exact .inl ⟨hd, by simp [primeNorm, h_zero]⟩
  · exact absurd h_split hp
  · exact .inr ⟨hd, h_inert, by rw [primeNorm, ite_eq_left h_inert]⟩

/-- At a non-split prime `p` (one with `chiK d p ≠ 1`), the degree `i₀ = leastFlatDegree d p` is
less than `q_p - 1`, where `q_p = primeNorm d p`. -/
lemma leastFlatDegree_lt (hp : chiK d p ≠ 1) : leastFlatDegree d p < primeNorm d p - 1 := by
  rcases ramified_or_inert hp with ⟨hd, hq⟩ | ⟨hd, -, hq⟩
  · grind [leastFlatDegree, (PrimeSevenModEight.mod_eight : d % 8 = 7)]
  · have h3 : 3 ≤ p := (Fact.out : p.Prime).two_le.lt_of_ne' (ne_two_of_chiK_ne_one hp)
    rw [leastFlatDegree, ite_eq_right hd, hq, Nat.lt_sub_iff_add_lt]
    nlinarith

/-- At a non-split prime `p` (one with `chiK d p ≠ 1`), one has `p + 1 ≡ i₀ = leastFlatDegree d p`
mod `q_p - 1`, where `q_p = primeNorm d p`. -/
lemma add_one_modEq_leastFlatDegree (hp : chiK d p ≠ 1) :
    p + 1 ≡ leastFlatDegree d p [MOD primeNorm d p - 1] := by
  rcases ramified_or_inert hp with ⟨hd, hq⟩ | ⟨hd, -, -⟩
  · have h_eq : p + 1 = p - 1 + 2 := by grind [(Fact.out : p.Prime).pos]
    rw [leastFlatDegree, ite_eq_left hd, hq, h_eq]
    exact Nat.add_modEq_left
  · rw [leastFlatDegree, ite_eq_right hd]

variable [PadicPlace p]

/-- Let `d ≡ 7` mod `8` be a prime and `p` a prime with Legendre symbol `chiK d p = (p / d) ≠ 1`.
The numbers `π_p = piPrime d p`, `q_p = primeNorm d p`, `i₀ = leastFlatDegree d p` are `√-d`, `p`,
`2` if `p = d`, and `p`, `p²`, `p + 1` if `p` is inert; `π_p` is read in `ℂ_p` by the embedding `ιₚ`
that `PadicPlace p` fixes. If `ϖ ≠ 0` and `‖ϖ‖ ^ (q_p - 1) = ‖π_p‖`, then `π_p ϖ ^ i₀ / (q_p c_ϖ)`
has norm one. -/
lemma norm_piPrime_mul_pow_leastFlatDegree_div (hp : chiK d p ≠ 1) {ϖ : ℂ_[p]} (hϖ0 : ϖ ≠ 0)
    (hϖ : ‖ϖ‖ ^ (primeNorm d p - 1) = ‖ιₚ (piPrime d p)‖) :
    ‖ιₚ (piPrime d p) * ϖ ^ leastFlatDegree d p / (primeNorm d p * (ϖ ^ (p + 1) / p))‖ = 1 := by
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  rcases ramified_or_inert hp with ⟨hd, hq⟩ | ⟨hpd_ne, -, hq⟩
  · have h_norm : ‖ιₚ (piPrime d p)‖ = ‖ϖ ^ (p - 1)‖ := by rw [norm_pow, ← hϖ, hq]
    have h_eq : ιₚ (piPrime d p) * ϖ ^ 2 / (p * (ϖ ^ (p + 1) / p)) =
        ιₚ (piPrime d p) / ϖ ^ (p - 1) := by
      rw [pow_succ ϖ p, ← pow_sub_one_mul (Fact.out : p.Prime).ne_zero ϖ]
      field
    rw [leastFlatDegree, ite_eq_left hd, hq, h_eq, norm_div, h_norm,
      div_self (norm_ne_zero_iff.2 (pow_ne_zero _ hϖ0))]
  · have h_eq : (p : ℂ_[p]) * ϖ ^ (p + 1) / (p ^ 2 * (ϖ ^ (p + 1) / p)) = 1 := by field
    rw [leastFlatDegree, piPrime, ite_eq_right hpd_ne, ite_eq_right hpd_ne, hq, map_natCast,
      Nat.cast_pow, h_eq, norm_one]

omit [PrimeSevenModEight d] in
lemma piPrime_sq_of_ramified (hd : p = d) : ιₚ (piPrime d p) ^ 2 = -(p : ℂ_[p]) := by
  rw [piPrime, ite_eq_left hd, map_I_mul_sqrt_sq, ← hd]

/-- Let `d ≡ 7` mod `8` be a prime and `p` a prime that is non-split in `ℚ(√-d)`. Let
`π_p = piPrime d p` be `√-d` if `p = d` and `p` otherwise, mapped to `ℂ_p` by the place `ιₚ`, and
let `q_p = primeNorm d p` be the norm of a prime above `p`. For `n > 2` we have
`‖π_p ^ n / q_p‖ ≤ ‖π_p‖`: the number `π_p ^ n / q_p` is `p ^ (n - 2)` if `p` is inert, and
`-π_p ^ (n - 2)` if `p = d`. -/
lemma norm_piPrime_pow_div_le (hp : chiK d p ≠ 1) {n : ℕ} (hn : 2 < n) :
    ‖ιₚ (piPrime d p) ^ n / primeNorm d p‖ ≤ ‖ιₚ (piPrime d p)‖ := by
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = 2 + (k + 1) := ⟨n - 3, by omega⟩
  have h_eq : ‖ιₚ (piPrime d p) ^ (2 + (k + 1)) / primeNorm d p‖ =
      ‖ιₚ (piPrime d p)‖ ^ (k + 1) := by
    rcases ramified_or_inert hp with ⟨hd, hq⟩ | ⟨hpd_ne, -, hq⟩
    · -- Here `π_p ^ 2 = -p`.
      simp [hq, pow_add, piPrime_sq_of_ramified hd, mul_right_comm _ _ (p : ℝ),
        (Fact.out : p.Prime).ne_zero]
    · simp [hq, piPrime, hpd_ne, pow_add, hp0]
  rw [h_eq]
  exact pow_le_of_le_one (norm_nonneg _) (norm_piPrime_lt_one d).le k.succ_ne_zero

end Numbers

namespace CMLattice
variable {p : ℕ} [Fact p.Prime] {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) [PadicPlace p]

/-! ## Step 1: averaging -/

/-- The series `g^♭`: the part of `g = -log θ` (`C.negLogTheta`) in the degrees `≡ p + 1` mod
`q_p - 1`, where `q_p = primeNorm d p` and `θ` is the theta function of `C`, a lattice with complex
multiplication by the ring of integers of `ℚ(√-d)`. -/
noncomputable def negLogThetaPart : ℂ_[p]⟦X⟧ :=
  congruencePart (primeNorm d p - 1) (p + 1) C.negLogTheta

/-- The exponent `Ξ₁ = -g^♭(ϖ z) / c_ϖ`, where `g^♭ = C.negLogThetaPart` and
`c_ϖ = ϖ ^ (p + 1) / p`. -/
noncomputable def exponentSeries (ϖ : ℂ_[p]) : ℂ_[p]⟦X⟧ :=
  -(ϖ ^ (p + 1) / p)⁻¹ • rescale ϖ C.negLogThetaPart

lemma constantCoeff_negLogThetaPart : constantCoeff C.negLogThetaPart = (0 : ℂ_[p]) := by
  rw [← coeff_zero_eq_constantCoeff_apply, negLogThetaPart, congruencePart, coeff_mk,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_negLogTheta, ite_self]

/-- Let `g = -log θ` and let `g^♭` be its part in the degrees `≡ p + 1` mod `q_p - 1`. The series
`θ exp g^♭ = exp (g^♭ - g)`, with `exp a` written `expSubst a`, lies in the ring `𝒪[[y]]` of series
with coefficients of norm at most one in the Taylor series of `y = C.translatedY`. -/
lemma expSubst_negLogThetaPart_sub_mem :
    expSubst (C.negLogThetaPart - C.negLogTheta : ℂ_[p]⟦X⟧) ∈ C.integralSeriesRing := by
  -- Its `(q_p - 1)`-th power is the product of the `exp (ζ ^ (-p - 1) g(ζ z) - g(z))` over the
  -- `(q_p - 1)`-th roots of unity `ζ`, and `q_p - 1` is prime to `p`.
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ_[p] (primeNorm d p - 1)
  let term (i : ℕ) : ℂ_[p]⟦X⟧ :=
    (ζ ^ i)⁻¹ ^ (p + 1) • rescale (ζ ^ i) C.negLogTheta - C.negLogTheta
  have h_zero : constantCoeff (C.negLogThetaPart - C.negLogTheta : ℂ_[p]⟦X⟧) = 0 := by
    simp [constantCoeff_negLogThetaPart, constantCoeff_negLogTheta]
  have h_term_zero (i : ℕ) : constantCoeff (term i) = 0 := by
    simp [term, constantCoeff_negLogTheta]
  have h_sum : ∑ _i ∈ range (primeNorm d p - 1), (C.negLogThetaPart - C.negLogTheta) =
      ∑ i ∈ range (primeNorm d p - 1), term i := by
    rw [sum_sub_distrib, sum_sub_distrib, negLogThetaPart, congruencePart_eq_sum hζ, sum_const,
      card_range, ← Nat.cast_smul_eq_nsmul ℂ_[p], smul_inv_smul₀ (NeZero.ne _)]
  have h_prod : expSubst (C.negLogThetaPart - C.negLogTheta : ℂ_[p]⟦X⟧) ^ (primeNorm d p - 1) =
      ∏ i ∈ range (primeNorm d p - 1), expSubst (term i) := by
    rw [← expSubst_sum h_term_zero, ← h_sum, expSubst_sum fun _ ↦ h_zero, prod_const, card_range]
  refine C.isSeriesGenerator_translatedY.expSubst_mem_of_pow_mem
    (coprime_primeNorm_sub_one d p) h_zero ?_
  rw [h_prod]
  exact prod_mem fun i _ ↦ C.expSubst_rescale_sub_mem_of_pow_eq_one
    (by rw [pow_right_comm, hζ.pow_eq_one, one_pow])

/-- For `ϖ ≠ 0` the exponent `Ξ₁ = C.exponentSeries ϖ` satisfies `c_ϖ Ξ₁ = -g^♭(ϖ z)`, where
`c_ϖ = ϖ ^ (p + 1) / p` and `g^♭ = C.negLogThetaPart`. -/
lemma smul_exponentSeries {ϖ : ℂ_[p]} (hϖ0 : ϖ ≠ 0) :
    (ϖ ^ (p + 1) / p) • C.exponentSeries ϖ = -rescale ϖ C.negLogThetaPart := by
  simp [exponentSeries, smul_smul, hϖ0, (Fact.out : p.Prime).ne_zero]

/-- Let `θ` be the Taylor series of `C.θ`, the twisted translate of the sigma function of `C` by the
point `C.t` of order two, normalised to `θ(0) = 1` and read in `ℂ_p` by the embedding `ιₚ`. Let
`ϖ ≠ 0` have valuation at least `ρ_p = v(π_p) / (q_p - 1)`. Then `θ(ϖ z) = W exp (c_ϖ Ξ₁)` for a
series `W` over the integers of `ℂ_p`. -/
lemma exists_rescale_theta_eq_mul_expSubst {ϖ : ℂ_[p]} (hϖ0 : ϖ ≠ 0)
    (hϖ : ‖ϖ‖ ≤ p ^ (-varpiValuation d p)) :
    ∃ W : (valRingCp p)⟦X⟧, rescale ϖ (taylorVia ιₚ C.θ) =
      seriesToCp W * expSubst ((ϖ ^ (p + 1) / p) • C.exponentSeries ϖ) := by
  obtain ⟨W, hW⟩ := C.rescale_mem_range_seriesToCp hϖ C.expSubst_negLogThetaPart_sub_mem
  have h_flat_zero : constantCoeff (-C.negLogThetaPart : ℂ_[p]⟦X⟧) = 0 := by
    simp [constantCoeff_negLogThetaPart]
  have h_theta : taylorVia ιₚ C.θ = expSubst (C.negLogThetaPart - C.negLogTheta : ℂ_[p]⟦X⟧) *
      expSubst (-C.negLogThetaPart : ℂ_[p]⟦X⟧) := by
    rw [← expSubst_add _ (by simp [constantCoeff_negLogThetaPart, constantCoeff_negLogTheta])
      h_flat_zero, taylorVia_theta_eq_expSubst, ← sub_eq_add_neg, sub_sub_cancel_left]
  refine ⟨W, ?_⟩
  rw [h_theta, map_mul, hW, smul_exponentSeries C hϖ0, rescale_subst h_flat_zero, map_neg]

/-! ## Step 2: the functional equation -/

/-- The functional equation, modulo `π_p`, for the exponent `Ξ₁`. Let `p` be a prime that does not
split in `ℚ(√-d)`. The numbers `π_p = piPrime d p`, `q_p = primeNorm d p`,
`i₀ = leastFlatDegree d p`, `ρ_p = varpiValuation d p` are `√-d`, `p`, `2`, `1 / (2 p - 2)` if
`p = d`, and `p`, `p²`, `p + 1`, `1 / (p² - 1)` if `p` is inert. If `‖ϖ‖ = p ^ (-ρ_p)` and
`T(ϖ z) = ϖ Y` with `Y ∈ 𝒪[[z]]`, then there is `λ ∈ 𝒪` with
`(1 - π_p ^ n / q_p) [z ^ n] Ξ₁ ≡ λ [z ^ n] Y ^ i₀` modulo `π_p 𝒪` for all `n`. -/
lemma exists_functional_equation_exponentSeries {ϖ : ℂ_[p]} {Y : (valRingCp p)⟦X⟧}
    (hp : chiK d p ≠ 1) (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p))
    (hY : rescale ϖ C.formalParam = ϖ • seriesToCp Y) :
    ∃ l : valRingCp p, ∀ n : ℕ,
      ‖(1 - ιₚ (piPrime d p) ^ n / primeNorm d p) * coeff n (C.exponentSeries ϖ) -
        (l * coeff n (Y ^ leastFlatDegree d p)).val‖ ≤ ‖ιₚ (piPrime d p)‖ := by
  -- Combine the Frobenius congruence for `g` with `G ∈ 𝒪[[T]]`, take the `(q - 1)`-congruence
  -- part, rescale by `ϖ`, and divide by `-q c_ϖ`. On the right a unit `u` appears, and the
  -- remainder has the factor `ϖ ^ (q - 1)` of norm `‖π‖`.
  set π : ℂ_[p] := ιₚ (piPrime d p)
  set q : ℕ := primeNorm d p
  set i : ℕ := leastFlatDegree d p
  have hq0 : (q : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (one_lt_primeNorm d p).ne_bot
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_norm_eq_rpow hϖ
  have hϖπ : ‖ϖ‖ ^ (q - 1) = ‖π‖ := by rw [hϖ, norm_piPrime_eq_rpow_pow]
  obtain ⟨G, hG, h_frob⟩ := C.exists_negLogTheta_frobenius_congruence hp
  obtain ⟨G₀, rfl⟩ := C.mem_integralSeriesRing_iff_exists_subst_formalParam.1 hG
  obtain ⟨l, G', hG₀⟩ := exists_congruencePart_eq_smul_X_pow_add (leastFlatDegree_lt hp) G₀
  obtain ⟨V, hV⟩ := C.rescale_mem_range_seriesToCp hϖ.le
    (C.mem_integralSeriesRing_iff_exists_subst_formalParam.2 ⟨G', rfl⟩)
  have h_subst : HasSubst (C.formalParam : ℂ_[p]⟦X⟧) :=
    .of_constantCoeff_zero' C.constantCoeff_formalParam
  have h_part : (q : ℂ_[p]) • C.negLogThetaPart - rescale π C.negLogThetaPart =
      π • ((l : ℂ_[p]) • C.formalParam ^ i +
        C.formalParam ^ (i + (q - 1)) * subst C.formalParam (seriesToCp G')) := by
    have h_mod (n : ℕ) : n ≡ p + 1 [MOD primeNorm d p - 1] ↔ n ≡ i [MOD q - 1] :=
      ⟨(·.trans (add_one_modEq_leastFlatDegree hp)),
        (·.trans (add_one_modEq_leastFlatDegree hp).symm)⟩
    have h_rhs : congruencePart (q - 1) i (subst C.formalParam (seriesToCp G₀)) =
        (l : ℂ_[p]) • C.formalParam ^ i +
          C.formalParam ^ (i + (q - 1)) * subst C.formalParam (seriesToCp G') := by
      rw [congruencePart_subst_formalParam, hG₀, subst_add h_subst, subst_smul h_subst,
        subst_mul h_subst, subst_pow h_subst, subst_pow h_subst, subst_X h_subst]
    rw [← h_rhs]
    ext n
    have h_c : q * coeff n C.negLogTheta - π ^ n * coeff n C.negLogTheta =
        π * coeff n (subst C.formalParam (seriesToCp G₀)) := by
      simpa only [map_sub, coeff_smul, coeff_rescale, smul_eq_mul] using congrArg (coeff n) h_frob
    simp only [negLogThetaPart, congruencePart, map_sub, coeff_smul, coeff_rescale, coeff_mk,
      smul_eq_mul, mul_ite, mul_zero, h_mod]
    split_ifs
    · exact h_c
    · exact sub_zero _
  set R : (valRingCp p)⟦X⟧ := Y ^ (i + (q - 1)) * V
  have h_scaled : (q : ℂ_[p]) • rescale ϖ C.negLogThetaPart -
      rescale π (rescale ϖ C.negLogThetaPart) =
      (π * ϖ ^ i) • ((l : ℂ_[p]) • seriesToCp (Y ^ i) + ϖ ^ (q - 1) • seriesToCp R) := calc
    _ = rescale ϖ ((q : ℂ_[p]) • C.negLogThetaPart - rescale π C.negLogThetaPart) := by
      rw [map_sub, rescale_smul, rescale_rescale, rescale_rescale, mul_comm]
    _ = π • ((l : ℂ_[p]) • (ϖ • seriesToCp Y) ^ i +
          (ϖ • seriesToCp Y) ^ (i + (q - 1)) * seriesToCp V) := by
      simp only [h_part, map_mul, map_add, map_pow, rescale_smul, hY, hV]
    _ = _ := by
      simp only [R, map_mul, map_pow, smul_pow, smul_mul_assoc]
      module
  let u : ℂ_[p] := -(π * ϖ ^ i / (q * (ϖ ^ (p + 1) / p)))
  have hu : ‖u‖ = 1 := (norm_neg _).trans (norm_piPrime_mul_pow_leastFlatDegree_div hp hϖ0 hϖπ)
  refine ⟨⟨u, hu.le⟩ * l, fun n ↦ ?_⟩
  have h_scaled_coeff : q * coeff n (rescale ϖ C.negLogThetaPart) -
      π ^ n * coeff n (rescale ϖ C.negLogThetaPart) =
        π * ϖ ^ i * (l * (coeff n (Y ^ i)).val + ϖ ^ (q - 1) * (coeff n R).val) := by
    simpa only [map_sub, map_add, coeff_smul, coeff_rescale _ π, smul_eq_mul, coeff_seriesToCp]
      using congrArg (coeff n) h_scaled
  have h_coeff : (1 - π ^ n / q) * coeff n (C.exponentSeries ϖ) - u * l * (coeff n (Y ^ i)).val =
      u * ϖ ^ (q - 1) * (coeff n R).val := by
    simp only [exponentSeries, coeff_smul, smul_eq_mul, u]
    rw [← mul_right_inj' hq0]
    linear_combination (norm := field) -(ϖ ^ (p + 1) / p)⁻¹ * h_scaled_coeff
  calc ‖(1 - π ^ n / q) * coeff n (C.exponentSeries ϖ) - u * l * (coeff n (Y ^ i)).val‖
    _ = ‖π‖ * ‖(coeff n R).val‖ := by
      rw [h_coeff, norm_mul, norm_mul, hu, one_mul, norm_pow, hϖπ]
    _ ≤ ‖π‖ := mul_le_of_le_one_right (norm_nonneg π) (coeff n R).property

/-! ## Step 3: solving the functional equation -/

/-- Let `p` be non-split in `ℚ(√-d)`, that is, `chiK d p ≠ 1`, and `q_p = primeNorm d p`. For any
`ϖ`, the exponent `Ξ₁ = C.exponentSeries ϖ` has no terms below the degree
`i₀ = leastFlatDegree d p`, the least positive degree congruent to `p + 1` mod `q_p - 1`. -/
lemma coeff_exponentSeries_eq_zero_of_lt {ϖ : ℂ_[p]} (hp : chiK d p ≠ 1) {n : ℕ}
    (hn : n < leastFlatDegree d p) :
    coeff n (C.exponentSeries ϖ) = 0 := by
  have h_degree_lt : leastFlatDegree d p < primeNorm d p - 1 := leastFlatDegree_lt hp
  have h_not : ¬n ≡ p + 1 [MOD primeNorm d p - 1] := fun h ↦ by
    have h_modEq : n ≡ leastFlatDegree d p [MOD primeNorm d p - 1] :=
      h.trans (add_one_modEq_leastFlatDegree hp)
    exact hn.ne (h_modEq.eq_of_lt_of_lt (hn.trans h_degree_lt) h_degree_lt)
  simp [exponentSeries, negLogThetaPart, congruencePart, h_not]

/-- Let `p` be non-split (`chiK d p ≠ 1`), `π_p = piPrime d p`, `q_p = primeNorm d p`, and let
`a ∈ valRingCp p` satisfy `(1 - π_p ^ n / q_p) [z ^ n] Ξ₁ ≡ a` modulo `π_p` (through `ιₚ`) for the
exponent `Ξ₁ = C.exponentSeries ϖ`. Then `[z ^ n] Ξ₁ ≡ a` if `n > 2`, where the factor is `≡ 1`, and
if `n < leastFlatDegree d p`, where `Ξ₁` has no term of degree `n`. -/
lemma norm_coeff_exponentSeries_sub_le {ϖ : ℂ_[p]} (hp : chiK d p ≠ 1) {n : ℕ}
    (hn : n < leastFlatDegree d p ∨ 2 < n) {a : valRingCp p}
    (h_eq : ‖(1 - ιₚ (piPrime d p) ^ n / primeNorm d p) * coeff n (C.exponentSeries ϖ) - a.val‖ ≤
      ‖ιₚ (piPrime d p)‖) :
    ‖coeff n (C.exponentSeries ϖ) - a.val‖ ≤ ‖ιₚ (piPrime d p)‖ := by
  rcases hn with hn | hn
  · simpa only [C.coeff_exponentSeries_eq_zero_of_lt hp hn, mul_zero] using h_eq
  · exact norm_sub_le_of_norm_one_sub_mul_sub_le (norm_piPrime_lt_one d)
      (norm_piPrime_pow_div_le hp hn) a.property h_eq

/-- Let `p = d`, so that `π_p = piPrimeInt d` is `√-d`, `q_p = primeNorm d p` is `p` and
`ρ_p = varpiValuation d p` is `1 / (2 p - 2)`. Let `‖ϖ‖ = p ^ (-ρ_p)` and `T(ϖ z) = ϖ Y` with
`Y ∈ 𝒪[[z]]` and `[z ^ 2] Y ^ 2 ≡ 1` modulo `π_p`, and let `half` be the inverse of `2` in `𝒪`. Then
`Ξ₁` comes from a series `Ξ ∈ 𝒪[[z]]` by the inclusion `seriesToCp`, and `Ξ ≡ λ (Y ^ 2 - z ^ 2 / 2)`
modulo `π_p` for some `λ ∈ 𝒪`. -/
lemma exists_seriesToCp_eq_exponentSeries_of_ramified {ϖ : ℂ_[p]} {Y : (valRingCp p)⟦X⟧}
    (hd : p = d) (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p))
    (hY : rescale ϖ C.formalParam = ϖ • seriesToCp Y)
    (hY_two : piPrimeInt d ∣ 1 - coeff 2 (Y ^ 2)) {half : valRingCp p} (h_half : 2 * half = 1) :
    ∃ (Ξ : (valRingCp p)⟦X⟧) (l : valRingCp p),
      seriesToCp Ξ = C.exponentSeries ϖ ∧
      PowerSeries.C (piPrimeInt d) ∣ Ξ - l • (Y ^ 2 - half • X ^ 2) := by
  have h_chi : chiK d p = 0 := chiK_eq_zero_of_ramified hd
  have hp : chiK d p ≠ 1 := by simp [h_chi]
  have hq : primeNorm d p = p := by simp [primeNorm, h_chi]
  have h_degree : leastFlatDegree d p = 2 := ite_eq_left hd
  obtain ⟨l, hl⟩ : ∃ l : valRingCp p, ∀ n : ℕ,
      ‖(1 - ιₚ (piPrime d p) ^ n / primeNorm d p) * coeff n (C.exponentSeries ϖ) -
        (l * coeff n (Y ^ 2)).val‖ ≤ ‖ιₚ (piPrime d p)‖ := by
    simpa only [h_degree] using C.exists_functional_equation_exponentSeries hp hϖ hY
  suffices h_coeff : ∀ n : ℕ, ‖coeff n (C.exponentSeries ϖ) -
      (coeff n (l • (Y ^ 2 - half • X ^ 2))).val‖ ≤ ‖ιₚ (piPrime d p)‖ by
    obtain ⟨Ξ, hΞ, h_dvd⟩ := exists_seriesToCp_eq_and_C_dvd_sub (π := piPrimeInt d) h_coeff
    exact ⟨Ξ, l, hΞ, h_dvd⟩
  intro n
  rw [coeff_smul, map_sub, coeff_smul, coeff_X_pow, smul_eq_mul, smul_eq_mul]
  obtain rfl | hn := eq_or_ne n 2
  · -- In degree `2` the factor is `2`: from `2 x ≡ λ c` and `c ≡ 1` follows `x ≡ λ (c - 1 / 2)`.
    rw [ite_eq_left rfl, mul_one]
    set x : ℂ_[p] := coeff 2 (C.exponentSeries ϖ)
    set c : valRingCp p := coeff 2 (Y ^ 2)
    have h_factor : 1 - ιₚ (piPrime d p) ^ 2 / primeNorm d p = 2 := by
      rw [hq, piPrime_sq_of_ramified hd, neg_div, div_self (NeZero.ne _), sub_neg_eq_add,
        one_add_one_eq_two]
    have h_double : ‖2 * x - (l * c).val‖ ≤ ‖ιₚ (piPrime d p)‖ := by
      simpa only [h_factor] using hl 2
    have h_one : ‖(l * (1 - c)).val‖ ≤ ‖ιₚ (piPrime d p)‖ :=
      valRingCp.dvd_iff_norm_le.1 (hY_two.mul_left l)
    have h_eq : x - (l * (c - half)).val =
        half.val * ((2 * x - (l * c).val) + (l * (1 - c)).val) := by
      have h_coe : 2 * half.val = 1 := congrArg Subtype.val h_half
      push_cast
      linear_combination -(x - l * c) * h_coe
    rw [h_eq, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) half.property).trans
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h_double h_one))
  · rw [ite_eq_right hn, mul_zero, sub_zero]
    exact C.norm_coeff_exponentSeries_sub_le hp (by omega) (hl n)

end CMLattice

section Reduction
variable {p : ℕ} [Fact p.Prime] {d : ℕ} [PrimeSevenModEight d] [PadicPlace p]

/-- The reduction map `𝒪 → 𝒪 / π_p`, where `𝒪 = valRingCp p` and `π_p = piPrimeInt d`. -/
noncomputable abbrev reducePiPrime (d : ℕ) [PrimeSevenModEight d] :
    valRingCp p →+* valRingCp p ⧸ Ideal.span {piPrimeInt d} :=
  Ideal.Quotient.mk (Ideal.span {piPrimeInt d})

lemma reducePiPrime_eq_iff {a b : valRingCp p} :
    reducePiPrime d a = reducePiPrime d b ↔ piPrimeInt d ∣ a - b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

/-- The ring `𝒪 / π_p` is nontrivial, because `π_p` has norm less than one. -/
instance : Nontrivial (valRingCp p ⧸ Ideal.span {(piPrimeInt d : valRingCp p)}) := by
  rw [Ideal.Quotient.nontrivial_iff, Ne, Ideal.span_singleton_eq_top,
    isUnit_integer_iff_norm_eq_one]
  exact (norm_piPrime_lt_one d).ne

/-- The ring `𝒪 / π_p` has characteristic `p`, because `π_p` divides `p`. -/
instance : CharP (valRingCp p ⧸ Ideal.span {(piPrimeInt d : valRingCp p)}) p := by
  rw [CharP.charP_iff_prime_eq_zero Fact.out, ← map_natCast (reducePiPrime d),
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact piPrimeInt_dvd_natCast d

lemma map_reducePiPrime_eq_iff {F G : (valRingCp p)⟦X⟧} :
    F.map (reducePiPrime d) = G.map (reducePiPrime d) ↔ C (piPrimeInt d) ∣ F - G := by
  simp only [PowerSeries.ext_iff, coeff_map, reducePiPrime_eq_iff, C_dvd_iff_dvd_coeff, map_sub]

open scoped Classical in
/-- Let `Y ≡ ∑_j z ^ q_p ^ j` modulo `π_p`, where `q_p = primeNorm d p` and `π_p = piPrimeInt d`.
If the powers of `q_p` are the `p ^ i` with `i ∈ I`, then `Y` reduces to `∑_{i ∈ I} z ^ p ^ i`. -/
lemma map_reducePiPrime_eq_primePowerSeries {Y : (valRingCp p)⟦X⟧}
    (hY : ∀ n : ℕ, piPrimeInt d ∣ coeff n Y - if ∃ j : ℕ, n = primeNorm d p ^ j then 1 else 0)
    {I : Set ℕ} (hI : ∀ n : ℕ, (∃ j : ℕ, n = primeNorm d p ^ j) ↔ ∃ i ∈ I, n = p ^ i) :
    Y.map (reducePiPrime d) = primePowerSeries (valRingCp p ⧸ Ideal.span {piPrimeInt d}) p I := by
  ext n
  rw [coeff_map, reducePiPrime_eq_iff.2 (hY n), primePowerSeries, coeff_mk,
    apply_ite (reducePiPrime d), map_one, map_zero]
  exact if_congr (hI n) rfl rfl

open scoped Classical in
/-- Let `Y ≡ ∑_j z ^ q_p ^ j` modulo `π_p`, where `q_p = primeNorm d p` and `π_p = piPrimeInt d`.
If `q_p = p ^ 2`, as for inert `p`, then `Y ^ p Y` is congruent to the product of
`∑_{i odd} z ^ p ^ i` and `∑_{i even} z ^ p ^ i`. -/
lemma C_dvd_pow_sub_primePowerSeries_odd_mul_even {Y : (valRingCp p)⟦X⟧}
    (hY : ∀ n : ℕ, piPrimeInt d ∣ coeff n Y - if ∃ j : ℕ, n = primeNorm d p ^ j then 1 else 0)
    (hq : primeNorm d p = p ^ 2) :
    C (piPrimeInt d) ∣ Y ^ (p + 1) - primePowerSeries (valRingCp p) p {i : ℕ | Odd i} *
      primePowerSeries (valRingCp p) p {i : ℕ | Even i} := by
  have h_powers (n : ℕ) :
      (∃ j : ℕ, n = primeNorm d p ^ j) ↔ ∃ i ∈ {i : ℕ | Even i}, n = p ^ i := by
    simp [hq, ← pow_mul, even_iff_exists_two_mul]
  rw [← map_reducePiPrime_eq_iff, map_pow, map_reducePiPrime_eq_primePowerSeries hY h_powers,
    pow_succ, primePowerSeries_even_pow, map_mul, map_primePowerSeries, map_primePowerSeries]

open scoped Classical in
/-- Let `Y ≡ ∑_j z ^ q_p ^ j` modulo `π_p`, where `q_p = primeNorm d p` and `π_p = piPrimeInt d`.
If `q_p = p`, as for `p = d`, then `Y ^ 2` is congruent to the square of `∑_i z ^ p ^ i`. -/
lemma C_dvd_sq_sub_primePowerSeries_univ_sq {Y : (valRingCp p)⟦X⟧}
    (hY : ∀ n : ℕ, piPrimeInt d ∣ coeff n Y - if ∃ j : ℕ, n = primeNorm d p ^ j then 1 else 0)
    (hq : primeNorm d p = p) :
    C (piPrimeInt d) ∣ Y ^ 2 - primePowerSeries (valRingCp p) p Set.univ ^ 2 := by
  rw [← map_reducePiPrime_eq_iff, map_pow, map_pow, map_primePowerSeries,
    map_reducePiPrime_eq_primePowerSeries (I := Set.univ) hY fun n ↦ by simp [hq]]

/-!
## Step 4: the unit

The coefficient of `z ^ (p + 1)` in `Ξ₁` is a unit multiple of that of `z ^ (p - 1)` in `x`, which
is a unit by `New.CMLattice.norm_coeff_taylorVia_translatedX_eq_one`.
-/

/-- Let `d ≡ 7` mod `8` be a prime, `C` a lattice stable under the ring of integers of `ℚ(√-d)`, and
`p` a prime that is inert there. For `ϖ ≠ 0` the coefficient of `z ^ (p + 1)` in
`Ξ₁ = C.exponentSeries ϖ = -(p / ϖ ^ (p + 1)) g^♭(ϖ z)` has norm one. -/
lemma CMLattice.norm_coeff_exponentSeries_eq_one {p : ℕ} [Fact p.Prime] {d : ℕ}
    [PrimeSevenModEight d] (C : CMLattice d) [PadicPlace p] {ϖ : ℂ_[p]}
    (h_inert : chiK d p = -1) (hϖ0 : ϖ ≠ 0) :
    ‖coeff (p + 1) (C.exponentSeries ϖ)‖ = 1 := by
  have h_exponent : coeff (p + 1) (C.exponentSeries ϖ) = -(p * coeff (p + 1) C.negLogTheta) := by
    rw [exponentSeries, coeff_smul, coeff_rescale, negLogThetaPart, congruencePart, coeff_mk,
      ite_eq_left (Nat.ModEq.refl _), smul_eq_mul]
    field
  -- Up to its constant term, `x` is the second derivative of `g`.
  have h_deriv : coeff (p - 1) (taylorVia ιₚ C.translatedX) =
      p * coeff (p + 1) C.negLogTheta * (p + 1 : ℕ) := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := Nat.exists_eq_add_of_le' (Fact.out : p.Prime).two_le
    have h_coeff := congrArg (coeff (k + 1)) C.derivative_derivative_negLogTheta
    rw [map_add, coeff_succ_C, zero_add, coeff_derivative, coeff_derivative] at h_coeff
    simp only [Nat.add_one_sub_one, ← h_coeff]
    push_cast
    ring
  have h_unit : ‖((p + 1 : ℕ) : ℂ_[p])‖ = 1 :=
    (Nat.coprime_self_add_right.2 (Nat.coprime_one_right p)).norm_natCast_eq_one ℂ_[p]
  calc ‖coeff (p + 1) (C.exponentSeries ϖ)‖
    _ = ‖p * coeff (p + 1) C.negLogTheta * ((p + 1 : ℕ) : ℂ_[p])‖ := by
      rw [h_exponent, norm_neg, norm_mul _ ((p + 1 : ℕ) : ℂ_[p]), h_unit, mul_one]
    _ = 1 := by rw [← h_deriv, C.norm_coeff_taylorVia_translatedX_eq_one h_inert]

lemma isUnit_of_piPrimeInt_dvd_sub {a b : valRingCp p} (ha : IsUnit a)
    (h_dvd : piPrimeInt d ∣ a - b) : IsUnit b := by
  have h_local : IsLocalHom (reducePiPrime (p := p) d) :=
    .of_surjective _ Ideal.Quotient.mk_surjective
  rw [← isUnit_map_iff (reducePiPrime d), ← reducePiPrime_eq_iff.2 h_dvd]
  exact ha.map _

end Reduction

open WithPiTopology

variable {p : ℕ} [Fact p.Prime]

/-- For any set `S` of exponents and any coefficients `λ_{e j}` in the valuation ring of `ℂ_p`, the
family `λ_{e j} (X ^ p ^ e X) ^ p ^ j` over `e ∈ S` and `j ∈ ℕ` is summable in the topology of
coefficientwise convergence. -/
lemma summable_smul_X_pow_mul_X_pow (S : Set ℕ) (l : ℕ → ℕ → valRingCp p) :
    Summable fun x : S × ℕ ↦
      l x.1 x.2 • (X ^ p ^ (x.1 : ℕ) * X : (valRingCp p)⟦X⟧) ^ p ^ x.2 := by
  have h_order (e : ℕ) :
      ((p ^ e + 1 : ℕ) : ℕ∞) ≤ MvPowerSeries.order (X ^ p ^ e * X : (valRingCp p)⟦X⟧) := by
    rw [← pow_succ]
    exact MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ constantCoeff_X
  exact summable_smul_pow_pow (Fact.out : p.Prime).one_lt h_order S l

variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) [PadicPlace p]

open scoped Classical in
/-- The exponent modulo `π_p` at an inert prime. Let `p` be inert in `ℚ(√-d)`, that is,
`chiK d p = (p / d) = -1`, so that `π_p = piPrimeInt d` is `p`, `q_p = primeNorm d p` is `p²` and
`ρ_p = varpiValuation d p` is `1 / (p² - 1)`. Let `‖ϖ‖ = p ^ (-ρ_p)` and `T(ϖ z) = ϖ Y` with
`Y ∈ 𝒪[[z]]` and `Y ≡ ∑_j z ^ q_p ^ j` modulo `π_p`. Then `Ξ₁` comes from a series `Ξ ∈ 𝒪[[z]]` by
the inclusion `seriesToCp`, and `Ξ ≡ ∑_{e odd} ∑_j λ (z ^ p ^ e z) ^ p ^ j` modulo `π_p` for a unit
`λ` of `𝒪`. -/
lemma CMLattice.exists_eq_exponentSeries_dvd_sub_tsum_of_inert {ϖ : ℂ_[p]} {Y : (valRingCp p)⟦X⟧}
    (h_inert : chiK d p = -1) (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p))
    (hTY : rescale ϖ C.formalParam = ϖ • seriesToCp Y)
    (hY : ∀ n : ℕ, piPrimeInt d ∣ coeff n Y - if ∃ j : ℕ, n = primeNorm d p ^ j then 1 else 0) :
    ∃ (Ξ : (valRingCp p)⟦X⟧) (l : valRingCp p),
      seriesToCp Ξ = C.exponentSeries ϖ ∧
      PowerSeries.C (piPrimeInt d) ∣
        Ξ - ∑' x : {e : ℕ | Odd e} × ℕ, l • (X ^ p ^ (x.1 : ℕ) * X) ^ p ^ x.2 ∧
      IsUnit l := by
  have hp : chiK d p ≠ 1 := by simp [h_inert]
  have hp_ne_two : p ≠ 2 := ne_two_of_chiK_ne_one hp
  have hpd_ne : p ≠ d := fun hd ↦ by simp [chiK_eq_zero_of_ramified hd] at h_inert
  have hp_two_le : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h_degree : leastFlatDegree d p = p + 1 := ite_eq_right hpd_ne
  obtain ⟨l, hl⟩ := C.exists_functional_equation_exponentSeries hp hϖ hTY
  obtain ⟨Ξ, hΞ, hΞ_congr⟩ :=
    exists_seriesToCp_eq_and_C_dvd_sub (π := piPrimeInt d) (G := l • Y ^ (p + 1)) fun n ↦
      C.norm_coeff_exponentSeries_sub_le hp (by omega)
        (by simpa only [h_degree, coeff_smul, smul_eq_mul] using hl n)
  set P : (valRingCp p)⟦X⟧ := primePowerSeries (valRingCp p) p {i : ℕ | Odd i} *
    primePowerSeries (valRingCp p) p {i : ℕ | Even i}
  have hY_pow_congr : PowerSeries.C (piPrimeInt d) ∣ Y ^ (p + 1) - P :=
    C_dvd_pow_sub_primePowerSeries_odd_mul_even hY (by rw [primeNorm, ite_eq_left h_inert])
  have h_dvd : PowerSeries.C (piPrimeInt d) ∣ Ξ - l • P :=
    dvd_sub_smul_of_dvd_sub hΞ_congr hY_pow_congr
  refine ⟨Ξ, l, hΞ, ?_, ?_⟩
  · rwa [(hasSum_primePowerSeries_odd_mul_even hp_ne_two l).tsum_eq]
  · -- The number `λ` is congruent to the coefficient of `z ^ (p + 1)` in `Ξ`.
    have h_coeff : coeff (p + 1) P = 1 := by
      simpa using coeff_primePowerSeries_odd_mul_even (R := valRingCp p) hp_ne_two odd_one 0
    have h_unit : IsUnit (coeff (p + 1) Ξ) := by
      rw [isUnit_integer_iff_norm_eq_one, ← coeff_seriesToCp, hΞ]
      exact C.norm_coeff_exponentSeries_eq_one h_inert (ne_zero_of_norm_eq_rpow hϖ)
    refine isUnit_of_piPrimeInt_dvd_sub (d := d) h_unit ?_
    simpa only [map_sub, coeff_smul, h_coeff, smul_eq_mul, mul_one]
      using (C_dvd_iff_dvd_coeff _ _).1 h_dvd (p + 1)

open scoped Classical in
/-- The exponent modulo `π_p` at the ramified prime. Let `p = d`, so that `π_p = piPrimeInt d` is
`√-d`, `q_p = primeNorm d p` is `p` and `ρ_p = varpiValuation d p` is `1 / (2 p - 2)`. Let
`‖ϖ‖ = p ^ (-ρ_p)` and `T(ϖ z) = ϖ Y` with `Y ∈ 𝒪[[z]]` and `Y ≡ ∑_j z ^ q_p ^ j` modulo `π_p`, and
let `half` be the inverse of `2` in `𝒪`. Then `Ξ₁` comes from a series `Ξ ∈ 𝒪[[z]]` by the inclusion
`seriesToCp`, and there is `λ ∈ 𝒪` with `Ξ ≡ ∑_e ∑_j λ_{e j} (z ^ p ^ e z) ^ p ^ j` modulo `π_p`,
where `λ_{0 0} = λ / 2`, `λ_{0 j} = λ` for `j ≥ 1`, and `λ_{e j} = 2 λ` for `e ≥ 1`. -/
lemma CMLattice.exists_exponentSeries_tsum_of_ramified {ϖ : ℂ_[p]} {Y : (valRingCp p)⟦X⟧}
    (hd : p = d) (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p))
    (hTY : rescale ϖ C.formalParam = ϖ • seriesToCp Y)
    (hY : ∀ n : ℕ, piPrimeInt d ∣ coeff n Y - if ∃ j : ℕ, n = primeNorm d p ^ j then 1 else 0)
    {half : valRingCp p} (h_half : 2 * half = 1) :
    ∃ (Ξ : (valRingCp p)⟦X⟧) (l : valRingCp p),
      seriesToCp Ξ = C.exponentSeries ϖ ∧
      PowerSeries.C (piPrimeInt d) ∣ Ξ - ∑' x : ↥(Set.univ : Set ℕ) × ℕ,
        (if (x.1 : ℕ) = 0 then if x.2 = 0 then l * half else l else 2 * l) •
          (X ^ p ^ (x.1 : ℕ) * X) ^ p ^ x.2 := by
  have h_chi : chiK d p = 0 := chiK_eq_zero_of_ramified hd
  have hp : chiK d p ≠ 1 := by simp [h_chi]
  have hq : primeNorm d p = p := by simp [primeNorm, h_chi]
  have hp_ne_two : p ≠ 2 := ne_two_of_chiK_ne_one hp
  set P : (valRingCp p)⟦X⟧ := primePowerSeries (valRingCp p) p Set.univ
  have hY_sq_congr : PowerSeries.C (piPrimeInt d) ∣ Y ^ 2 - P ^ 2 :=
    C_dvd_sq_sub_primePowerSeries_univ_sq hY hq
  have h_coeff : coeff 2 (P ^ 2) = 1 := by
    simpa using coeff_primePowerSeries_univ_sq (R := valRingCp p) hp_ne_two 0 0
  have hY_two : piPrimeInt d ∣ 1 - coeff 2 (Y ^ 2) := by
    rw [dvd_sub_comm, ← h_coeff, ← map_sub]
    exact (C_dvd_iff_dvd_coeff _ _).1 hY_sq_congr 2
  obtain ⟨Ξ, l, hΞ, hΞ_congr⟩ : ∃ (Ξ : (valRingCp p)⟦X⟧) (l : valRingCp p),
      seriesToCp Ξ = C.exponentSeries ϖ ∧
      PowerSeries.C (piPrimeInt d) ∣ Ξ - l • (Y ^ 2 - half • X ^ 2) :=
    C.exists_seriesToCp_eq_exponentSeries_of_ramified hd hϖ hTY hY_two h_half
  refine ⟨Ξ, l, hΞ, ?_⟩
  rw [(hasSum_primePowerSeries_univ_sq_sub hp_ne_two h_half l).tsum_eq]
  exact dvd_sub_smul_of_dvd_sub hΞ_congr (by rwa [sub_sub_sub_cancel_right])

/-- Let `d ≡ 7` mod `8` be a prime, `C` a lattice with complex multiplication by the ring of
integers of `ℚ(√-d)`, and `p` a prime that does not split there. There are `ϖ ∈ ℂ_p` with
`‖ϖ‖ = p ^ (-ρ_p)` (where `‖p‖ = p⁻¹`), series `Ξ`, `W` over the ring `𝒪 = valRingCp p` of integers
of `ℂ_p` with `Ξ(0) = 0`, and numbers `λ_{e j} ∈ 𝒪` such that `θ(ϖ z) = W exp (c_ϖ Ξ)` and
`Ξ ≡ ∑_e ∑_j λ_{e j} (z ^ p ^ e z) ^ p ^ j` modulo `π_p`. Here `θ` is the Taylor series of the theta
function of `C`, read in `ℂ_p` by the embedding `ιₚ` that `PadicPlace p` fixes,
`c_ϖ = ϖ ^ (p + 1) / p`, `exp a` is written `expSubst a`, and `e` runs over
`I_p° = partnerExponents d p`: the odd numbers, or all if `p = d`. If `p` is inert, the `λ_{e 0}`
with `e` odd are units. -/
theorem CMLattice.exists_exponent_tsum (hp : chiK d p ≠ 1) :
    ∃ (ϖ : ℂ_[p]) (Ξ W : (valRingCp p)⟦X⟧) (l : ℕ → ℕ → valRingCp p),
      ‖ϖ‖ = p ^ (-varpiValuation d p) ∧
      constantCoeff Ξ = 0 ∧
      rescale ϖ (taylorVia ιₚ C.θ) = seriesToCp W * expSubst ((ϖ ^ (p + 1) / p) • seriesToCp Ξ) ∧
      PowerSeries.C (piPrimeInt d) ∣ Ξ - ∑' x : partnerExponents d p × ℕ,
        l x.1 x.2 • (X ^ p ^ (x.1 : ℕ) * X) ^ p ^ x.2 ∧
      (chiK d p = -1 → ∀ e : ℕ, Odd e → IsUnit (l e 0)) := by
  -- Scale by `ϖ` so that `Y = T(ϖ z) / ϖ` is integral, and split `exp (c_ϖ Ξ₁)` off `θ(ϖ z)`.
  obtain ⟨ϖ, Y, hϖ, hTY, -, hY⟩ := C.exists_scaled_formalParam (p := p)
  obtain ⟨W, hW⟩ := C.exists_rescale_theta_eq_mul_expSubst (ne_zero_of_norm_eq_rpow hϖ) hϖ.le
  have h_zero {Ξ : (valRingCp p)⟦X⟧} (hΞ : seriesToCp Ξ = C.exponentSeries ϖ) :
      constantCoeff Ξ = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, ← ZeroMemClass.coe_eq_zero, ← coeff_seriesToCp, hΞ,
      C.coeff_exponentSeries_eq_zero_of_lt hp (leastFlatDegree_pos d p)]
  rcases ramified_or_inert hp with ⟨hd, -⟩ | ⟨-, h_inert, -⟩
  · -- Take `λ_{0 0} = λ / 2`, `λ_{0 j} = λ` for `j ≥ 1`, and `λ_{e j} = 2 λ` for `e ≥ 1`.
    have h_all : partnerExponents d p = Set.univ := by simp [partnerExponents, hd]
    have h_not_inert : chiK d p ≠ -1 := by simp [chiK_eq_zero_of_ramified hd]
    have h_coprime : p.Coprime 2 :=
      (Nat.coprime_primes Fact.out Nat.prime_two).2 (ne_two_of_chiK_ne_one hp)
    have h_two : IsUnit ((2 : ℕ) : valRingCp p) :=
      isUnit_integer_iff_norm_eq_one.2 (h_coprime.norm_natCast_eq_one ℂ_[p])
    obtain ⟨half, h_half⟩ : ∃ half : valRingCp p, 2 * half = 1 := h_two.exists_right_inv
    obtain ⟨Ξ, l, hΞ, h_dvd⟩ := C.exists_exponentSeries_tsum_of_ramified hd hϖ hTY hY h_half
    let coef (e j : ℕ) : valRingCp p := if e = 0 then if j = 0 then l * half else l else 2 * l
    rw [← hΞ] at hW
    refine ⟨ϖ, Ξ, W, coef, hϖ, h_zero hΞ, hW, ?_, fun h_inert ↦ absurd h_inert h_not_inert⟩
    rwa [h_all]
  · -- Take `λ_{e j} = λ`.
    obtain ⟨Ξ, l, hΞ, h_dvd, h_unit⟩ :=
      C.exists_eq_exponentSeries_dvd_sub_tsum_of_inert h_inert hϖ hTY hY
    rw [← hΞ] at hW
    refine ⟨ϖ, Ξ, W, fun _ _ ↦ l, hϖ, h_zero hΞ, hW, ?_, fun _ _ _ ↦ h_unit⟩
    rwa [partnerExponents_of_inert h_inert]

end New
end
end

/-!
# The normal form of theta products at non-split primes

The file treats products of theta functions at a prime `p` that is not split in `K = ℚ(√-d)`. Here
`θ` is the theta function of the CM curve, `y` the parameter `C.translatedY` of the curve, composed
with the forms `u† z`, and `E` is `K` with a root of unity adjoined.

The vectors `u` of `Eⁿ` form a resolution of the identity and are integral above `p`. The partner of
an infinite place `τ` of `E` is `-p ^ e τ`, and `Γ_e` is the coupling of the places with their
partners. Congruences modulo `π_p` between powers at a place and conjugation at its partner lead to
a normal form for `∏ θ(u_j† z) ^ m j` times an integral series in the `y(u† z)`.

## Main definitions and results

* `New.Parameters.norm_pow_sub_conj_partner_le`: for `e` in `I_p°`, modulo `π_p`, the `p ^ e`-th
  power at a place `τ` is complex conjugation at its partner `-p ^ e τ`.
* `New.Parameters.piPrimeInt_dvd_sum_linearSeries_sub_coupling`: at a non-split `p`, for a
  resolution of the identity by vectors `u` integral above `p`, the sum
  `∑ m j * (u_j† z) ^ p ^ e * (u_j† z)` is the coupling `Γ_e` modulo `π_p` for `e` in `I_p°`.
* `New.Parameters.exists_hasNormalForm`: at a non-split prime `p`, for a resolution of the identity
  by vectors `u` integral above `p`, the product `∏ θ(u_j† z) ^ m j` times an integral series in the
  `y(u† z)` has the normal form.

Notions from other files:
* `New.piPrime`, `New.piPrimeInt`: the number `π_p`, which is `√-d` if `p = d` and `p` otherwise, in
  `ℂ` and in the valuation ring (through the embedding `ιₚ : ℂ → ℂ_p`).
* `New.chiK`, `New.partnerExponents`: the character `χ_K`, with `χ_K(p) ≠ 1` at non-split `p`, and
  the set `I_p°` of exponents `e`: the odd ones if `p` is inert, all if `p = d`, none if `p` splits.
* `New.IsResolution`: the vectors `u` with multiplicities `m` satisfy `z = ∑ m j (u_j† z) u_j`,
  where `u† z = ∑ conj (τ(u_c)) z_(τ,c)`.
* `New.coupling`, `New.HasNormalForm`: `Γ_e = ∑ z_(τ,c) ^ p ^ e * z_(τ',c)` with `τ'` the partner
  of `τ`, and `F(ϖ z) = W exp (c_ϖ ∑ λ_{e j} Γ_e ^ p ^ j)` with `W` integral.
-/

@[expose] public section

/-! ## Substitution of a linear form -/

section LinearForm

open Finset MvPowerSeries Nat Finsupp

namespace New

variable {p : ℕ} [Fact p.Prime] {X : Type} [Fintype X]

open MvPolynomial

/-- The coefficient of `z ^ D` in `g(∑ c_x z_x)` is `c ^ D g⁽ⁿ⁾(0) / D!` with `n = |D|`, where
`c ^ D = ∏ c_x ^ D_x`, `D! = ∏ D_x!` and `g⁽ⁿ⁾(0)` is `n!` times the `n`-th coefficient of `g`. -/
@[simp] lemma coeff_subst_linearSeries {D : X →₀ ℕ} (c : X → ℂ_[p]) (g : PowerSeries ℂ_[p]) :
    (g.subst (linearSeries c)).coeff D =
      (∏ x : X, c x ^ D x) * (D.degree ! * g.coeff D.degree) / ∏ x : X, ((D x)! : ℂ_[p]) := by
  -- Apply the chain rule to the jet along the monomial `z ^ D`, and evaluate both jets.
  have h_monomial : linSubst (fun _ : Unit ↦ c) (monomial D 1) =
      (∏ x : X, c x ^ D x) • MvPolynomial.X () ^ D.degree := by
    simp only [linSubst, aeval_monomial]
    simp [prod_fintype, smul_pow, prod_smul, prod_pow_eq_pow_sum, degree_eq_sum]
  have h_chain : jet ℂ_[p] (monomial D 1) (g.subst (linearSeries c)) =
      jet ℂ_[p] (linSubst (fun _ : Unit ↦ c) (monomial D 1)) g :=
    jet_subst_linearSeries (fun _ : Unit ↦ c) (monomial D 1) g
  rw [h_monomial, X_pow_eq_monomial, map_smul, LinearMap.smul_apply, jet_monomial,
    jet_monomial] at h_chain
  rw [eq_div_iff (Finset.prod_ne_zero_iff.2 fun x _ ↦ mod_cast factorial_ne_zero (D x)), mul_comm]
  simpa [prod_fintype, PowerSeries.coeff] using h_chain

/-- Scaling all variables of `g(∑ c_x z_x)` by `a` is scaling the variable of `g` by `a`. -/
@[simp] lemma rescale_subst_linearSeries {a : ℂ_[p]} (c : X → ℂ_[p]) (g : PowerSeries ℂ_[p]) :
    rescale (fun _ : X ↦ a) (g.subst (linearSeries c)) = (g.rescale a).subst (linearSeries c) := by
  ext D
  simp [coeff_subst_linearSeries, prod_pow_eq_pow_sum, degree_eq_sum, field]

end New

end LinearForm

/-!
## Partners of places and couplings

The congruence for powers at partners compares two ring maps on generators of `𝓞 E`. It turns the
identity `∑ m_j τ(u_{j,c}) (u_j† z) = z_(τ,c)` into the congruence for the coupling.
-/

section Partner

open MvPowerSeries ComplexConjugate NumberField Finset

namespace New

/-- An element of the valuation ring of `ℂ_p` is divisible by `π_p` (`√-d` if `p = d`, else `p`)
exactly when its norm is at most that of `π_p`. -/
lemma piPrimeInt_dvd_iff {d p : ℕ} [PrimeSevenModEight d] [Fact p.Prime] [PadicPlace p]
    {x : valRingCp p} : piPrimeInt d ∣ x ↔ ‖(x : ℂ_[p])‖ ≤ ‖ιₚ (piPrime d p)‖ :=
  valRingCp.dvd_iff_norm_le

namespace Parameters

/-- The partner `-p ^ e τ` of an infinite place `τ` of `E`. Here `P` fixes the prime `d` and the
modulus `q₀`, and `E = P.E s` is `K = ℚ(√-d)` with a root of unity of order `q₁ = P.q₁ s` adjoined,
`s` being the level in the tower of these fields. The infinite places `P.Φ s` of `E` form the group
`Gal(E/K) = (ℤ/q₁)ˣ`, and the partner is the product of `τ` with `P.placeOfInt s (-p ^ e)`, the
place of the class of `-p ^ e` modulo `q₁` (the identity if this class is not a unit). -/
noncomputable def partner (P : Parameters) (s p e : ℕ) (τ : P.Φ s) : P.Φ s :=
  P.placeOfInt s (-p ^ e) * τ

/-- Let `p` be non-split in `K = ℚ(√-d)` (`χ_K(p) ≠ 1`) and let `ϖ` have valuation
`ρ_p = varpiValuation P.d p`, which is `1 / (p² - 1)` if `p` is inert and `1 / (2 p - 2)` if
`p = d`. Then `c_ϖ π_p` has valuation `1 / (p - 1)`, where `c_ϖ = ϖ ^ (p + 1) / p` and `π_p` is
`√-d` if `p = d` and `p` otherwise. -/
lemma norm_pow_succ_div_mul_piPrimeInt (P : Parameters) {p : ℕ} [Fact p.Prime] [PadicPlace p]
    (hp : chiK P.d p ≠ 1) {ϖ : ℂ_[p]} (hϖ : ‖ϖ‖ = p ^ (-varpiValuation P.d p)) :
    ‖ϖ ^ (p + 1) / p * (piPrimeInt P.d : valRingCp p)‖ = p ^ (-(1 / (p - 1)) : ℝ) := by
  -- The valuations of `ϖ ^ (p + 1)`, `1 / p` and `π_p` add up to `1 / (p - 1)`.
  have hp_gt : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have h_exponent :
      -varpiValuation P.d p * (p + 1) + 1 + -piPrimeValuation P.d p = -(1 / (p - 1)) := by
    have hp_sub : (p : ℝ) - 1 ≠ 0 := by linarith
    obtain ⟨rfl, -⟩ | ⟨h_ne, h_split | h_inert⟩ := chiK_cases P.d p
    · grind [varpiValuation_self, piPrimeValuation_self]
    · exact absurd h_split hp
    · have hp_sq : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
      rw [varpiValuation_of_inert h_inert, piPrimeValuation_of_ne h_ne]
      field
  rw [norm_mul, norm_div, norm_pow, hϖ, norm_p_eq_inv, norm_piPrimeInt, ← h_exponent,
    Real.rpow_add (by positivity), Real.rpow_add (by positivity), Real.rpow_one, div_inv_eq_mul,
    ← Real.rpow_mul_natCast (by positivity), Nat.cast_add, Nat.cast_one]

/-- Let `E = P.E s` be `K = ℚ(√-d)` (`d = P.d`) with a root of unity of order `q₁ = P.q₁ s`
adjoined, `s` being the level in the tower of these fields. Let `e` be in
`I_p° = partnerExponents P.d p`. Let `τ : P.Φ s` be an infinite place of `E`, and
`τ' = -p ^ e τ = P.partner s p e τ` its partner: the product of `τ` with the class of `-p ^ e` in
the group `Gal(E/K) = (ℤ/q₁)ˣ` of places. Then `τ(α) ^ p ^ e ≡ conj (τ'(α))` modulo `π_p` for `α` in
`𝓞 E`. -/
lemma norm_pow_sub_conj_partner_le {P : Parameters} {s p : ℕ} [Fact p.Prime] [PadicPlace p] {e : ℕ}
    (he : e ∈ partnerExponents P.d p) (τ : P.Φ s) (α : 𝓞 (P.E s)) :
    ‖ιₚ (Φ τ α) ^ p ^ e - ιₚ (conj (Φ (P.partner s p e τ) α))‖ ≤ ‖ιₚ (piPrime P.d p)‖ := by
  -- Both sides are ring maps to `𝒪 / π_p`. By `forall_map_galOfPlaceInt_eq_pow_iff` it suffices
  -- that they agree at the root of unity, which holds by the choice of the partner, and at `√-d`.
  let toValRing : 𝓞 (P.E s) →+* valRingCp p :=
    ((ιₚ.comp (Φ τ)).comp (algebraMap (𝓞 (P.E s)) (P.E s))).codRestrict (valRingCp p)
      fun x ↦ (norm_ringOfIntegers_le (ιₚ.comp (Φ τ)) x :)
  have h_coe (x : 𝓞 (P.E s)) : (toValRing x : ℂ_[p]) = ιₚ (Φ τ x) := rfl
  let modPiPrime : valRingCp p →+* valRingCp p ⧸ Ideal.span {piPrimeInt P.d} := reducePiPrime P.d
  have h_mod_eq_zero (x : valRingCp p) :
      modPiPrime x = 0 ↔ ‖(x : ℂ_[p])‖ ≤ ‖ιₚ (piPrime P.d p)‖ := by
    rw [Ideal.Quotient.eq_zero_iff_dvd, piPrimeInt_dvd_iff]
  have h_sqrt :
      (chiK P.d p : valRingCp p ⧸ Ideal.span {piPrimeInt P.d}) ^ e * (-1 : ℤ) *
        modPiPrime (toValRing (P.sqrtNegDInE s)) = modPiPrime (toValRing (P.sqrtNegDInE s)) := by
    obtain h_eq | ⟨h_inert, h_odd⟩ := mem_partnerExponents.1 he
    · -- For `p = d` the image of `√-d` is `π_p`; for inert `p` the symbol is `-1` and `e` is odd.
      have h_zero : modPiPrime (toValRing (P.sqrtNegDInE s)) = 0 := by
        rw [h_mod_eq_zero, h_coe, coe_sqrtNegDInE, phi_algebraMap, QuadField.sqrtNegD_coe, piPrime,
          ite_eq_left h_eq]
      rw [h_zero, mul_zero]
    · simp [h_inert, h_odd.neg_one_pow]
  have h_frob : modPiPrime (toValRing (galOfPlaceInt (P.placeOfInt s (-p ^ e)) (star α))) =
      modPiPrime (toValRing α) ^ p ^ e := by
    have hp_not_dvd : ¬p ∣ P.q₁ s := fun h_dvd ↦
      chiK_ne_one_of_mem_partnerExponents he (P.chiK_eq_one_of_dvd Fact.out h_dvd)
    simpa using (forall_map_galOfPlaceInt_eq_pow_iff hp_not_dvd (modPiPrime.comp toValRing) e
      (.inr ⟨rfl, rfl⟩ : IsIdOrConjWithSign (starRingAut (R := 𝓞 (P.E s))) (-1))).2
      ⟨by rw [neg_one_mul], h_sqrt⟩ (star α)
  have h_partner : (toValRing (galOfPlaceInt (P.placeOfInt s (-p ^ e)) (star α)) : ℂ_[p]) =
      ιₚ (conj (Φ (P.partner s p e τ) α)) := by
    rw [h_coe, coe_galOfPlaceInt, ← phi_mul, coe_star_ringOfIntegers, map_star_complex, partner,
      mul_comm τ, starRingEnd_apply]
  rw [← h_partner]
  exact (h_mod_eq_zero (toValRing α ^ p ^ e - _)).1 (by rw [map_sub, map_pow, h_frob, sub_self])

/-- Let `E = P.E s` be `K = ℚ(√-d)` (`d = P.d`) with a root of unity of order `q₁ = P.q₁ s`
adjoined, `s` being the level in the tower of these fields. Let `e` be in
`I_p° = partnerExponents P.d p`. Let `τ : P.Φ s` be an infinite place of `E`, and
`τ' = -p ^ e τ = P.partner s p e τ` its partner: the product of `τ` with the class of `-p ^ e` in
the group `Gal(E/K) = (ℤ/q₁)ˣ` of places. Then `conj (τ(y)) ^ p ^ e ≡ τ'(y)` modulo `π_p` for `y` in
`E` integral at all primes above `p`. -/
lemma norm_conj_pow_sub_partner_le {P : Parameters} {s p : ℕ} [Fact p.Prime] [PadicPlace p] {e : ℕ}
    (he : e ∈ partnerExponents P.d p) (τ : P.Φ s) {y : P.E s} (hy : IsIntegralAbove p y) :
    ‖ιₚ (conj (Φ τ y)) ^ p ^ e - ιₚ (Φ (P.partner s p e τ) y)‖ ≤ ‖ιₚ (piPrime P.d p)‖ := by
  -- Write `y = α / N` with `N` prime to `p`, use the congruence for `conj α`, and cancel the unit
  -- `N ^ p ^ e ≡ N`.
  obtain ⟨N, α, hN, hα⟩ : ∃ (N : ℕ) (α : 𝓞 (P.E s)), p.Coprime N ∧ N * y = α := hy.exists_mul_eq
  let a : valRingCp p := ⟨ιₚ (conj (Φ τ y)), hy.norm_conj_le_one _⟩
  let b : valRingCp p := ⟨ιₚ (Φ (P.partner s p e τ) y), hy.norm_le_one (ιₚ.comp _)⟩
  have h_int : piPrimeInt P.d ∣ (N * a) ^ p ^ e - N * b := by
    simpa [piPrimeInt_dvd_iff, a, b, ← hα, coe_star_ringOfIntegers, map_star_complex] using
      norm_pow_sub_conj_partner_le he τ (star α)
  have h_fermat : piPrimeInt P.d ∣ (N : valRingCp p) ^ p ^ e - N := by
    have h_mod : (p : ℤ) ∣ (N : ℤ) ^ p ^ e - N :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simp [ZMod.pow_card_pow])
    exact (piPrimeInt_dvd_natCast P.d).trans
      (mod_cast map_dvd (Int.castRingHom (valRingCp p)) h_mod)
  have h_unit : IsUnit ((N : valRingCp p) ^ p ^ e) :=
    (isUnit_integer_iff_norm_eq_one.2 (hN.norm_natCast_eq_one ℂ_[p])).pow _
  have h_mul : piPrimeInt P.d ∣ (N : valRingCp p) ^ p ^ e * (a ^ p ^ e - b) := by
    have h_split : (N : valRingCp p) ^ p ^ e * (a ^ p ^ e - b) =
        (N * a) ^ p ^ e - N * b - (N ^ p ^ e - N) * b := by ring
    rw [h_split]
    exact h_int.sub (h_fermat.mul_right b)
  exact (piPrimeInt_dvd_iff (x := a ^ p ^ e - b)).1 (h_unit.dvd_mul_left.1 h_mul)

/-- Let `E = P.E s` be `K = ℚ(√-d)` with a root of unity of order `q₁ = P.q₁ s` adjoined, `e` in
`I_p° = partnerExponents P.d p` and `y` a vector over `E` integral above `p`. Then the `p ^ e`-th
power of the linear form `y† z = ∑ conj (τ(y_c)) z_(τ,c)` is `∑ τ'(y_c) z_(τ,c) ^ p ^ e` modulo
`π_p`; the sum runs over infinite places `τ` in `P.Φ s` and coordinates `c`.
`τ' = -p ^ e τ = P.partner s p e τ` is the product of `τ` with the class of `-p ^ e` in the group
`Gal(E/K) = (ℤ/q₁)ˣ` of places. `μ`, `ν` are the coefficients of the form and of the sum, read as
integers of `ℂ_p` through the embedding `ιₚ : ℂ → ℂ_p`. -/
lemma dvd_pow_sub_sum_partner {P : Parameters} {s p : ℕ} [Fact p.Prime] [PadicPlace p] {e : ℕ}
    {n : Type} [Fintype n] (he : e ∈ partnerExponents P.d p)
    {y : n → P.E s} (hy : ∀ i : n, IsIntegralAbove p (y i))
    {μ ν : P.Φ s × n → valRingCp p} (hμ : ∀ x : P.Φ s × n, (μ x : ℂ_[p]) = ιₚ (dagger y x))
    (hν : ∀ x : P.Φ s × n, (ν x : ℂ_[p]) = ιₚ (Φ (P.partner s p e x.1) (y x.2))) :
    C (piPrimeInt P.d) ∣ linearSeries μ ^ p ^ e - ∑ x : P.Φ s × n, ν x • X x ^ p ^ e := by
  have h_add : C (piPrimeInt P.d) ∣ linearSeries μ ^ p ^ e - ∑ x, (μ x • X x) ^ p ^ e :=
    dvd_sum_pow_sub_sum (mod_cast map_dvd C (piPrimeInt_dvd_natCast P.d)) _ _ e
  have h_coeff (x : P.Φ s × n) : piPrimeInt P.d ∣ μ x ^ p ^ e - ν x := by
    rw [piPrimeInt_dvd_iff, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, hμ, hν]
    exact norm_conj_pow_sub_partner_le he x.1 (hy x.2)
  rw [← sub_add_sub_cancel _ (∑ x, (μ x • X x) ^ p ^ e), ← sum_sub_distrib]
  refine h_add.add (dvd_sum fun x _ ↦ ?_)
  rw [smul_pow, ← sub_smul, smul_eq_C_mul]
  exact (map_dvd C (h_coeff x)).mul_right _

/-- For vectors `u_j` over `E = P.E s` integral above `p`, the linear forms `u_j† z`, whose
coefficient at `z_(τ,c)` is `conj (τ(u_{j,c}))` read in `ℂ_p` through the embedding `ιₚ` of `ℂ`,
have integral coefficients. -/
lemma norm_daggerForms_le_one (P : Parameters) (s : ℕ) {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {n J : Type} {u : J → n → P.E s}
    (hu : ∀ (j : J) (i : n), IsIntegralAbove p (u j i)) (j : J) (x : P.Φ s × n) :
    ‖(daggerForms u j x : ℂ_[p])‖ ≤ 1 :=
  (hu j x.2).norm_conj_le_one _

/-- Let `E = P.E s` be `K = ℚ(√-d)` (`d = P.d`) with a root of unity of order `q₁ = P.q₁ s`
adjoined, `s` being the tower level, and let `e` be in `I_p° = partnerExponents P.d p`. Let the
vectors `u_j` of `Eⁿ`, integral above `p` and each taken `m_j` times, be a resolution of the
identity: `z = ∑ m_j (u_j† z) u_j`. Then `∑ m_j (u_j† z) ^ p ^ e * (u_j† z)` is the coupling
`Γ_e = ∑ z_(τ,c) ^ p ^ e * z_(τ',c)` modulo `π_p`. -/
lemma piPrimeInt_dvd_sum_linearSeries_sub_coupling (P : Parameters) (s : ℕ) {p : ℕ} [Fact p.Prime]
    [PadicPlace p]
    {n J : Type} [Fintype n] [Fintype J] {u : J → n → P.E s} {m : J → ℕ} [DecidableEq n]
    {e : ℕ} (he : e ∈ partnerExponents P.d p)
    (h_res : IsResolution u m) (hu : ∀ (j : J) (i : n), IsIntegralAbove p (u j i))
    {μ : J → P.Φ s × n → valRingCp p}
    (hμ : ∀ (j : J) (x : P.Φ s × n), (μ j x : ℂ_[p]) = daggerForms u j x) :
    C (piPrimeInt P.d) ∣
      ∑ j : J, m j * (linearSeries (μ j) ^ p ^ e * linearSeries (μ j)) -
        coupling (P.partner s p) e := by
  -- `ν j (τ, c)` is the coordinate `c` of `u j` at the partner of `τ`.
  let ν (j : J) (x : P.Φ s × n) : valRingCp p :=
    ⟨ιₚ (Φ (P.partner s p e x.1) (u j x.2)), (hu j x.2).norm_le_one (ιₚ.comp _)⟩
  have h_pow (j : J) :
      C (piPrimeInt P.d) ∣ linearSeries (μ j) ^ p ^ e - ∑ x, ν j x • X x ^ p ^ e :=
    dvd_pow_sub_sum_partner he (hu j) (hμ j) fun _ ↦ rfl
  have h_identity (x : P.Φ s × n) :
      ∑ j, (m j * ν j x) • linearSeries (μ j) = X (P.partner s p e x.1, x.2) :=
    h_res.sum_smul_linearSeries (P.partner s p e x.1, x.2) (fun _ ↦ rfl) hμ
  have h_coupling : coupling (P.partner s p) e =
      ∑ j, (m j : MvPowerSeries (P.Φ s × n) (valRingCp p)) *
        ((∑ x, ν j x • X x ^ p ^ e) * linearSeries (μ j)) := by
    simp only [coupling, ← h_identity, mul_sum, sum_mul, smul_eq_C_mul, map_mul, map_natCast]
    rw [sum_comm]
    exact sum_congr rfl fun j _ ↦ sum_congr rfl fun x _ ↦ by ring
  rw [h_coupling, ← sum_sub_distrib]
  refine dvd_sum fun j _ ↦ ?_
  rw [← mul_sub, ← sub_mul]
  exact ((h_pow j).mul_right _).mul_left _

end Parameters

end New

end Partner

/-!
## The normal form of products of theta functions

Each theta factor at `ϖ z` is an integral series times `exp (c_ϖ Ξ(u† z))`. Modulo `π_p` the
`p`-th power is additive, so the exponents add up to a combination of powers of the couplings.
-/

section NormalForm

open MvPowerSeries WithPiTopology

namespace New
variable {p : ℕ} [Fact p.Prime]

/-- Let `π ∣ p`, let `Ξ` be a series in one variable congruent to
`∑ λ_{e j} (z ^ p ^ e * z) ^ p ^ j` modulo `π`, the sum over `e ∈ S` and `j` with
`λ_{e j} = l e j`, and let `partner e` be a self-map of the set `Φ` of places, with
`Γ_e = coupling partner e = ∑ z_(τ,c) ^ p ^ e * z_(partner e τ,c)` summed over `(τ, c)` in `Φ × n`.
If series `L_i` without constant term are such that `∑ m_i L_i ^ p ^ e * L_i` is `Γ_e` modulo `π`
for `e ∈ S`, then the `Ξ(L_i)`, each taken `m_i` times, add up to
`couplingSum S partner l = ∑ λ_{e j} Γ_e ^ p ^ j` modulo `π`. -/
lemma dvd_sum_subst_sub_couplingSum {Φ n J : Type} [Fintype Φ] [Fintype n] [Fintype J]
    {S : Set ℕ} {partner : ℕ → Φ → Φ} {l : ℕ → ℕ → valRingCp p} {π : valRingCp p} (hπ : π ∣ p)
    {Ξ : PowerSeries (valRingCp p)}
    (hΞ : C π ∣ Ξ -
      ∑' x : S × ℕ, l x.1 x.2 • (PowerSeries.X ^ p ^ (x.1 : ℕ) * PowerSeries.X) ^ p ^ x.2)
    {L : J → MvPowerSeries (Φ × n) (valRingCp p)} (hL : ∀ i : J, constantCoeff (L i) = 0)
    {m : J → ℕ} (hΓ : ∀ e ∈ S, C π ∣ ∑ i : J, m i * (L i ^ p ^ e * L i) - coupling partner e) :
    C π ∣ ∑ i : J, m i • Ξ.subst (L i) - couplingSum S partner l := by
  have h_subst (i : J) : PowerSeries.HasSubst (L i) := .of_constantCoeff_zero (hL i)
  set T : PowerSeries (valRingCp p) :=
    ∑' x : S × ℕ, l x.1 x.2 • (PowerSeries.X ^ p ^ (x.1 : ℕ) * PowerSeries.X) ^ p ^ x.2
  have h_replace (i : J) : C π ∣ Ξ.subst (L i) - T.subst (L i) := by
    obtain ⟨G, hG⟩ : C π ∣ Ξ - T := hΞ
    exact ⟨PowerSeries.subst (L i) G, by rw [← PowerSeries.subst_sub (h_subst i), hG,
      ← smul_eq_C_mul, ← smul_eq_C_mul, PowerSeries.subst_smul (h_subst i)]⟩
  have h_sum (i : J) :
      HasSum (fun x : S × ℕ ↦ l x.1 x.2 • (L i ^ p ^ (x.1 : ℕ) * L i) ^ p ^ x.2)
        (T.subst (L i)) := by
    -- Substitution is continuous, so it maps the sum `T` term by term.
    have h_cont : Continuous (PowerSeries.substAlgHom (R := valRingCp p) (h_subst i)) := by
      rw [PowerSeries.coe_substAlgHom]
      exact continuous_subst_of_constantCoeff_eq_zero fun _ ↦ hL i
    rw [← PowerSeries.coe_substAlgHom (h_subst i)]
    simpa only [Function.comp_def, map_smul, map_pow, map_mul, PowerSeries.substAlgHom_X] using
      (summable_smul_X_pow_mul_X_pow S l).hasSum.map _ h_cont
  -- Term by term: `p ^ j`-th powers are additive modulo `π`.
  have h_tsum_congr : C π ∣ ∑ i, m i * T.subst (L i) - couplingSum S partner l := by
    refine C_dvd_of_hasSum ((hasSum_sum fun i _ ↦ (h_sum i).mul_left _).sub hasSum_couplingSum) ?_
    rintro ⟨⟨e, he⟩, j⟩
    -- A sum with multiplicities is a sum over the pairs `(i, k)` with `k < m i`.
    have h_add : C π ∣
        (∑ i, m i * (L i ^ p ^ e * L i)) ^ p ^ j - ∑ i, m i * (L i ^ p ^ e * L i) ^ p ^ j := by
      simpa [Fintype.sum_sigma] using dvd_sum_pow_sub_sum (mod_cast map_dvd C hπ) .univ
        (fun x : Σ i, Fin (m i) ↦ L x.1 ^ p ^ e * L x.1) j
    have h_diff : C π ∣ ∑ i, m i * (L i ^ p ^ e * L i) ^ p ^ j - coupling partner e ^ p ^ j := by
      simpa only [sub_sub_sub_cancel_left] using
        ((hΓ e he).trans (sub_dvd_pow_sub_pow _ _ (p ^ j))).sub h_add
    -- The common factor `λ_{e j}` comes out of the sum.
    simp only [smul_eq_C_mul, mul_left_comm _ (C (l e j)), ← Finset.mul_sum, ← mul_sub]
    exact h_diff.mul_left _
  have h_sum_replace : C π ∣
      ∑ i, (m i : MvPowerSeries (Φ × n) (valRingCp p)) * (Ξ.subst (L i) - T.subst (L i)) :=
    Finset.dvd_sum fun i _ ↦ (h_replace i).mul_left _
  simpa only [nsmul_eq_mul, mul_sub, Finset.sum_sub_distrib, sub_add_sub_cancel] using
    h_sum_replace.add h_tsum_congr

/-- For a series `g` without constant term, `exp (n g) = exp(g) ^ n`. -/
lemma expSubst_nsmul {σ : Type} {g : MvPowerSeries σ ℂ_[p]} (hg : constantCoeff g = 0) (n : ℕ) :
    expSubst (n • g) = expSubst g ^ n := by
  simpa using expSubst_sum (t := Finset.range n) (a := fun _ ↦ g) fun _ ↦ hg

/-- For a linear form `L = ∑ ν_x z_x` with integral coefficients, `g(L)` at `ϖ z` is the series
`g(ϖ t)` at `t = L`. -/
lemma rescale_subst_linearSeries_coe {X : Type} [Fintype X] (ϖ : ℂ_[p]) (g : PowerSeries ℂ_[p])
    (ν : X → valRingCp p) :
    (g.subst (linearSeries fun x : X ↦ (ν x : ℂ_[p]))).rescale (fun _ : X ↦ ϖ) =
      (g.rescale ϖ).subst (seriesToCp (linearSeries ν)) := by
  rw [rescale_subst_linearSeries]
  simp [linearSeries]

/-- The inclusion `seriesToCp` of integral series commutes with substituting a series `L` without
constant term into a series `G` in one variable. -/
lemma seriesToCp_subst {X : Type} {L : MvPowerSeries X (valRingCp p)} (hL : constantCoeff L = 0)
    (G : PowerSeries (valRingCp p)) :
    seriesToCp (G.subst L) = PowerSeries.subst (seriesToCp L) (seriesToCp G) :=
  PowerSeries.map_subst (.of_constantCoeff_zero hL) G

namespace CMLattice
variable {d : ℕ} (C : CMLattice d) [PadicPlace p] {I X : Type} [Fintype I]
  [Fintype X] {μ : I → X → valRingCp p} {ϖ : ℂ_[p]}

/-- Let `d ≡ 7 mod 8` be prime, `C` a lattice with complex multiplication by the integers of
`ℚ(√-d)` and a point `t` of order two with `a₁² = 12 ℘(t)`, and `y` the Taylor series at `0`, read
in `ℂ_p` by `ιₚ`, of `C.translatedY z = (℘'(z + t) - a₁ (℘(z + t) - ℘(t))) / 2`. Let `μ_i` be
integral linear forms and `v(ϖ) ≥ ρ_p = varpiValuation d p`. Then a series `H` in
`C.multiSeriesRing`, the ring of integral series in the `y(μ_i z)`, is integral at `ϖ z`: `H(ϖ z)`
is in the range of `seriesToCp`, the inclusion of series over the integers of `ℂ_p`. -/
lemma rescale_mem_range_of_mem_multiSeriesRing [PrimeSevenModEight d]
    (hϖ : ‖ϖ‖ ≤ p ^ (-varpiValuation d p))
    {H : MvPowerSeries X ℂ_[p]} (hH : H ∈ C.multiSeriesRing fun (i : I) (x : X) ↦ (μ i x : ℂ_[p])) :
    H.rescale (fun _ : X ↦ ϖ) ∈ seriesToCp.range := by
  -- `y(ϖ w) = Y(w)` with `Y` integral, so `G(y(μ z))` at `ϖ z` is `G(Y(μ z))`.
  obtain ⟨G, rfl⟩ := hH
  obtain ⟨Y, hY⟩ : PowerSeries.rescale ϖ (taylorVia ιₚ C.translatedY) ∈ seriesToCp.range :=
    C.rescale_mem_range_seriesToCp hϖ C.isSeriesGenerator_translatedY.generator_mem
  have hY_zero : constantCoeff Y = 0 := by simpa using congrArg constantCoeff hY
  let Z (i : I) : MvPowerSeries X (valRingCp p) := PowerSeries.subst (linearSeries (μ i)) Y
  have hZ (i : I) : seriesToCp (Z i) = rescale (fun _ ↦ ϖ)
      ((taylorVia ιₚ C.translatedY).subst (linearSeries fun x ↦ (μ i x : ℂ_[p]))) := by
    rw [rescale_subst_linearSeries_coe, ← hY, seriesToCp_subst (constantCoeff_linearSeries _)]
  have h_subst : HasSubst Z := hasSubst_of_constantCoeff_zero fun i ↦
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_linearSeries _) Y hY_zero
  refine ⟨G.subst Z, ?_⟩
  -- Scaling is a substitution, and substitutions compose.
  simp only [map_subst h_subst, hZ, rescale_eq_subst]
  rw [← subst_comp_subst_apply (C.hasSubst_translatedY_subst _) (HasSubst.smul_X _)]
  simp [Function.comp_def]

/-- Let `C` be a lattice with complex multiplication by the integers of `ℚ(√-d)` and a point of
order two, and `θ = taylorVia ιₚ C.θ` the Taylor series of its theta function, read in `ℂ_p` by the
embedding `ιₚ` of `ℂ`. Let `θ(ϖ z) = W exp (κ Ξ)` with integral series `W`, `Ξ` and `Ξ(0) = 0`. Then
`C.thetaProd`, the product `∏ θ(μ_i z) ^ m_i` for integral linear forms `μ_i`, is at `ϖ z` the
integral series `∏ W(μ_i z) ^ m_i` times `exp (κ ∑ m_i Ξ(μ_i z))`. -/
lemma rescale_thetaProd_eq_mul_expSubst {κ : ℂ_[p]} {W Ξ : PowerSeries (valRingCp p)}
    (hΞ : PowerSeries.constantCoeff Ξ = 0)
    (h_theta : (taylorVia ιₚ C.θ).rescale ϖ = seriesToCp W * expSubst (κ • seriesToCp Ξ))
    (m : I → ℕ) :
    (C.thetaProd (fun (i : I) (x : X) ↦ (μ i x : ℂ_[p])) m).rescale (fun _ : X ↦ ϖ) =
      seriesToCp (∏ i : I, W.subst (linearSeries (μ i)) ^ m i) *
        expSubst (κ • seriesToCp (∑ i : I, m i • Ξ.subst (linearSeries (μ i)))) := by
  have hL (i : I) : constantCoeff (linearSeries (μ i)) = 0 := constantCoeff_linearSeries _
  have h_zero (i : I) : constantCoeff (κ • seriesToCp (Ξ.subst (linearSeries (μ i)))) = 0 := by
    simp [PowerSeries.constantCoeff_subst_eq_zero (hL i) Ξ hΞ]
  have h_factor (i : I) :
      ((taylorVia ιₚ C.θ).subst (linearSeries fun x ↦ (μ i x : ℂ_[p]))).rescale (fun _ ↦ ϖ) =
        seriesToCp (W.subst (linearSeries (μ i))) *
          expSubst (κ • seriesToCp (Ξ.subst (linearSeries (μ i)))) := by
    have h_subst : PowerSeries.HasSubst (seriesToCp (linearSeries (μ i))) :=
      .of_constantCoeff_zero (by simp [hL])
    rw [rescale_subst_linearSeries_coe, h_theta, PowerSeries.subst_mul h_subst,
      seriesToCp_subst (hL i), seriesToCp_subst (hL i), ← PowerSeries.subst_smul h_subst]
    -- It remains that substitution into an exponential is substitution into the exponent.
    exact congrArg _ (subst_expSubst (by simpa using .inr hΞ) h_subst.const)
  rw [thetaProd, map_prod, map_prod, map_sum, Finset.smul_sum, expSubst_sum fun i ↦ ?_,
    ← Finset.prod_mul_distrib]
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [map_pow, h_factor, mul_pow, map_pow, map_nsmul, smul_comm κ, expSubst_nsmul (h_zero i)]
  · rw [map_nsmul, smul_comm κ, map_nsmul, h_zero i, smul_zero]

end CMLattice

namespace Parameters

/-- Let `E = P.E s` be `K = ℚ(√-d)` with a root of unity of order `q₁ = P.q₁ s` adjoined, `p` a
prime not split in `K` (`chiK P.d p ≠ 1`), `I_p° = partnerExponents P.d p`, and for an infinite
place `τ` of `E` let its partner `τ' = -p ^ e τ` be the product of `τ` with the class of `-p ^ e` in
the group `Gal(E/K) = (ℤ/q₁)ˣ` of places. There are `ϖ` of valuation `ρ_p = varpiValuation P.d p`
and integers `λ_{e j}` of `ℂ_p`, with the `λ_{e 0}` for odd `e` units if `p` is inert, such that the
following holds. Take any resolution of the identity by vectors `u_j` of `Eⁿ`, taken `m_j` times and
integral above `p`. Then the product `∏ θ(u_j† z) ^ m_j` times an integral series in the `y(u_j† z)`
has the normal form. -/
lemma exists_hasNormalForm (P : Parameters) (s : ℕ) [PadicPlace p] (hp : chiK P.d p ≠ 1) :
    ∃ (ϖ : ℂ_[p]) (l : ℕ → ℕ → valRingCp p),
    ‖ϖ‖ = p ^ (-varpiValuation P.d p) ∧
    (chiK P.d p = -1 → ∀ e : ℕ, Odd e → IsUnit (l e 0)) ∧
    ∀ {n J : Type} [Fintype n] [DecidableEq n] [Fintype J] (u : J → n → P.E s) (m : J → ℕ),
      IsResolution u m → (∀ (j : J) (i : n), IsIntegralAbove p (u j i)) →
        ∀ H ∈ P.cmCurve.multiSeriesRing (daggerForms u),
          HasNormalForm (partnerExponents P.d p) (P.partner s p) ϖ l
            (P.cmCurve.thetaProd (daggerForms u) m * H) := by
  -- On one curve: `θ(ϖ z) = W exp (c_ϖ Ξ)` with `Ξ ≡ ∑ λ_{e j} (z ^ p ^ e * z) ^ p ^ j`.
  obtain ⟨ϖ, Ξ, W, l, hϖ, hΞ_zero, h_theta, hΞ, h_unit⟩ := P.cmCurve.exists_exponent_tsum hp
  refine ⟨ϖ, l, hϖ, h_unit, ?_⟩
  intro n J _ _ _ u m h_res hu H hH
  -- The linear forms `u† z` are integral, so at `ϖ z` the series is an integral series times
  -- the exponential of `c_ϖ ∑ m_j Ξ(u_j† z)`.
  let μ (j : J) (x : P.Φ s × n) : valRingCp p :=
    ⟨daggerForms u j x, P.norm_daggerForms_le_one s hu j x⟩
  have hL (j : J) : constantCoeff (linearSeries (μ j)) = 0 := constantCoeff_linearSeries _
  obtain ⟨V, hV⟩ : H.rescale (fun _ : P.Φ s × n ↦ ϖ) ∈ seriesToCp.range :=
    P.cmCurve.rescale_mem_range_of_mem_multiSeriesRing (μ := μ) hϖ.le hH
  have h_prod : (P.cmCurve.thetaProd (daggerForms u) m * H).rescale (fun _ ↦ ϖ) =
      seriesToCp ((∏ j, W.subst (linearSeries (μ j)) ^ m j) * V) *
        expSubst ((ϖ ^ (p + 1) / p) • seriesToCp (∑ j, m j • Ξ.subst (linearSeries (μ j)))) := by
    rw [map_mul, map_mul, hV, mul_right_comm,
      ← P.cmCurve.rescale_thetaProd_eq_mul_expSubst hΞ_zero h_theta m]
  have h_congr : C (piPrimeInt P.d) ∣ ∑ j, m j • Ξ.subst (linearSeries (μ j)) -
      couplingSum (partnerExponents P.d p) (P.partner s p) l :=
    dvd_sum_subst_sub_couplingSum (piPrimeInt_dvd_natCast P.d) hΞ hL fun e he ↦
      P.piPrimeInt_dvd_sum_linearSeries_sub_coupling s he h_res hu fun _ _ ↦ rfl
  refine .of_dvd_sub (P.norm_pow_succ_div_mul_piPrimeInt hp hϖ).le ?_ h_congr h_prod
  simp [PowerSeries.constantCoeff_subst_eq_zero (hL _) Ξ hΞ_zero]

end Parameters

end New

end NormalForm
