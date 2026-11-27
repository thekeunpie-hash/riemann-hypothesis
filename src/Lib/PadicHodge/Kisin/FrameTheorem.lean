module

import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.RingTheory.PicardGroup
public import Lib.General.NumberTheory.CoefficientRings
public import Lib.PadicHodge.Kisin.Bicommutant
public import Lib.PadicHodge.Kisin.KummerChartExistence
public import Lib.PadicHodge.TateSen
import Lib.PadicHodge.Crystalline.FixedRatios
import Lib.PadicHodge.Kisin.PeriodMatrixBasis
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Topology.Separation.CompletelyRegular
public import Lib.ClassField.LocalDuality.CrystallineDuality
public import Lib.PadicHodge.ArtinSchreierSequence
import Lib.PadicComparison.Descent.TestCategory
import Lib.PadicHodge.Crystalline.HodgeTateForms
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Lib.PadicHodge.Kisin.PeriodMatrixFrame
import Lib.PadicHodge.RadiusLemma

section
section
/-!
# Kummer charts: the different, the primes φ^a E of A_inf and their images in B_dR

Fix a Kummer chart `k` (`New.Lift.KummerChart`) with ring `S ⊆ A_inf` and distinguished element `E`.
The file studies the elements p_a = φ^a E and δ = zτ of A_inf and bounds the different of the chart.

## Main definitions and results

* `New.Lift.KummerChart.exists_derivative_dvd_p_pow`: a bound for the different.
* `New.Lift.phiInvToBdR`: the map `r ↦ φ^{-a} r` from `A_inf` to `B_dR`.
* `New.Lift.KummerChart.phiInvToBdR_mem_hodgeFil_one_iff`,
  `New.Lift.KummerChart.phiInvToBdR_frobE_zpow_mem_hodgeFil`: it sends `r` to an element of positive
  order exactly when `φ^a E` divides `r`, and the `m`-th power of the image of `φ^a E` has order at
  least `m`.
* `New.Lift.KummerChart.valueField`: the subfield `𝒦_a` of `B_dR` in which values are taken.
* `New.Lift.KummerChart.sum_phiInvToBdR_map_mul_mem_of_mem_valueField`: `S`-linear maps `A_inf → S`
  preserve linear relations over `𝒦_a`.
* `New.Lift.KummerChart.smul_sub_mem_hodgeFil_of_valueField`: if `φ^a E` divides `gs − s` for all
  `s` in `S`, then `g` fixes the elements of `𝒦_a` of order at least `0` modulo `t`; more generally,
  the same holds for the sums `∑ l, t l s` and `∑ l, t l x`, with the `t l` in the Galois monoid.

Notions from other files:
* `New.Period.Ainf`: the ring A_inf of p-typical Witt vectors over the tilt O^♭ of the ring O_C of
  integers of C_p.
* `New.Period.tau`, `New.Period.xi`: τ = [ε^(1/p)] − 1, with φ τ = μ = [ε] − 1, and ξ = μ/τ.
* `New.Lift.FrobGroup`: the group ℤ × Γ, acting on A_inf by (n, g) ↦ φ^n j(g).
* `New.Lift.Chart.S`, `New.Lift.Chart.bicommutant`: for a chart, the Λ-subalgebra S of A_inf that is
  the image of the chart's map Λ[[X]] → A_inf, with `k.coord₀ : A_inf → S` an S-linear retraction of
  A_inf onto S, and the subalgebra S_B of B^+ of the elements whose multiplication commutes with
  every S-linear map of B^+ that keeps the image of A_max.
* `New.Period.hodgeFil`: the step Fil^n = t^n B_dR^+ of the filtration of B_dR, for n in ℤ.

## Relation to the literature

Known; see `Lib.PadicHodge.Kisin.PeriodMatrixFrame` for sources.
-/

@[expose] public section

noncomputable section

namespace New.Lift.KummerChart

open Period Polynomial FrobGroup ValuationRing NeZero

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] [k : KummerChart Γ] (a : ℕ)

/-! ### The primes p_a = φ^a E and the element δ = zτ -/

/-- The submonoid of ℤ × Γ consisting of the elements (0,g) with g in the subgroup Γ' of the
Kummer chart. -/
def galMonoid : Submonoid (FrobGroup Γ) := MonoidHom.mrange (inr.comp k.subgroup.subtype)

/-- The element δ = zτ of A_inf, where z is the coordinate of the Kummer chart. -/
def zTau : Ainf := tau * k.z

lemma val_frobE : (k.frobE a).val = φ ^ a • k.E := by
  rw [phi_pow_smul]
  exact k.coe_phi_pow a k.E

/-- The prime p does not divide p_a = φ^a E in A_inf. -/
lemma not_p_dvd_val_frobE : ¬↑p ∣ (k.frobE a).val := by
  -- Undoing `φ ^ a` would give `p ∣ E`, and `E` divides `ξ`.
  rintro ⟨y, hy⟩
  have h_E : k.E.val = ↑p * ((φ ^ a)⁻¹ • y) := by
    simpa [val_frobE, ← eq_inv_smul_iff] using hy
  exact not_p_dvd_xi ((Dvd.intro _ h_E.symm).trans k.associated_E_xi.dvd)

/-- The image in W(C^♭) of p_a = φ^a(E), as a unit; it is invertible because p does not divide
p_a in A_inf. -/
def frobEUnit : WittCFlatˣ := (isUnit_algebraMap_wittCFlat_of_not_p_dvd
  (not_p_dvd_val_frobE a)).unit

/-- The image in W(C^♭) of δ = zτ, as a unit; it is invertible because p divides neither z nor τ
in A_inf. -/
def zTauUnit : WittCFlatˣ :=
  (isUnit_algebraMap_wittCFlat_of_not_p_dvd
    (Ainf.prime_p.not_dvd_mul not_p_dvd_tau k.not_p_dvd_z)).unit

variable {a : ℕ} {b : ℕ} (g : k.galMonoid)

@[simp high]
lemma frobE_ne_zero : (k.frobE a).val ≠ 0 := fun h ↦ not_p_dvd_val_frobE a (by simp [h])

/-- Bound for the different of a chart: write the Kummer chart as S = Λ⟦z⟧ ⊂ A_inf with
Λ = `WittFq k.f` (Witt vectors of a finite field), let E = `k.E` ∈ S be the image of X^e A + p, and
let e be the ramification index of the chart. Then there is a polynomial P over Λ with E ∣ P(z) in S
such that θ(P'(z)) divides p^d in O_C, where θ : A_inf → O_C is Fontaine's map, where
d = `differentBound` is 0 if e = 1 and v_p(e) + 1 otherwise. -/
lemma exists_derivative_dvd_p_pow :
    ∃ P : (WittFq k.f)[X],
      k.E ∣ aeval k.z P ∧ theta (aeval k.z P.derivative).val ∣ p ^ k.differentBound := by
  -- Take `P = X ^ e - R`, with `R` the remainder of `z ^ e` modulo `E`. If `θ (P'(z))` did not
  -- divide `p ^ (v_p e + 1)`, this power would divide `P'`, whose top coefficient is `e`.
  -- Weierstrass division: `rem s` is the one polynomial of degree `< e` with `E ∣ s - (rem s)(z)`.
  have h_division : ∀ s : k.S, ∃ r : (WittFq k.f)[X]_k.e, k.frobE 0 ∣ s - r.val.aeval k.z ∧
      ∀ r' : (WittFq k.f)[X]_k.e, k.frobE 0 ∣ s - r'.val.aeval k.z → r' = r :=
    k.weierstrass_division 0 (one_mul k.e)
  choose rem h_rem h_uniq using h_division
  set R : (WittFq k.f)[X] := (rem (k.z ^ k.e)).val
  have hR : k.frobE 0 ∣ k.z ^ k.e - R.aeval k.z := h_rem (k.z ^ k.e)
  have hR_deg : ∀ i, k.e ≤ i → R.coeff i = 0 := by
    simpa [degreeLT] using (rem (k.z ^ k.e)).property
  have hP_dvd : k.E ∣ aeval k.z (X ^ k.e - R) := by simpa [Chart.frobE] using hR
  refine ⟨X ^ k.e - R, hP_dvd, ?_⟩
  unfold differentBound
  split_ifs with he_one
  · -- for `e = 1` the remainder `R` is a constant, so `P' = 1`
    have hR_derivative : R.derivative = 0 := by
      ext i
      simp [coeff_derivative, hR_deg (i + 1) (by omega)]
    simp [he_one, hR_derivative]
  set m : ℕ := padicValNat p k.e + 1
  -- divisibility in `O_C` is total, so it suffices to exclude `p ^ m ∣ θ (P'(z))`
  refine (dvd_total _ _).resolve_right fun h_dvd ↦ ?_
  apply pow_succ_multiplicity_not_dvd (p := p) (NeZero.ne k.e)
  rw [← Nat.padicValNat_def]
  -- the quotient can be taken in `S` modulo `E`: apply `exists_frobE_dvd_sub_of_dvd` to an
  -- `S`-linear retraction of `A_inf` onto `S`
  have h_theta_zero (r : Ainf) : thetaPhiInv 0 r = theta r := by
    simpa using thetaPhiInv_phi_pow 0 r
  have h_dvd_zero : thetaPhiInv 0 ((p ^ m : k.S) : Ainf) ∣
      thetaPhiInv 0 (aeval k.z (X ^ k.e - R).derivative).val := by simpa [h_theta_zero] using h_dvd
  -- (the type of `hx` is left to the elaborator: stated, it sends the check into long unfolding)
  obtain ⟨x, hx⟩ := k.exists_frobE_dvd_sub_of_dvd 0 k.coord₀ (p ^ m) _ h_dvd_zero
  rw [k.coord₀_coe] at hx
  -- `P'` and `p ^ m • rem x` have degree `< e` and are both remainders of `p ^ m * x` modulo `E`
  have h_deg : (X ^ k.e - R).derivative ∈ (WittFq k.f)[X]_k.e := by
    simp only [degreeLT, Submodule.mem_iInf, LinearMap.mem_ker, lcoeff_apply]
    intro i hi
    simp [coeff_derivative, coeff_X_pow, hR_deg (i + 1) (by omega), show i + 1 ≠ k.e by omega]
  -- the polynomials are left to unification: written out, elaboration times out
  have h_left : (⟨_, h_deg⟩ : (WittFq k.f)[X]_k.e) = rem (p ^ m * x) :=
    h_uniq (p ^ m * x) ⟨_, h_deg⟩ (dvd_sub_comm.mp hx)
  have h_mul : k.frobE 0 ∣ p ^ m * x - (p ^ m • rem x).val.aeval k.z := by
    simpa [mul_sub] using (h_rem x).mul_left (p ^ m)
  have h_right : p ^ m • rem x = rem (p ^ m * x) := h_uniq (p ^ m * x) _ h_mul
  have h_eq : (X ^ k.e - R).derivative = p ^ m • (rem x).val :=
    congrArg Subtype.val (h_left.trans h_right.symm)
  -- the coefficient of `X ^ (e - 1)` in `P'` is `e`, so `p ^ m` divides `e` in `Λ`
  have h_coeff : ((p ^ m : ℕ) : WittFq k.f) ∣ (k.e : WittFq k.f) := by
    have h_top : (X ^ k.e - R).derivative.coeff (k.e - 1) = (k.e : WittFq k.f) := by
      simp [coeff_derivative, hR_deg, NeZero.one_le]
    exact ⟨(rem x).val.coeff (k.e - 1), by
      rw [← h_top, h_eq, AddMonoidAlgebra.coeff_smul_apply, nsmul_eq_mul]⟩
  -- pass from `Λ` to `O_C` by `θ`, and on to `ℕ` by `p`-adic norms
  have h_coeff_OC : ((p ^ m : ℕ) : OC) ∣ (k.e : OC) := by
    simpa using (theta.comp (algebraMap (WittFq k.f) Ainf)).map_dvd h_coeff
  have h_norm : ‖((k.e : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    simpa [← PadicComplex.norm_extends', valRingCp.dvd_iff_norm_le, norm_p_eq_inv] using h_coeff_OC
  exact_mod_cast (Padic.norm_int_le_pow_iff_dvd _ _).mp h_norm

/-- The subgroup Γ', with the restriction of j, is a group over G_p: its image is open. -/
@[simps]
instance : OverGp k.subgroup p where
  toGp := toGp.comp k.subgroup.subtype
  isOpen_range :=
    ⟨Subgroup.isOpen_of_mem_nhds _ (nhds_one_le_map_nearOne Γ (nearOne_le fun g ↦ ⟨g, rfl⟩))⟩

lemma not_frobE_dvd_p (a : ℕ) : ¬(k.frobE a).val ∣ p := by simp [frobE_dvd_iff, NeZero.ne]

lemma frobE_dvd_phi_pow_tau (h_lt : a < b) : (k.frobE a).val ∣ φ ^ b • tau := by
  -- Write `b` as `a + c + 1`: `thetaPhiInv a` sends `φ ^ (a + c + 1) τ` to `θ (φ ^ c μ) = 0`, as
  -- `φ τ = μ`.
  obtain ⟨c, rfl⟩ : ∃ c : ℕ, b = a + c + 1 := Nat.exists_eq_add_of_lt h_lt
  simp [pow_add, mul_smul, phi_smul_ainf, phi_pow_smul c, frobE_dvd_iff]

/-- For a ≠ b, the element p_a = φ^a E does not divide p_b = φ^b E in A_inf. -/
lemma not_frobE_dvd_frobE_of_ne (h_ne : a ≠ b) : ¬(k.frobE a).val ∣ k.frobE b := by
  -- Both elements are prime, so each would divide the other. The one of smaller index divides
  -- `φ ^ n τ`, with `n` the larger index; the one of index `n` does not.
  intro h_dvd
  have prime (n : ℕ) : Prime (k.frobE n).val := by
    simp [Prime, isUnit_iff_dvd_one, frobE_dvd_iff]
  have not_dvd (n : ℕ) : ¬(k.frobE n).val ∣ φ ^ n • tau := by simp [frobE_dvd_iff]
  obtain hab | hba := h_ne.lt_or_gt
  · exact not_dvd b (((prime a).associated_of_dvd (prime b) h_dvd).dvd'.trans
      (frobE_dvd_phi_pow_tau hab))
  · exact not_dvd a (h_dvd.trans (frobE_dvd_phi_pow_tau hba))

/-- For any action of ℤ × Γ on a type X, an element g of the Galois monoid of the chart commutes
with φ^a. -/
lemma smul_phi_pow_comm {X : Type*} [MulAction (FrobGroup Γ) X] (x : X) :
    g • φ ^ a • x = φ ^ a • g • x := by
  -- the second component of `φ` is `1`, and the first factor `ℤ` is commutative
  have h_comm : Commute (g : FrobGroup Γ) (φ ^ a) :=
    (Commute.prod (.all _ _) (.one_right _)).pow_right a
  simp only [Submonoid.smul_def, smul_smul, h_comm.eq]

/-- The coordinate z is a Teichmüller lift, so φ^a z = z^(p^a). -/
lemma phi_pow_smul_z : φ ^ a • k.z.val = k.z ^ p ^ a := by simp [phi_pow_smul, k.z_eq_teichmuller]

lemma zTau_dvd_phi_pow_smul (a : ℕ) : k.zTau ∣ φ ^ a • k.zTau := by
  simp [k.z_eq_teichmuller, phi_pow_smul, mul_dvd_mul, tau, sub_one_dvd_pow_sub_one, zTau,
    NeZero.ne]

lemma not_frobE_dvd_zTau (a : ℕ) : ¬(k.frobE a : Ainf) ∣ k.zTau := by
  -- `zTau` divides `φ ^ a • zTau`, and `φ ^ a • E` does not divide the latter.
  intro h
  simpa [zTau, frobE_dvd_iff, Chart.theta_z_ne_zero] using h.trans (zTau_dvd_phi_pow_smul a)

/-! ### The action of Γ' on the chart -/

/-- Let Γ' be the subgroup of Γ of index prime to p attached to the Kummer chart S = Λ⟦z⟧, and let g
be in the Galois monoid, that is, an element (0, γ) of ℤ × Γ with γ ∈ Γ', acting through γ. Then for
every s ∈ S, the element zτ·E divides gs − s in A_inf, where zτ = `zTau` and z is the coordinate of
the chart. -/
lemma zTau_mul_E_dvd_smul_sub (s : k.S) : k.zTau * k.E ∣ g • s - s := by
  -- As `τ E` is associated to `μ` and `g` fixes the constants, it is enough that `z μ ∣ g z - z`.
  obtain ⟨_, γ, rfl⟩ := g
  obtain ⟨h_const, h_fix⟩ : FixesLambda k.f (toGp (γ : Γ)) ∧
      toGp (γ : Γ) • theta k.z = theta k.z := fixes γ
  have hz : theta k.z ≠ 0 := k.theta_z_ne_zero
  grw [zTau, mul_rotate, mul_assoc, k.associated_E_mul_tau_mu.dvd]
  apply k.dvd_smul_sub_of_fixesLambda _ h_const
  -- `z = [ϖ]` and `g z = [ϖ']` with `ϖ' = g ϖ`; `ϖ'` has the same untilt as `ϖ`, so `ϖ' = ϖ η`.
  let a : FrobGal := MonoidHom.inr (Multiplicative ℕ) (Gp p) (toGp (γ : Γ))
  have h_z : k.z.val = WittVector.teichmuller p k.varpiFlat := k.z_eq_teichmuller
  have h_fix' : theta (a • k.z.val) = theta k.z.val :=
    (theta_smul (toGp (γ : Γ)) k.z.val).trans h_fix
  change k.z.val * mu ∣ a • k.z.val - k.z.val
  rw [h_z, smul_teichmuller] at h_fix' ⊢
  rw [h_z] at hz
  generalize a • k.varpiFlat = ϖ' at h_fix' ⊢
  have h_untilt_dvd : k.varpiFlat.untilt ∣ ϖ'.untilt := by simpa using h_fix'.symm.dvd
  obtain ⟨η, hη⟩ : k.varpiFlat ∣ ϖ' := Variety.untilt_dvd_iff.mp h_untilt_dvd
  -- `η` has untilt `1`, as `ϖ` and `ϖ η` have the same nonzero untilt; so `θ (φ ^ n ([η] - 1)) = 0`
  -- for all `n`, which makes `[η] - 1` a multiple of `μ` (`mu_dvd_of_theta_frobEnd`)
  have hη_one : η.untilt = 1 := by
    have h_untilt : k.varpiFlat.untilt * η.untilt = k.varpiFlat.untilt := by simpa [hη] using h_fix'
    have h_ne : k.varpiFlat.untilt ≠ 0 := by simpa using hz
    exact (mul_eq_left₀ h_ne).mp h_untilt
  have h_theta (j : ℕ) : theta (frobEnd^[j] (WittVector.teichmuller p η - 1)) = 0 := by
    simp [hη_one]
  have h_mu : mu ∣ WittVector.teichmuller p η - 1 := mu_dvd_of_theta_frobEnd h_theta
  rw [hη, map_mul, ← mul_sub_one]
  exact mul_dvd_mul_left _ h_mu

end New.Lift.KummerChart

/-! ## The fields 𝒦_a in B_dR and linearity of coordinate maps over them -/

namespace New.Lift

open Period Algebra IntermediateField algebraAdjoinAdjoin BdRPlus Submodule FrobGroup Finset

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] [k : KummerChart Γ]
  (a : ℕ) {n : ℤ} {x y : BdR} {r : Ainf}

/-- The ring homomorphism `A_inf → B_dR` that sends `r` to the image of `φ^{-a} r`. -/
def phiInvToBdR : Ainf →+* BdR :=
  (algebraMap Ainf BdR).comp (MulSemiringAction.toRingHom (FrobGroup Γ) Ainf (φ ^ a)⁻¹)

/-- The subfield `𝒦_a` of `B_dR` generated over the fixed field of `Γ'` by the products
`b * φ^{-a} s` with `b` in `S_B` and `s` in `S`. It is the field generated by the images of `S_B`
and of `φ^{-a} S`, see `KummerChart.valueField_eq_adjoin_union`. -/
def KummerChart.valueField : IntermediateField (localFieldOf k.subgroup) BdR :=
  IntermediateField.adjoin (localFieldOf k.subgroup)
    (Set.range fun q : k.bicommutant × k.S ↦
      algebraMap k.bicommutant BdR q.1 * phiInvToBdR a q.2)

variable {a}

omit [KummerChart Γ] in
@[simp] lemma phiInvToBdR_eq_zero_iff : phiInvToBdR a r = 0 ↔ r = 0 := by
  simp [phiInvToBdR, inv_smul_eq_iff]

omit Γ k in
lemma smul_mem_hodgeFil (g : Gp p) (hx : x ∈ hodgeFil n) : g • x ∈ hodgeFil n := by
  -- `g` multiplies `tUnit ^ n` by a scalar (`smul_tUnit_zpow`)
  obtain ⟨y, rfl⟩ := mem_hodgeFil.mp hx
  -- `↓` rewrites `g • tUnit ^ n` by `smul_tUnit_zpow` before `simp` splits the power
  simp [↓smul_mul', ↓smul_tUnit_zpow, smul_of_tower_mem, mem_hodgeFil]

namespace KummerChart

variable (g : k.galMonoid)

/-- The Galois monoid acts on B_dR through the Galois group G_p. -/
instance : MulSemiringAction k.galMonoid BdR := .compHom _ ((toGp.comp snd).domRestrict _)

/-- The action of the Galois monoid on B_dR is compatible with its action on A_inf. -/
instance : SMulDistribClass k.galMonoid Ainf BdR := ⟨fun ⟨_, γ, rfl⟩ ↦ smul_distrib_smul (toGp γ)⟩

/-- An element g of the Galois monoid commutes with the map `r ↦ φ^{-a} r` from A_inf to
BdR. -/
@[simp] lemma smul_phiInvToBdR : g • phiInvToBdR a r = phiInvToBdR a (g • r) := by
  simp [phiInvToBdR, eq_inv_smul_iff, ← smul_phi_pow_comm]

lemma galMonoid_smul_mem_hodgeFil (hx : x ∈ hodgeFil n) : g • x ∈ hodgeFil n :=
  smul_mem_hodgeFil _ hx

/-- For r in A_inf, the image of φ^{−a}(r) in B_dR lies in tB_dR^+ if and only if φ^a(E) divides
r in A_inf. -/
lemma phiInvToBdR_mem_hodgeFil_one_iff :
    phiInvToBdR a r ∈ hodgeFil 1 ↔ (k.frobE a : Ainf) ∣ r :=
  algebraMap_mem_hodgeFil_one_iff.trans (by simp [frobE_dvd_iff, ← thetaPhiInv_phi_pow a])

/-- Let `r` in A_inf be prime to `φ^a E`. Then for every integer `m` and every `y` in B_dR, the
product of `(φ^{-a} r)^m` and `y` lies in Fil^n = t^n B_dR^+ exactly when `y` does. -/
lemma mul_mem_hodgeFil_iff_of_not_frobE_dvd (hr : ¬(k.frobE a : Ainf) ∣ r) (m : ℤ) :
    phiInvToBdR a r ^ m * y ∈ hodgeFil n ↔ y ∈ hodgeFil n := by
  -- `phiInvToBdR a r` comes from a unit of `BdRPlus`: a non-unit lies in `hodgeFil 1`, which
  -- forces `k.frobE a ∣ r`.
  have hu : IsUnit (algebraMap Ainf BdRPlus ((φ ^ a)⁻¹ • r)) :=
    isUnit_iff.mpr fun h_fil ↦
      hr (phiInvToBdR_mem_hodgeFil_one_iff.mp (algebraMap_mem_hodgeFil_one_iff.mpr h_fil))
  have h_unit : phiInvToBdR a r = algebraMap BdRPlus BdR hu.unit := rfl
  have h_smul : phiInvToBdR a r ^ m * y = hu.unit ^ m • y := by
    cases m <;> simp [h_unit, Units.smul_def, smul_def']
  rw [h_smul, smul_mem_iff']

/-- For every integer m, let u be the image in B_dR of φ^{−a}(φ^a E), that is, of E. Then u^m lies
in Fil^m = t^m B_dR^+. -/
lemma phiInvToBdR_frobE_zpow_mem_hodgeFil (a : ℕ) (m : ℤ) :
    phiInvToBdR a (k.frobE a) ^ m ∈ hodgeFil m := by
  -- `phiInvToBdR a (k.frobE a)` is the image of `E`, and `E w = t` for a unit `w` of `BdRPlus`.
  obtain ⟨w, hw⟩ : Associated (algebraMap Ainf BdRPlus k.E) tPeriod :=
    (k.associated_E_xi.map _).trans associated_xi_tPeriod
  refine mem_hodgeFil.mpr ⟨↑(w ^ m)⁻¹, ?_⟩
  cases m <;>
    simp [phiInvToBdR, val_frobE, tUnit, ← hw, mul_pow, field, ← IsScalarTower.algebraMap_apply]

lemma phiInvToBdR_mem_valueField (s : k.S) : phiInvToBdR a s ∈ valueField a :=
  subset_adjoin _ _ ⟨(1, s), by simp⟩

lemma algebraMap_bicommutant_mem_valueField (b : k.bicommutant) :
    algebraMap k.bicommutant BdR b ∈ valueField a :=
  subset_adjoin _ _ ⟨(b, 1), by simp⟩

/-- The field `𝒦_a` is generated by the images of `S_B` and of `φ^{-a} S`. -/
lemma valueField_eq_adjoin_union :
    valueField a = IntermediateField.adjoin (localFieldOf k.subgroup)
      (Set.range (algebraMap k.bicommutant BdR) ∪ Set.range fun s : k.S ↦ phiInvToBdR a s) := by
  apply le_antisymm
  · exact IntermediateField.adjoin_le_iff.mpr (Set.forall_mem_range.mpr fun (b, s) ↦
      mul_mem (subset_adjoin _ _ (.inl ⟨b, rfl⟩)) (subset_adjoin _ _ (.inr ⟨s, rfl⟩)))
  · exact IntermediateField.adjoin_le_iff.mpr (Set.union_subset
      (Set.forall_mem_range.mpr algebraMap_bicommutant_mem_valueField)
      (Set.forall_mem_range.mpr phiInvToBdR_mem_valueField))

/-- The field `𝒦_0` is contained in `𝒦_a`. -/
lemma valueField_zero_le : valueField 0 ≤ valueField a := by
  rw [valueField_eq_adjoin_union (a := 0)]
  refine IntermediateField.adjoin_le_iff.mpr (Set.union_subset
    (Set.forall_mem_range.mpr algebraMap_bicommutant_mem_valueField)
    (Set.forall_mem_range.mpr fun s ↦ ?_))
  -- At level `0` the image of `S` lies in the image of `S_B`.
  rw [show phiInvToBdR 0 (s : Ainf) = algebraMap Ainf BdR s by simp [phiInvToBdR]]
  exact algebraMap_bicommutant_mem_valueField ⟨Chart.ainfToBPlus s, k.ainfToBPlus_mem_bicommutant s⟩

/-- An element of `B_dR` fixed by `Γ'` lies in `Fil⁰` and in `𝒦₀`. -/
lemma mem_hodgeFil_zero_and_mem_valueField_zero_of_fixed
    (h_fixed : ∀ g : k.subgroup, x = toGp (g : Γ) • x) :
    x ∈ hodgeFil 0 ∧ x ∈ valueField 0 := by
  -- Tate–Sen: a fixed element of `BdR` is a constant `c` in the fixed field of `toGp Γ'`.
  obtain ⟨c, hc⟩ : ∃ c : localFieldOf k.subgroup,
      x - algebraMap (localFieldOf k.subgroup) BdR c ∈ (⊥ : Submodule BdRPlus BdR) :=
    BdR.exists_sub_mem_of_smul_sub_mem _ ⊥ fun g ↦ sub_eq_zero.mpr (h_fixed g).symm
  rw [sub_eq_zero.mp ((Submodule.mem_bot BdRPlus).mp hc)]
  exact ⟨algebraMap_mem_hodgeFil_zero, (valueField 0).algebraMap_mem c⟩

@[simp]
lemma coord₀_one : k.coord₀ 1 = 1 := k.coord₀_coe 1

/-- Let `f : A_inf → S` be `S`-linear, and let the `v l` lie in `𝒦_a` = `valueField a`, the subfield
of `B_dR` generated over the fixed field of Γ' by the images of `S_B` and of φ^{-a} S. If the sum of
the `φ^{-a} (r l) * v l` lies in a `B_dR^+`-submodule `W` of `B_dR`, then so does the sum of the
`φ^{-a} (f (r l)) * v l`. -/
lemma sum_phiInvToBdR_map_mul_mem_of_mem_valueField (f : Ainf →ₗ[k.S] k.S) {ι : Type*} [Fintype ι]
    (v : ι → BdR) (r : ι → Ainf) (hv : ∀ l : ι, v l ∈ valueField a) {W : Submodule BdRPlus BdR}
    (h_sum : ∑ l : ι, phiInvToBdR a (r l) * v l ∈ W) :
    ∑ l : ι, phiInvToBdR a (f (r l)) * v l ∈ W := by
  -- Let `A` be the algebra generated over the constants by the products `b * φ^{-a} s`.
  let prod : k.bicommutant × k.S →* BdR := (algebraMap k.bicommutant BdR).toMonoidHom.coprod
    ((phiInvToBdR a).domRestrict k.S).toMonoidHom
  let A : Subalgebra (localFieldOf k.subgroup) BdR :=
    Algebra.adjoin (localFieldOf k.subgroup) (Set.range prod)
  -- Clear denominators: `𝒦_a` is the fraction field of `A`.
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
    fun l ↦ (⟨v l, hv l⟩ : IntermediateField.adjoin (localFieldOf k.subgroup) (Set.range prod))
  choose w hw using hd
  have hw (l : ι) : ((d : A) : BdR)⁻¹ * w l = v l := by
    simpa [Subtype.ext_iff, smul_def' (d : A), ← inv_mul_eq_iff_eq_mul₀] using! hw l
  -- The products form a monoid, so they span `A` over the constants.
  choose q _ c hc using fun l ↦ (mem_span_image_iff_exists_fun _).mp
    (by simpa using (adjoin_eq_span _ (Set.range prod)).le (w l).property :
      (w l : BdR) ∈ span (localFieldOf k.subgroup) (prod '' Set.univ))
  -- The conjugate `f' = φ^{-a} ∘ f ∘ φ^a` is again `S`-linear.
  let f' : Ainf →ₗ[k.S] Ainf :=
    { toFun x := (φ ^ a)⁻¹ • f (φ ^ a • x)
      map_add' := by simp
      map_smul' s x := by
        simpa [smul_def', inv_smul_eq_iff, Subtype.ext_iff] using
          f.map_smul ⟨φ ^ a • s, by simp [phi_pow_smul, ← k.coe_phi_pow]⟩ (φ ^ a • x) }
  -- Applying the extension of `f'` to `BPlus` multiplies the weighted sum by some `u : BdRPlus`.
  let term (i : Σ l, q l) : BPlus :=
    i.2.val.1 * Chart.ainfToBPlus ((φ ^ a)⁻¹ • i.2.val.2 • r i.1)
  obtain ⟨u, hu⟩ := k.isChartOf.dvd_extendToBPlus _
    (fun i : Σ l, q l ↦ (c i.1 i.2).property) f' term
  simp [term, f', k.extendToBPlus_mul, k.extendToBPlus_ainfToBPlus,
    -not_isEmpty_of_nonempty] at hu
  have h_mul : ∑ l, w l * phiInvToBdR a (f (r l)) =
      (∑ l, w l * phiInvToBdR a (r l)) * algebraMap BdRPlus BdR u := by
    with_unfolding_all
      simpa [← hc, prod, sum_mul, sum_sigma', smul_def', mul_assoc,
        -not_isEmpty_of_nonempty] using! congr(algebraMap BdRPlus BdR $hu)
  -- Multiply by `d⁻¹`: the new sum is `u` times the old one.
  have h_scale (z : ι → BdR) : ∑ l, z l * v l = ((d : A) : BdR)⁻¹ * ∑ l, w l * z l := by
    simp only [← hw, mul_sum, mul_assoc, mul_comm (z _)]
  convert smul_mem W u h_sum using 1
  rw [h_scale, h_scale, h_mul, Algebra.smul_def]
  ring

/-- Let `g` and `t 0, …, t (m - 1)` be elements of the Galois monoid of the chart, that is, elements
(0, γ) of ℤ × Γ with γ in the subgroup Γ', each acting through γ. Let `x` be an element of `𝒦_a`
(the subfield of `B_dR` generated over the fixed field of Γ' by `S_B` and φ^{-a} S) that lies in
Fil⁰ = B_dR^+. Suppose that for every `s` in `S`, `φ^a E` divides `g (∑ l, t l s) - ∑ l, t l s` in
A_inf; then `g (∑ l, t l x) - ∑ l, t l x` lies in Fil¹ = t B_dR^+. -/
lemma smul_sub_mem_hodgeFil_of_valueField {m : ℕ} (t : Fin m → k.galMonoid)
    (hx : x ∈ valueField a) (hx_int : x ∈ hodgeFil 0)
    (hg : ∀ s : k.S,
      (k.frobE a : Ainf) ∣ g • ∑ l : Fin m, t l • (s : Ainf) - ∑ l : Fin m, t l • (s : Ainf)) :
    g • ∑ l : Fin m, t l • x - ∑ l : Fin m, t l • x ∈ hodgeFil 1 := by
  -- By density, `p ^ e * x ≡ r` modulo `hodgeFil 1` for some `e` and some `r` in `Ainf`.
  obtain ⟨y, hy⟩ : ∃ y : BdRPlus, algebraMap BdRPlus BdR y = x := by
    simpa using mem_hodgeFil.mp hx_int
  obtain ⟨e, r, hr⟩ : ∃ e : ℕ, ∃ r : Ainf,
      algebraMap Ainf BdRPlus xi ^ 1 ∣ p ^ e * y - algebraMap Ainf BdRPlus r :=
    y.exists_Ainf_approx 1
  -- Read this as a relation with coefficients `1`, `φ ^ a • r` between `p ^ e • x` and `-1`, and
  -- apply the retraction `k.coord₀ : Ainf → S` to the coefficients: `r` is replaced by `φ^{-a} s`.
  let s : k.S := k.coord₀ (φ ^ a • r)
  have h_rel : ∑ l : Fin 2, phiInvToBdR a (![1, φ ^ a • r] l) * ![p ^ e • x, -1] l ∈
      hodgeFil 1 := by
    simpa [phiInvToBdR, ← hy, sub_eq_add_neg, IsScalarTower.algebraMap_apply Ainf BdRPlus BdR] using
      algebraMap_mem_hodgeFil_iff_xi_pow_dvd.mpr hr
  have approx : p ^ e • x - phiInvToBdR a s ∈ hodgeFil 1 := by
    simpa [← sub_eq_add_neg] using sum_phiInvToBdR_map_mul_mem_of_mem_valueField k.coord₀
      ![p ^ e • x, -1]
      ![1, φ ^ a • r] (Fin.forall_fin_two.mpr ⟨nsmul_mem hx (p ^ e), neg_mem (one_mem _)⟩) h_rel
  -- By `hg` the claim holds for `φ^{-a} s`, hence for `p ^ e • x`; `p` is prime to `k.frobE a`.
  refine (mul_mem_hodgeFil_iff_of_not_frobE_dvd (not_frobE_dvd_p a) e).mp ?_
  have h_fix_s :
      phiInvToBdR a (g • ∑ l, t l • (s : Ainf) - ∑ l, t l • (s : Ainf)) ∈ hodgeFil 1 :=
    phiInvToBdR_mem_hodgeFil_one_iff.mpr (hg s)
  have approx_sum : ∑ l, t l • (p ^ e • x - phiInvToBdR a s) ∈ hodgeFil 1 :=
    sum_mem fun l _ ↦ galMonoid_smul_mem_hodgeFil (t l) approx
  have h_fix_approx : g • ∑ l, t l • (p ^ e • x - phiInvToBdR a s) ∈ hodgeFil 1 :=
    galMonoid_smul_mem_hodgeFil g approx_sum
  -- `p ^ e` times the claim is the sum of `h_fix_approx` and `h_fix_s` minus `approx_sum`
  simpa [mul_sub, mul_sum, smul_sum, smul_sub, ← sub_eq_add_neg] using
    sub_mem (add_mem h_fix_approx h_fix_s) approx_sum

end KummerChart

end New.Lift

end
end
end

/-!
# Kisin modules of Kummer charts: lattices with jump sets, letter projectors, invariant forms

For a Kummer chart `k : New.Lift.KummerChart Γ` there is a ring S ⊂ A_inf, the image of Λ⟦X⟧ with
Λ = W(𝔽_{p^f}), and a subgroup Γ' of Γ. Kisin modules are defined inside `L.Ambient = W(C^♭) ⊗ L`
for a lattice L with prescribed jump sets. The objects are functorial in L and compatible with
Frobenius and with Γ'. They split according to the letters `i ∈ 𝔽_{p^f}ˣ`, on which the root of
unity ζ of the coefficients acts as the Teichmüller lift `ω i = letterTeich i`.

## Main definitions and results

* `New.Lift.KummerChart.Letter`: the letters, the units i of 𝔽_{p^f}. For coefficients O with
  ζ^(p^f − 1) = 1 (`New.Lift.KummerChart.Coeffs`), the letter i cuts out the part
  `New.Lift.KummerChart.JumpLattice.letterPart` where ζ = [i].
* `New.Lift.KummerChart.JumpLattice`: a lattice L, crystalline over Γ', with a finite set
  `jumpSet i` of integers for each letter that holds its jumps at the embeddings above i.
* `New.Lift.KummerChart.JumpLattice.forms`: forms, A_inf-linear maps to B_dR that are Γ'-equivariant
  on 1 ⊗ L.
* `New.Lift.KummerChart.JumpLattice.kisinAinf`, `New.Lift.KummerChart.JumpLattice.kisinModule`,
  `New.Lift.KummerChart.JumpLattice.kisinLoc`: an A_inf-module cut out by forms, the Kisin module N,
  and N with all φ^a E inverted.
* `New.Lift.KummerChart.JumpLattice.mem_letterPart_iff_letterProj`,
  `New.Lift.KummerChart.JumpLattice.sum_letterProj`: `e i = letterProj i` projects onto the letter
  `i`, and the `e i` sum to the identity.
* `New.Lift.KummerChart.JumpLattice.exists_span_formsOfType_mod_pred`: the functionals of type `u`
  at `i`, modulo those of type `u - 1`, are spanned over Q̄_p by at most `L.jumpMultiplicity i u` of
  them.
* `New.Lift.KummerChart.JumpLattice.formsOfType_subset_pred_of_notMem`: if `n ∉ L.jumpSet i`, the
  functionals of type `n` at `i` are of type `n - 1`.

Notions from other files:
* `New.Lift.KummerChart`: a chart Λ⟦X⟧ → A_inf (ring `S`, element `E` generating ker θ,
  `frobE a` = φ^a(E)) together with a subgroup Γ' of Γ whose fixed field it belongs to.
* `New.Lift.GalLattice`: a finite free O-module with an O-linear representation of Γ.
* `New.Period.WittCFlat`: the ring W(C^♭) of p-typical Witt vectors over the fraction field C^♭ of
  the tilt O^♭ of the ring of integers of C_p.
* `New.Period.overZp`: a representation of Γ on a module T over a Z_p-algebra R, regarded as a
  Z_p-linear representation.
* `New.Period.jump`: the multiplicity of a Hodge–Tate jump u of a representation at an embedding γ
  of the coefficients into ℂ_p.

## Relation to the literature

Known result: Hodge–Tate weights of Kisin modules. This is the analogue, for the Kisin module of one
Kummer chart inside A_inf, of the statements on Wach modules in the literature. This file proves
only the bounds on the weights, not that the Galois action is trivial modulo the variable. It holds
per unramified embedding of the coefficients, and it gives only upper bounds by the multiplicity of
each jump.
Source: L. Berger, Limites de représentations cristallines, Compositio Math. 140 (2004), 1473–1498,
§III; N. Wach, Représentations p-adiques potentiellement cristallines, Bull. SMF 124 (1996),
375–400.

See also `Lib.PadicHodge.Kisin.PeriodMatrixFrame`.
-/

@[expose] public section

noncomputable section

/-!
## Letters, lattices with jump sets, forms and Kisin modules

* `New.Lift.saturateBy`: the saturation of a submodule P by a submonoid M, the x with mx in P for
  some m in M.
* `New.Lift.KummerChart.Letter`, `New.Lift.KummerChart.Coeffs`,
  `New.Lift.KummerChart.JumpLattice`: the letters, rings of coefficients with a root ζ, and
  lattices with jump sets.
* `New.Lift.KummerChart.JumpLattice.letterOp`, `letterPart`, `letterProj`: the operator ω(i)⁻¹ζ,
  the part at the letter i, and the projector onto it.

Conventions: `New.Lift.FrobGroup Γ` = ℤ × Γ acts on W(C^♭) ⊗ L, with φ the Frobenius;
`DiagTensor.mk 1 t` is 1 ⊗ t; `hodgeFil n` is tⁿB_dR^+; E is an element of S, a generator of ker θ,
and `k.frobE a` is φ^a E.
-/

namespace New.Lift

open Period WittVector Submodule Set FrobGroup Module Fintype Algebra

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] [k : KummerChart Γ]
  {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X] {Q : Submodule R X}

/-! ### Saturation of a submodule -/

/-- The saturation of a submodule P of X by a submonoid M: the x in X with mx in P for some m in
M. -/
def saturateBy (M : Submonoid R) (P : Submodule R X) : Submodule R X :=
  -- the preimage of the `M`-torsion of `X ⧸ P`, with its carrier written out
  ((torsion' R (X ⧸ P) M).comap P.mkQ).copy {x : X | ∃ r ∈ M, r • x ∈ P}
    (by simp [← Quotient.mk_smul])

lemma mem_saturateBy_of_mem {M : Submonoid R} {x : X} (hx : x ∈ Q) : x ∈ saturateBy M Q :=
  ⟨1, one_mem M, by simpa using hx⟩

/-- If `r` divides an element `s` of `M` and `r • x` lies in the saturation of `Q` by `M`, then
so does `x`. -/
lemma mem_saturateBy_of_smul {M : Submonoid R} {r s : R} {x : X} (hrs : r ∣ s) (hs : s ∈ M)
    (hx : r • x ∈ saturateBy M Q) : x ∈ saturateBy M Q := by
  obtain ⟨c, rfl⟩ := hrs
  obtain ⟨a, ha, hax⟩ : ∃ a ∈ M, a • r • x ∈ Q := hx
  -- `(a * (r * c)) • x = c • a • r • x`
  exact ⟨a * (r * c), mul_mem ha hs, by simpa [mul_smul, smul_comm c] using smul_mem Q c hax⟩

/-- Induction on the saturation by the monoid generated by the f(a): a property that holds on Q
and passes from f(a)·x to x holds on all of the saturation. -/
@[elab_as_elim]
lemma saturateBy_induction {ι : Sort*} {x : X} {f : ι → R} {C : X → Prop}
    (hx : x ∈ saturateBy (Submonoid.closure (range f)) Q) (h₀ : ∀ x ∈ Q, C x)
    (h₁ : ∀ (a : ι) (x : X), C (f a • x) → C x) : C x := by
  obtain ⟨r, hr, hrx⟩ : ∃ r ∈ Submonoid.closure (range f), r • x ∈ Q := hx
  -- Induction on the number of factors `f a` in `r`, where `r • x ∈ Q`.
  induction hr using Submonoid.closure_induction_right generalizing x with
  | one => exact h₀ x (by simpa using hrx)
  | mul_right r _ s hs ih =>
    obtain ⟨a, rfl⟩ := hs
    exact h₁ a x (ih (by simpa [mul_smul] using hrx))

namespace KummerChart

/-! ### Letters, coefficients and lattices with jump sets -/

/-- The letters of a Kummer chart: the multiplicative group of the field with p^f elements in
O^♭. A letter i singles out the embeddings g of a ring of coefficients into ℂ_p with g(ζ) = θ([i]),
[i] the Teichmüller lift; these are the embeddings above i, and φ^a sends [i] to [i^(p^a)]. -/
def Letter : Type := (flatFq k.f)ˣ
  deriving CommGroup, Finite, IsCyclic

/-- The letters form a finite type. -/
instance : Fintype Letter := .ofFinite _

/-- The number `p ^ f - 1` of letters is invertible in `ℤ_[p]`, being a unit modulo `p`. -/
instance : Invertible (card Letter : ℤ_[p]) :=
  IsUnit.invertible <| .of_map PadicInt.toZMod _ <| by
    simp [↓card_eq_nat_card, Letter, Nat.card_units, NeZero.pos, ZMod.natCast_self]

/-- The permutation i ↦ i^p of the letters, the units of the field with p^f elements. -/
def letterFrob : Equiv.Perm Letter :=
  (Units.mapEquiv (frobeniusEquiv (flatFq k.f) p).toMulEquiv).toEquiv

/-- The multiplicative map sending a letter to its Teichmüller lift in the Witt vectors of the
field with p^f elements, viewed in the ring S of the chart. -/
def letterTeich : Letter →* k.S :=
  (algebraMap (WittFq k.f) k.S).toMonoidHom.comp ((teichmuller p).comp (Units.coeHom (flatFq k.f)))

/-- The elements ζ of O with ζ^q = 1, where q = p^f − 1 is the number of letters of the chart. -/
abbrev LetterRoot (O : Type*) [Monoid O] : Type _ := {ζ : O // ζ ^ Nat.card Letter = 1}

/-- A ring of coefficients: a finite free Z_p-algebra O with an element ζ, ζ^{p^f−1} = 1, which
cuts out the letters. -/
structure Coeffs where
  /-- The ring of coefficients O. -/
  (O : Type)
  /-- O is a commutative ring. -/
  [commRing : CommRing O]
  /-- O is a ℤ_p-algebra. -/
  [padicIntegerRing : PadicIntegerRing O p]
  /-- An element ζ of O with ζ^(p^f − 1) = 1. -/
  ζ : LetterRoot O

attribute [instance] Coeffs.commRing Coeffs.padicIntegerRing

-- A ring of coefficients is read as its underlying type.
instance : CoeSort Coeffs Type := ⟨Coeffs.O⟩

/-- A lattice with jump sets: a finite free O-module with an action of Γ, crystalline over Γ', with,
for each letter i, a finite set of integers that contains its jumps at every embedding g of O with
g(ζ) = θ(ω(i)). -/
structure JumpLattice (O : Coeffs) extends toGalLattice : GalLattice O Γ where
  /-- For each letter, a finite set of integers that holds the jumps at that letter. -/
  jumpSet : Letter → Finset ℤ
  /-- One set of integers for each embedding of O. -/
  embJumps : (O →ₐ[ℤ_[p]] ℂ_[p]) → Finset ℤ
  /-- The lattice is crystalline over Γ' and has its jumps at each embedding in the set given for
  that embedding. -/
  inClass : InClass (Filter.map k.subgroup.subtype ⊤) ⊥ embJumps toGalLattice
  /-- The set at a letter i contains the set of every embedding g with g(ζ) = θ(ω(i)). -/
  embJumps_subset {g : O →ₐ[ℤ_[p]] ℂ_[p]} {i : Letter} :
      g O.ζ = (theta (k.letterTeich i)).val → embJumps g ⊆ jumpSet i

variable {k} {O : Coeffs} {L : JumpLattice O} (L' : JumpLattice O) (i : Letter) (l a : ℕ) (u : ℤ)

/-- The letter a steps before i: the image of i under the a-th power of the inverse of the
permutation x ↦ x^p, so that φ^a sends its Teichmüller lift to that of i. -/
@[simp]
abbrev Letter.stepBack : Letter := (k.letterFrob ^ a)⁻¹ i

/-- The standard exponent at the step `a` for the level `l` and the weight `u`: `0` for `a < l`
and `-u` for `a ≥ l`. -/
@[grind]
def stdOrders : ℤ := if a < l then 0 else -u

namespace JumpLattice

/-! ### Forms and the Kisin module -/

/-- The module W(C^♭)⊗L for the lattice underlying L. -/
abbrev Ambient : Type := DiagTensor (Rep.of (overZp L.ρ))

/-- For an O-linear map F: L → L' of lattices, the W(C^♭)-linear map W(C^♭) ⊗ L → W(C^♭) ⊗ L'
obtained by extension of scalars. -/
abbrev wittMap (F : L.Carrier →ₗ[O] L'.Carrier) : L.Ambient →ₗ[WittCFlat] L'.Ambient :=
  DiagTensor.map F

/-- The A_inf-submodule of W(C^♭) ⊗ L spanned by the elements 1 ⊗ y, y in L. -/
def ainfLattice : Submodule Ainf L.Ambient := span Ainf (M := L.Ambient) (range (DiagTensor.mk 1))

/-- The type of A_inf-linear maps from W(C^♭) ⊗ L to B_dR. -/
abbrev Functional : Type := L.Ambient →ₗ[Ainf] BdR

/-- The set of A_inf-linear maps μ: W(C^♭) ⊗ L → B_dR that are Γ'-equivariant on 1 ⊗ L, that is,
μ(1 ⊗ gt) = g·μ(1 ⊗ t). -/
def forms : Set L.Functional :=
  {μ : L.Functional | ∀ (t : L.Carrier) (g : k.subgroup),
    μ (DiagTensor.mk 1 (L.ρ g t)) = toGp g.val • μ (DiagTensor.mk 1 t)}

/-- The action of m ∈ ℤ × Γ on W(C^♭) ⊗ L is semilinear: m • (r • x) = (m • r) • (m • x). -/
lemma frobGroup_smul_smul (m : FrobGroup Γ) (r : Ainf) (x : L.Ambient) :
    m • r • x = (m • r) • m • x := smul_distrib_smul m r x

/-- The action of an element m of ℤ × Γ on W(C^♭) ⊗ L, as a map semilinear for the action of m
on A_inf. -/
@[simps]
def semilinearAct (m : FrobGroup Γ) :
    L.Ambient →ₛₗ[MulSemiringAction.toRingHom (FrobGroup Γ) Ainf m] L.Ambient where
  toFun x := m • x
  map_add' := smul_add m
  map_smul' := frobGroup_smul_smul m

/-- The A_inf-module of the x in A_inf[1/τ] ⊗ L (some power of the element `tau` of A_inf sends x
into the A_inf-span of the 1 ⊗ y, y in L) with μ(φ^n x) in B_dR^+ for all n ≥ 1 and all μ in
`New.Lift.KummerChart.JumpLattice.forms`. -/
def kisinAinf : Submodule Ainf L.Ambient :=
  saturateBy (Submonoid.powers tau) L.ainfLattice ⊓
    { carrier := {x : Ambient | ∀ n : ℕ, ∀ μ ∈ L.forms, μ (φ ^ (n + 1) • x) ∈ hodgeFil 0}
      add_mem' := by aesop
      zero_mem' := by simp
      smul_mem' := by simp_all [frobGroup_smul_smul, smul_of_tower_mem] }

/-- The invariant functionals μ (`New.Lift.KummerChart.JumpLattice.forms`) whose restriction to
1 ⊗ L comes from a Z_p-linear map of L into the period ring `Bmax`. -/
def crysForms : Set L.Functional :=
  {μ ∈ L.forms | ∃ l : L.Carrier →ₗ[ℤ_[p]] Bmax, ∀ t : Rep.of (overZp L.ρ),
    μ (DiagTensor.mk 1 t) = algebraMap Bmax BdR (l t)}

/-- For an A_inf-submodule Q of W(C^♭) ⊗ L, the S-submodule of the x in Q on which every form in
`New.Lift.KummerChart.JumpLattice.forms` takes values in the field 𝒦₀ = `valueField 0`, a subfield
of B_dR that contains the image of S. -/
def valueFieldPoints (Q : Submodule Ainf L.Ambient) : Submodule k.S L.Ambient where
  carrier := {x ∈ Q | ∀ μ ∈ L.forms, μ x ∈ valueField 0}
  add_mem' := by aesop
  zero_mem' := by simp
  smul_mem' s x hx := by
    obtain ⟨hx_mem, hx_val⟩ := hx
    refine ⟨smul_mem _ _ hx_mem, fun μ hμ ↦ ?_⟩
    -- `μ (s • x)` is the product of the image of `s` and `μ x`, both in `valueField 0`
    simpa [phiInvToBdR, smul_def', IsScalarTower.algebraMap_apply k.S Ainf BdR] using
      mul_mem (phiInvToBdR_mem_valueField s) (hx_val μ hμ)

/-- The Kisin module of L: the S-module of the x in `New.Lift.KummerChart.JumpLattice.kisinAinf` on
which all Γ'-equivariant forms take values in the field 𝒦₀ (`New.Lift.KummerChart.valueField`). -/
abbrev kisinModule : Submodule k.S L.Ambient := valueFieldPoints L.kisinAinf

/-- The image of `New.Lift.KummerChart.JumpLattice.kisinAinf` under φ^l. It is the A_inf-submodule
of the x in W(C^♭)⊗L with φ^{−l}x in `New.Lift.KummerChart.JumpLattice.kisinAinf`. -/
def frobKisinAinf : Submodule Ainf L.Ambient := L.kisinAinf.comap (semilinearAct (φ ^ l)⁻¹)

/-- The x in W(C^♭) ⊗ L that some product of the φ^a E multiplies into
`New.Lift.KummerChart.JumpLattice.kisinAinf`. -/
def kisinLocAinf : Submodule Ainf L.Ambient :=
  saturateBy (Submonoid.closure (range fun a ↦ (k.frobE a).val)) L.kisinAinf

/-- The Kisin module N with all φ^a E inverted: the x in
`New.Lift.KummerChart.JumpLattice.kisinLocAinf` on which all forms take values in the field 𝒦₀. -/
def kisinLoc : Submodule k.S L.Ambient := L.valueFieldPoints kisinLocAinf

/-! ### Equivariant maps -/

/-- A Γ-equivariant O-linear map L → L' between lattices over the same coefficients O. -/
abbrev Hom : Type := L.ρ.IntertwiningMap L'.ρ

/-- For an equivariant map F : L → L', the W(C^♭)-linear map W(C^♭)⊗L → W(C^♭)⊗L' obtained by
extension of scalars. -/
abbrev Hom.wittMap {L' : JumpLattice O} (F : L.Hom L') : L.Ambient →ₗ[WittCFlat] L'.Ambient :=
  L.wittMap L' F.toLinearMap

/-- Scalar multiplication on L by the root of unity ζ of the coefficient ring O, as an
equivariant map from L to itself. -/
def mulZeta : L.Hom L := ⟨LinearMap.lsmul O L.Carrier O.ζ, by aesop⟩

/-- The endomorphism ω(i)⁻¹ζ of W(C^♭) ⊗ L, with ζ acting through L and ω(i), the Teichmüller
lift of the letter i, as a scalar. -/
def letterOp : L.Ambient →ₗ[WittCFlat] L.Ambient := k.letterTeich i⁻¹ • L.mulZeta.wittMap

/-- The part of W(C^♭) ⊗ L at the letter i: the A_inf-submodule on which ζ acts as the
Teichmüller lift ω(i). -/
def letterPart : Submodule Ainf L.Ambient := (L.letterOp i - 1).ker.restrictScalars Ainf

/-- The endomorphism q⁻¹ Σ_{n<q} (ω(i)⁻¹ζ)^n of W(C^♭) ⊗ L, q = p^f − 1; as ζ^q = 1 it
projects to the part at the letter i. -/
def letterProj : L.Ambient →ₗ[WittCFlat] L.Ambient :=
  ⅟(card Letter : ℤ_[p]) • ∑ n ∈ Finset.range (card Letter), L.letterOp i ^ n

/-- The A_inf-linear μ: W(C^♭) ⊗ L → B_dR that are Γ'-equivariant on 1 ⊗ L and send the
projection of 1 ⊗ L to the letter i into t^{−u}B_dR^+. -/
def formsOfType : Set L.Functional :=
  {μ ∈ L.forms | ∀ t : Rep.of (overZp L.ρ), μ (L.letterProj i (DiagTensor.mk 1 t)) ∈ hodgeFil (-u)}

open scoped Classical in
/-- The total multiplicity of the Hodge–Tate jump u of L over all embeddings γ of O in ℂ_p above
the letter i, that is, with γ(ζ) = θ(ω(i)). -/
abbrev jumpMultiplicity : ℕ :=
  ∑ γ : O.O →ₐ[ℤ_[p]] ℂ_[p] with γ O.ζ = ↑(theta (k.letterTeich i)), jump L.ρ γ u

/-- The x in W(C^♭) ⊗ L that some non-zero divisor of A_inf multiplies into the A_inf-span of
the elements 1 ⊗ y, y in L. -/
abbrev fracSpan : Submodule Ainf L.Ambient := saturateBy (nonZeroDivisors Ainf) L.ainfLattice

/-- The least natural number a such that all Hodge–Tate jumps of L, as a Z_p-representation of
Γ', lie in [−a, a]; it is 0 if there is none. -/
def jumpBound : ℕ :=
  sInf {a : ℕ | ∀ u : ℤ,
    jump ((overZp L.ρ).comp k.subgroup.subtype) (ofId ℤ_[p] ℂ_[p]) u ≠ 0 → -a ≤ u ∧ u ≤ a}

/-- For an A_inf-linear μ: W(C^♭) ⊗ L → B_dR, the map μ ∘ φ^{−a}, semilinear for φ^{−a}: A_inf →
B_dR. -/
def valueAt (μ : L.Functional) : L.Ambient →ₛₗ[phiInvToBdR a] BdR where
  toAddHom := μ.toAddHom.comp (semilinearAct (φ ^ a)⁻¹).toAddHom
  map_smul' := by simp [phiInvToBdR, smul_def']

end JumpLattice

end KummerChart

end New.Lift

/-!
## Letter projectors, functoriality, and forms of a given type

A functional is an `A_inf`-linear map `L.Ambient → B_dR`. It is invariant (`forms`) if it is
`Γ'`-equivariant on `1 ⊗ L`. It is of type `u` at `i` (`formsOfType`) if moreover it maps
`letterProj i (1 ⊗ L)` into `t ^ (-u) B_dR⁺`.
-/

namespace New.Lift.KummerChart.JumpLattice

open Period WittVector Submodule Set FrobGroup Module RingHom Finset Algebra

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
  {k : KummerChart Γ} {O : Coeffs} {L L' : JumpLattice O} {l a b : ℕ} {i i' : Letter} {n : ℤ}
  {x : L.Ambient} (g : k.galMonoid) (F : L.Hom L') (m : FrobGroup Γ) {μ : L.Functional}

/-- The map `W(C^♭) ⊗ L → W(C^♭) ⊗ L'` induced by an equivariant `F` commutes with the action of
`m` in ℤ × Γ. -/
@[simp] lemma Hom.wittMap_smul (x : L.Ambient) : F.wittMap (m • x) = m • F.wittMap x := by
  induction x using DiagTensor.induction with
  | h_mk a t => simp [F.isIntertwining]
  | h_add x y hx hy => simp [hx, hy]

/-- The map induced by an O-linear `F : L → L'` sends the A_inf-span of the `1 ⊗ y`, y in L, into
the corresponding span for L'. -/
lemma wittMap_mem_ainfLattice (F : L.Carrier →ₗ[O.O] L'.Carrier) :
    x ∈ L.ainfLattice → L.wittMap L' F x ∈ L'.ainfLattice := fun hx ↦
  mapsTo_span (f := (L.wittMap L' F).restrictScalars Ainf) (by simp) hx

/-- Composing an invariant functional on `L'` with the map induced by `F` gives an invariant
functional on `L`. -/
lemma Hom.comp_wittMap_mem_forms {μ : L'.Functional} :
    μ ∈ L'.forms → μ ∘ₗ F.wittMap ∈ L.forms := by
  intro hμ t g
  -- `F.wittMap (1 ⊗ t) = 1 ⊗ F t`, and `F` commutes with `ρ g`.
  simpa [F.isIntertwining] using hμ (F t) g

/-- Let `F : L → L'` be an equivariant map of lattices with jump sets, and let
`F.wittMap : W(C^♭) ⊗ L → W(C^♭) ⊗ L'` be its extension of scalars. Then `F.wittMap` sends
`L.kisinAinf` into `L'.kisinAinf`. Here `kisinAinf` is the A_inf-module of those x in A_inf[1/τ] ⊗ L
with μ(φ^n x) ∈ B_dR^+ for all n ≥ 1 and all μ in `forms`. -/
lemma Hom.wittMap_mem_kisinAinf : x ∈ L.kisinAinf → F.wittMap x ∈ L'.kisinAinf := by
  rintro ⟨⟨r, hr, hrx⟩, h_fil⟩
  -- `F.wittMap` commutes with `r` and maps the lattice of `L` into that of `L'`.
  have h_lattice : r • F.wittMap x ∈ L'.ainfLattice := by
    simpa using wittMap_mem_ainfLattice F.toLinearMap hrx
  refine ⟨⟨r, hr, h_lattice⟩, fun n μ hμ ↦ ?_⟩
  -- `F.wittMap` commutes with `φ`, and `μ ∘ F.wittMap` is again invariant
  simpa [F.wittMap_smul] using h_fil n _ (F.comp_wittMap_mem_forms hμ)

/-- The map induced by an equivariant `F : L → L'` sends the Kisin module of L into that of L'. -/
lemma Hom.wittMap_mem_kisinModule (hx : x ∈ L.kisinModule) : F.wittMap x ∈ L'.kisinModule := by
  obtain ⟨hx_ainf, hx_value⟩ := hx
  exact ⟨F.wittMap_mem_kisinAinf hx_ainf, fun μ hμ ↦ hx_value _ (F.comp_wittMap_mem_forms hμ)⟩

/-- The map induced by an equivariant `F : L → L'` sends `L.frobKisinAinf l`, the image of
`L.kisinAinf` under φ^l, into `L'.frobKisinAinf l`. -/
lemma Hom.wittMap_mem_frobKisinAinf :
    x ∈ L.frobKisinAinf l → F.wittMap x ∈ L'.frobKisinAinf l := fun hx ↦ by
  simpa [frobKisinAinf] using F.wittMap_mem_kisinAinf hx

/-! ### The projectors to the letters -/

/-- The n-th power of `letterOp i`, that is of ω(i)⁻¹ζ, on a pure tensor `a ⊗ t`. -/
@[simp]
lemma letterOp_pow_mk (n : ℕ) (a : WittCFlat) (t : Rep.of (overZp L.ρ)) :
    (L.letterOp i ^ n) (no_index (DiagTensor.mk a t)) =
      k.letterTeich i⁻¹ ^ n • .mk a (O.ζ.val ^ n • t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih]
    simp [letterOp, pow_succ', mulZeta, smul_smul, mul_comm]

/-- x lies in the part at the letter i exactly when ζ acts on it as the Teichmüller lift ω(i). -/
lemma mem_letterPart_iff_mulZeta :
    x ∈ letterPart i ↔ L.mulZeta.wittMap x = k.letterTeich i • x :=
  sub_eq_zero.trans (inv_smul_eq_iff (g := k.letterTeich.toHomUnits i))

/-- The ring S of the chart acts on W(C^♭) ⊗ L through its inclusion in A_inf. -/
lemma smul_eq_val_smul (s : k.S) : s • x = s.val • x := rfl

/-- The map induced by an equivariant `F : L → L'` commutes with the projectors to the letter i. -/
@[simp] lemma Hom.wittMap_letterProj (x : L.Ambient) :
    F.wittMap (L.letterProj i x) = L'.letterProj i (F.wittMap x) := by
  induction x using DiagTensor.induction with
  | h_mk a t => simp [letterProj]
  | h_add x y hx hy => simp [hx, hy]

/-- If `m` in ℤ × Γ sends ω(i)⁻¹ to ω(i')⁻¹, it carries the projector to the letter i into the
projector to the letter i'. -/
lemma smul_letterProj {m : FrobGroup Γ}
    (h_teich : m • (k.letterTeich i⁻¹).val = k.letterTeich i'⁻¹) (x : L.Ambient) :
    m • L.letterProj i x = L.letterProj i' (m • x) := by
  induction x using DiagTensor.induction with
  | h_mk a t => simp [letterProj, smul_comm m, smul_sum, smul_eq_val_smul, h_teich,
    frobGroup_smul_smul]
  | h_add x y hx hy => simp [hx, hy]

/-- An element `g` of the Galois monoid of the chart commutes with the projector to each letter. -/
lemma gal_smul_letterProj (x : L.Ambient) :
    g.val • L.letterProj i x = L.letterProj i (g.val • x) := by
  -- `g` comes from `Γ'`, which fixes the Teichmüller lift `letterTeich i⁻¹`
  obtain ⟨γ, hγ⟩ := g.property
  refine smul_letterProj ?_ x
  rw [← hγ]
  exact (fixes γ).1 _

/-- φ^l sends ω(i)⁻¹ to ω(j)⁻¹, where j is the image of i under the l-th power of i ↦ i^p. -/
lemma phi_pow_smul_letterTeich :
    φ ^ l • (k.letterTeich i⁻¹).val = k.letterTeich ((k.letterFrob ^ l) i)⁻¹ := by
  -- `φ ^ l` raises the Teichmüller lift `letterTeich i⁻¹` to the power `p ^ l`, as `letterFrob ^ l`
  -- does with `i`.
  rw [phi_pow_smul, k.letterFrob.coe_pow]
  change _ = (k.letterTeich (((fun j : Letter ↦ j ^ p)^[l] i)⁻¹)).val
  rw [pow_iterate]
  change _ = (k.letterTeich ((i ^ p ^ l)⁻¹)).val
  rw [← inv_pow, map_pow, k.S.coe_pow]
  let a : flatFq k.f := (↑(i⁻¹ : (flatFq k.f)ˣ) : flatFq k.f)
  have h_teich : (k.letterTeich i⁻¹).val =
      teichmuller p (algebraMap (flatFq k.f) OFlat a) := by
    exact map_teichmuller _ _ _
  rw [h_teich, iterate_frobEnd_teichmuller]

/-- The projector to the letter i takes values in the part at the letter i. -/
lemma letterProj_mem_letterPart : L.letterProj i x ∈ letterPart i := by
  -- Let `q` be the order of `k.Letter`. The geometric sum gives
  -- `(letterOp i - 1) * ∑ n < q, letterOp i ^ n = letterOp i ^ q - 1`, and `letterOp i ^ q = 1`
  -- because `ζ ^ q = 1` and `i⁻¹ ^ q = 1`.
  have hζ : O.ζ.val ^ Fintype.card k.Letter = 1 := by simpa using O.ζ.property
  have h_order (y : L.Ambient) : (L.letterOp i ^ Fintype.card k.Letter) y = y := by
    induction y using DiagTensor.induction with
    | h_mk a t => simp [← map_pow, hζ, map_one]
    | h_add y z hy hz => rw [map_add, hy, hz]
  change ((L.letterOp i - 1) * L.letterProj i) x = 0
  simp [letterProj, mul_geom_sum, h_order]

/-- x lies in the part at the letter i exactly when the projector to i fixes it. -/
lemma mem_letterPart_iff_letterProj : x ∈ letterPart i ↔ L.letterProj i x = x := by
  constructor
  · -- if `letterOp i` fixes `x`, so do its powers, and `letterProj i` is their average
    intro hx
    simp_all [letterProj, pow_apply_eq_iterate, letterPart, Function.iterate_fixed, sub_eq_zero,
      invOf_smul_eq_iff, Nat.cast_smul_eq_nsmul]
  · intro h_fixed
    simpa [h_fixed] using (letterProj_mem_letterPart : L.letterProj i x ∈ letterPart i)

/-- The part at each letter is stable under the Galois monoid of the chart, in both directions. -/
lemma gal_smul_mem_letterPart : g • x ∈ letterPart i ↔ x ∈ letterPart i := by
  simp [mem_letterPart_iff_letterProj, k.galMonoid.smul_def, ← gal_smul_letterProj,
    smul_left_cancel_iff]

/-- `φ ^ a • x` lies in the part at the letter i exactly when x lies in the part at `i.stepBack a`,
the letter whose `p ^ a`-th power is i. -/
lemma phi_pow_smul_mem_letterPart_iff :
    φ ^ a • x ∈ letterPart i ↔ x ∈ letterPart (i.stepBack a) := by
  have h_comm (y : L.Ambient) :
      φ ^ a • L.letterProj (i.stepBack a) y = L.letterProj i (φ ^ a • y) := by
    simpa using smul_letterProj (phi_pow_smul_letterTeich (l := a) (i := i.stepBack a)) y
  simp [mem_letterPart_iff_letterProj, ← h_comm, smul_left_cancel_iff]

/-! ### Small facts on the Kisin module and the constants -/

lemma frobKisinAinf_zero : L.frobKisinAinf 0 = L.kisinAinf := by
  simp [frobKisinAinf, Submodule.ext_iff]

/-- The unit `frobEUnit a` acts by the element φ^a E of S, also on powers. -/
lemma frobEUnit_pow_smul (n : ℕ) : k.frobEUnit a ^ n • x = (k.frobE a).val ^ n • x := by
  simp [Units.smul_def, frobEUnit, ← map_pow]

omit Γ in
/-- The Witt vectors of the field with p^f elements have rank f over ℤ_p. -/
lemma finrank_wittFq {f : ℕ+} : Module.finrank ℤ_[p] (WittFq f) = f := by
  -- Count the quotient modulo `p` in two ways: it has `p ^ finrank` elements, and it is the
  -- residue field `flatFq f`, which has `p ^ f` elements.
  have h_ideal : pPowMultiples (WittFq f) 1 = (Ideal.span {(p : WittFq f)}).toAddSubgroup :=
    AddSubgroup.ext fun y ↦ by simp [mem_span_singleton, mul_comm, Nat.cast_smul_eq_nsmul]
  have h_index : (pPowMultiples (WittFq f) 1).index = Nat.card (flatFq f) :=
    (congrArg AddSubgroup.index h_ideal).trans (Nat.card_congr quotientPEquiv.toEquiv)
  simpa [Nat.pow_right_inj Fact.out] using h_index

lemma zTauUnit_smul : k.zTauUnit • x = k.zTau • x := (rfl)

@[simp]
lemma frobEUnit_smul : k.frobEUnit a • x = (k.frobE a).val • x := (rfl)

/-- The B_dR-linear map sending μ: W(C^♭) ⊗ L → B_dR to the vector of its values μ(1 ⊗ e_l) on a
chosen Z_p-basis (e_l) of L. -/
noncomputable def basisValues : L.Functional →ₗ[BdR] Fin (Module.finrank ℤ_[p] L.Carrier) → BdR :=
  LinearMap.pi fun l ↦ LinearMap.applyₗ' BdR
    (DiagTensor.mk 1 (finBasis ℤ_[p] (Rep.of (overZp L.ρ)) l))

/-- The A_inf-span of the `1 ⊗ y`, y in L, is spanned by the `1 ⊗ e_l` for the chosen ℤ_p-basis
(e_l) of L. -/
lemma ainfLattice_eq_span_basis :
    L.ainfLattice = span Ainf
      (Set.range (DiagTensor.mk 1 ∘ finBasis ℤ_[p] (Rep.of (overZp L.ρ)))) := by
  -- the vectors `1 ⊗ t` are the `ℤ_[p]`-span of those with `t` in the basis
  rw [← span_span_of_tower ℤ_[p], range_comp, ← map_span, Module.Basis.span_eq, Submodule.map_top,
    LinearMap.coe_range]
  rfl

/-! ### Invariant functionals and their conjugates -/

/-- Two functionals that agree on `1 ⊗ L` agree on `L.fracSpan`, since `B_dR` is torsion-free over
`A_inf`. -/
lemma apply_eq_of_mem_fracSpan (f f' : L.Functional) (h_values : basisValues f = basisValues f') :
    x ∈ L.fracSpan → f x = f' x := by
  rintro ⟨r, hr, hrx⟩
  -- `f` and `f'` agree on the span of the `1 ⊗ e_l`, which contains `r • x`.
  have h_eqOn : Set.EqOn f f'
      (Set.range (DiagTensor.mk 1 ∘ finBasis ℤ_[p] (Rep.of (overZp L.ρ)))) := by
    simpa [basisValues, funext_iff] using h_values
  have h_smul : f (r • x) = f' (r • x) := f.eqOn_span h_eqOn (ainfLattice_eq_span_basis.le hrx)
  simpa [smul_right_inj, show r ≠ 0 by simpa using hr] using h_smul

/-- An element g of Γ, embedded in ℤ × Γ, acts on A_inf through `toGp g`. -/
@[simp]
lemma inr_smul {r : Ainf} (g : Γ) : inr g • r = toGp g • r := rfl

/-- The conjugate of an A_inf-linear map μ: W(C^♭) ⊗ L → B_dR by g in Γ, namely
x ↦ (toGp g)⁻¹ · μ(g x). -/
@[simps]
noncomputable def conjForm (μ : L.Functional) (g : Γ) : L.Functional :=
  ⟨⟨fun x ↦ (toGp g)⁻¹ • μ (inr g • x), by simp⟩, by simp [smul_distrib_smul]⟩

/-- An invariant functional commutes with `Γ'` on all of `L.fracSpan`. -/
lemma form_gal_smul (hμ : μ ∈ L.forms) (hx : x ∈ L.fracSpan) : μ (g • x) = g • μ x := by
  obtain ⟨_, γ, rfl⟩ := g
  -- `conjForm μ γ` and `μ` agree on `1 ⊗ L` by invariance, hence on `L.fracSpan`.
  have h_values : basisValues (conjForm μ γ) = basisValues μ := by
    funext l
    simp [basisValues, hμ _]
  have h_conj : conjForm μ γ x = μ x := apply_eq_of_mem_fracSpan _ _ h_values hx
  exact inv_smul_eq_iff.1 h_conj

/-- The A_inf-span of the `1 ⊗ y`, y in L, is stable under ℤ × Γ. -/
lemma smul_mem_ainfLattice : x ∈ L.ainfLattice → m • x ∈ L.ainfLattice := fun hx ↦
  mapsTo_span (f := semilinearAct m) (by simp) hx

/-- `L.fracSpan` is stable under ℤ × Γ: if r x lies in the lattice, so does (m r)(m x). -/
lemma smul_mem_fracSpan : x ∈ L.fracSpan → m • x ∈ L.fracSpan := by
  rintro ⟨r, hr, hrx⟩
  refine ⟨m • r, ?_, ?_⟩
  · -- `m` acts on A_inf by a ring automorphism, so it keeps non-zero divisors.
    simpa [smul_eq_zero_iff_eq] using hr
  · -- `(m • r) • (m • x) = m • (r • x)`, and `r • x` lies in the lattice.
    rw [← frobGroup_smul_smul]
    exact smul_mem_ainfLattice m hrx

/-- `valueAt a μ`, which is μ ∘ φ^{-a}, turns the action of the n-th power of the unit φ^b E into
multiplication by the n-th power (n ∈ ℤ) of its image `phiInvToBdR a (frobE b)` in B_dR under
φ^{-a}. -/
lemma valueAt_frobEUnit_zpow_smul :
    ∀ x : L.Ambient,
      valueAt a μ (k.frobEUnit b ^ n • x) = phiInvToBdR a (k.frobE b) ^ n * valueAt a μ x := by
  -- Replace `x` by `frobEUnit b ^ (-n).toNat • x`, so that only natural powers of `frobEUnit b`
  -- remain.
  refine (MulAction.surjective (k.frobEUnit b ^ (-n).toNat)).forall.2 ?_
  cases n with
  | ofNat n => simp [frobEUnit_pow_smul]
  | negSucc n =>
    -- `↓`: `smul_smul` must join the unit and its inverse before `frobEUnit_pow_smul` applies.
    simp [↓smul_smul, frobEUnit_pow_smul]

lemma mk_one_mem_ainfLattice (t : Rep.of (overZp L.ρ)) : no_index (.mk 1 t) ∈ L.ainfLattice :=
  subset_span ⟨t, rfl⟩

/-- The projection of `1 ⊗ t` to a letter stays in the A_inf-span of the `1 ⊗ y`. -/
lemma letterProj_mk_mem_ainfLattice (t : Rep.of (overZp L.ρ)) :
    L.letterProj i (DiagTensor.mk 1 t) ∈ L.ainfLattice := by
  simp (maxDischargeDepth := 4) [letterProj, sum_mem, smul_of_tower_mem, mk_one_mem_ainfLattice]

/-- An invariant functional composed with the projector to a letter is again invariant. -/
lemma comp_letterProj_mem_forms (h : μ ∈ L.forms) : μ ∘ₗ L.letterProj i ∈ L.forms := by
  intro t g
  -- `μ` commutes with `g` on `fracSpan`, and `g` commutes with `letterProj i`
  let γ : k.galMonoid := ⟨inr g.val, g, rfl⟩
  have h_mk : γ.val • (DiagTensor.mk 1 t : L.Ambient) = DiagTensor.mk 1 (L.ρ g t) := by
    simp [γ]
  change μ (L.letterProj i (DiagTensor.mk 1 (L.ρ g t))) =
    γ • μ (L.letterProj i (DiagTensor.mk 1 t))
  rw [← h_mk, ← gal_smul_letterProj γ]
  exact form_gal_smul γ h (mem_saturateBy_of_mem (letterProj_mk_mem_ainfLattice t))

lemma valueAt_comp_wittMap {μ : L'.Ambient →ₗ[Ainf] BdR} :
    valueAt a (μ ∘ₗ F.wittMap) x = valueAt a μ (F.wittMap x) := by simp [valueAt]

/-! ### The letters decompose the module -/

/-- The projectors to the letters sum to the identity of W(C^♭) ⊗ L. -/
lemma sum_letterProj (x : L.Ambient) : ∑ i : Letter, L.letterProj i x = x := by
  -- Orthogonality of characters of the cyclic group `k.Letter`, of order `q` say: for `0 < n < q`
  -- the character `i ↦ letterTeich i⁻¹ ^ n` is not trivial, so its values sum to zero.
  have h_orth (n : ℕ) (hn : n ∈ Finset.range (Fintype.card k.Letter)) (hn₀ : n ≠ 0) :
      ∑ i, k.letterTeich i⁻¹ ^ n = 0 := by
    refine sum_hom_units_eq_zero (k.letterTeich.comp invMonoidHom ^ n) fun h_triv ↦ ?_
    have hn_lt : n < Nat.card k.Letter := by simpa using hn
    obtain ⟨i, hi⟩ : ∃ i : k.Letter, i ^ n ≠ 1 := exists_pow_ne_one_of_isCyclic hn₀ hn_lt
    -- The zeroth Witt component of `letterTeich i ^ n = 1` gives `i ^ n = 1`.
    have h_coeff : Units.val (i ^ n : (flatFq k.f)ˣ) = ((1 : (flatFq k.f)ˣ) : flatFq k.f) := by
      -- Elaborator: `using!`; the Teichmüller coefficient is matched only after unfolding.
      simpa [letterTeich, algebraMap_toAlgebra, ← map_pow] using!
        congrArg (fun s : k.S ↦ s.val.coeff 0) (DFunLike.congr_fun h_triv i⁻¹)
    exact hi (Units.ext h_coeff)
  suffices ∑ i : k.Letter, ∑ n ∈ Finset.range (Fintype.card k.Letter),
      k.letterTeich i⁻¹ ^ n • (L.mulZeta.wittMap ^ n) x =
    Fintype.card k.Letter • x by
      simpa [letterProj, letterOp, ← smul_sum, smul_pow, invOf_smul_eq_iff, Nat.cast_smul_eq_nsmul]
  -- After exchanging the two sums only the term `n = 0` survives, and it equals `q • x`.
  rw [sum_comm, sum_eq_single 0 (fun n hn hn₀ ↦ ?_) (by simp)]
  · simp
  · -- The scalar `0` of `S` acts here through A_inf only up to unfolding.
    rw [← sum_smul, h_orth n hn hn₀]
    exact zero_smul ..

/-! ### Functionals of given type and Hodge–Tate jumps -/

/-- For a lattice with jump sets `L`, a letter `i` and `u : ℤ`, `formsOfType i u` is the set of
A_inf-linear maps W(C^♭) ⊗ L → B_dR that are Γ'-equivariant on 1 ⊗ L and send the projection of
1 ⊗ L to `i` into t^{−u}B_dR^+. `L.jumpMultiplicity i u` is the total multiplicity of the Hodge–Tate
jump `u` over the embeddings of `O` above `i`. There are `r ≤ L.jumpMultiplicity i u` forms `ν m` of
type `u` at `i` such that every form of type `u` at `i` is a `Q̄_p`-combination of the `ν m` modulo
a form in `formsOfType i (u - 1)`. -/
lemma exists_span_formsOfType_mod_pred (i : Letter) (u : ℤ) :
    ∃ r ≤ L.jumpMultiplicity i u, ∃ ν : Fin r → L.formsOfType i u, ∀ μ ∈ L.formsOfType i u,
      ∃ c : Fin r → PadicAlgCl p,
      μ - ∑ m : Fin r, c m • (ν m).val ∈ formsOfType i (u - 1) := by
  -- The symbol `f μ : L.Carrier → ℂ_p` of `μ` is its leading coefficient on the letter `i`; the
  -- symbols are Hodge–Tate maps of weight `u`, so
  -- `IsPotentiallyCrystalline.sum_jump_eq_jump_overZp` bounds their span. In a basis of symbols the
  -- coordinates are Galois invariant, hence algebraic (Ax–Sen–Tate).
  have h_type (μ : L.formsOfType i u) (t : Rep.of (overZp L.ρ)) :
      ∃ y : BdRPlus, y • (tUnit ^ (-u)).val = μ.val (L.letterProj i (.mk 1 t)) :=
    mem_span_singleton.1 (μ.property.2 t)
  -- Write `μ (letterProj i (1 ⊗ t)) = a μ t • tUnit ^ (-u)` with `a μ t` in `B_dR⁺`.
  choose a ha using h_type
  -- The leading coefficient can be computed from any expression `y • tUnit ^ (-u)`. (`hz` is an
  -- explicit argument: as a default tactic it was slow to elaborate.)
  have theta_a {μ : L.formsOfType i u} {t : Rep.of (overZp L.ρ)} {z : ℂ_[p]} {y : BdRPlus}
      (h : μ.val (L.letterProj i (.mk 1 t)) = y • (tUnit ^ (-u)).val)
      (hz : thetaBdR y = z) :
      thetaBdR (a μ t) = z := by
    rw [show a μ t = y from (smul_left_inj (Units.ne_zero _)).1 ((ha μ t).trans h), hz]
  let f (μ : L.formsOfType i u) : L.Carrier →ₛₗ[(ofId ℤ_[p] ℂ_[p] : ℤ_[p] →+* ℂ_[p])] ℂ_[p] :=
    { toFun := thetaBdR ∘ a μ
      map_add' _ _ := theta_a (by simp [add_smul, ← ha]) (map_add ..)
      map_smul' c t := theta_a (y := c • a μ t) (by simp [← ha])
        (by simp +zetaDelta [smul_def', -toRingHom_ofId]) }
  -- `g` multiplies `tUnit ^ (-u)` by the cyclotomic character to the power `-u`, and `ζ` acts on
  -- the letter `i` by `letterTeich i`.
  have f_gal (μ : L.formsOfType i u) (t : Rep.of (overZp L.ρ)) (g : k.subgroup) :
      f μ (L.ρ g t) = (χ g ^ (-u)).val • toGp g • f μ t :=
    theta_a (hz := by simp +zetaDelta [smul_def', -toRingHom_ofId]) <| by
      have h_inv : μ.val (L.letterProj i (.mk 1 (L.ρ g t))) =
          toGp g.val • μ.val (L.letterProj i (.mk 1 t)) :=
        comp_letterProj_mem_forms μ.property.1 t g
      rw [h_inv, ← ha, smul_distrib_smul, smul_tUnit_zpow, smul_comm, ← smul_assoc]
  have f_ζ (μ : L.formsOfType i u) (t : Rep.of (overZp L.ρ)) :
      f μ (O.ζ.val • t) = theta (k.letterTeich i) * f μ t :=
    theta_a (hz := by simp +zetaDelta [smul_def', -toRingHom_ofId]) <| by
      have h_mk : (DiagTensor.mk 1 (O.ζ.val • t) : L.Ambient) = L.mulZeta.wittMap (.mk 1 t) := by
        simp [mulZeta]
      rw [h_mk, ← mulZeta.wittMap_letterProj (.mk 1 t),
        mem_letterPart_iff_mulZeta.1 letterProj_mem_letterPart, smul_eq_val_smul,
        μ.val.map_smul, ← ha, ← smul_assoc]
  -- A basis `b` of the span of the symbols, made of symbols `b m = f (ν m)`.
  obtain ⟨b, hb, span_b, b_indep⟩ := exists_fun_fin_finrank_span_eq ℂ_[p] (.range f)
  choose ν hν using hb
  -- The symbols are Hodge–Tate maps of weight `u` on which `ζ` acts by `letterTeich i`, so their
  -- span has dimension at most the jump multiplicity.
  have h_rank :
      Module.finrank ℂ_[p] (Submodule.span ℂ_[p] (Set.range f)) ≤ L.jumpMultiplicity i u :=
    L.inClass.isPotentiallyCrystalline.sum_jump_eq_jump_overZp.2 O.ζ.val (theta (k.letterTeich i)) u
      (range f)
      (forall_mem_range.2 fun μ ↦ ⟨fun t ↦ nearOne_le (f_gal μ t), f_ζ μ⟩)
  refine ⟨_, h_rank, ν, ?_⟩
  -- `μ` is taken as an element of the subtype `L.formsOfType i u`, the domain of `a` and `f`.
  refine SetCoe.forall'.2 fun μ ↦ ?_
  obtain ⟨c, hc⟩ : ∃ c : _ → ℂ_[p], ∑ m, c m • b m = f μ :=
    (mem_span_range_iff_exists_fun _).1 (span_b.ge (subset_span ⟨μ, rfl⟩))
  -- `f μ` and the `b m` transform in the same way, so `toGp g • c` are coordinates of `f μ` too.
  have c_fixed (g : k.subgroup) (m : Fin _) : toGp g • c m = c m := by
    refine (b_indep.eq_coords_of_eq (g := toGp g • c) (LinearMap.ext ?_) m).symm
    refine (L.ρ.apply_bijective g).2.forall.2 ?_
    simpa [← hc, ← hν, f_gal, smul_sum, -toRingHom_ofId] using (f_gal μ · g)
  choose c' hc' c_eq using fun m ↦ exists_mem_localFieldOf_of_forall_smul_eq k.subgroup fun g ↦
    c_fixed g m
  refine ⟨c', fun t g ↦ ?_, fun t ↦ ?_⟩
  · -- The difference is invariant, since `Γ'` fixes the coefficients.
    have c'_fixed (m) : toGp g.val • algebraMap _ BdR (c' m) = algebraMap _ BdR (c' m) :=
      (BdR.smul_algebraMap_padicAlgCl _ _).trans (congrArg _ (mem_localFieldOf.1 (hc' m) g))
    simp only [LinearMap.sub_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      μ.property.1 t, (ν _).property.1 t, smul_sub, smul_sum, smul_def', smul_mul', c'_fixed]
  · -- The leading coefficient of the difference vanishes, so its pole has order at most `u - 1`.
    have lead : thetaBdR (a μ t - ∑ m, c' m • a (ν m) t) = 0 := by
      simpa [← hν, c_eq, smul_def', sub_eq_zero, -toRingHom_ofId] using!
        LinearMap.congr_fun hc.symm t
    simpa [← ha, ↓← smul_def', sub_smul, sum_smul] using!
      mul_mem_hodgeFil (n := -u) (algebraMap_mem_hodgeFil_one_iff.2 lead) (subset_span rfl)

/-- If n is not in `L.jumpSet i`, every functional of type n at the letter i is of type n - 1. -/
lemma formsOfType_subset_pred_of_notMem (h : n ∉ L.jumpSet i) :
    L.formsOfType i n ⊆ L.formsOfType i (n - 1) := by
  obtain ⟨r, hr, ν, span_ν⟩ := L.exists_span_formsOfType_mod_pred i n
  -- `n` is no jump at any embedding over the letter `i`, so the family `ν` is empty.
  have no_jump : L.jumpMultiplicity i n = 0 := by
    refine sum_eq_zero fun γ hγ ↦ ?_
    by_contra h_jump
    have h_over : γ O.ζ = (theta (letterTeich i) : ℂ_[p]) := by simpa using hγ
    exact h (L.embJumps_subset h_over (L.inClass.mem_of_jump_ne_zero h_jump))
  obtain rfl : r = 0 := Nat.le_zero.1 (hr.trans_eq no_jump)
  intro μ hμ
  simpa using span_ν μ hμ

end New.Lift.KummerChart.JumpLattice

end
end
end

/-!
# The frame theorem for Kisin modules and stability under normalising Galois elements

Let `L` be a lattice datum over a Kummer chart `k`. The ring `S` of `k` has a variable `z` and the
element `E = z ^ e * unit + p`, and `k.frobE m` is `φ ^ m E`; `phiInvToBdR 0` is the map
`Ainf → BdR`. Let `h = L.jumpBound` and `τ = [ε^{1/p}] − 1`. A form is an `Ainf`-linear map
`W(C♭) ⊗ L → B_dR`. Those in `L.forms` are `Γ'`-equivariant on `1 ⊗ L`. They cut out the
`Ainf`-module `L.kisinAinf` and the Kisin module `N = L.kisinModule` over `S`. `L.ainfLattice` is
`Ainf ⊗ L`; `L.fracSpan` holds the `x` with `r • x ∈ L.ainfLattice` for some non-zero divisor `r` of
`Ainf`, and `L.frobKisinAinf l` is `φ ^ l (L.kisinAinf)`.

## Overview of this theory

A chart (`New.Lift.Chart`) is a `Λ`-algebra map `Λ⟦X⟧ → A_inf`, with `Λ = W(𝔽_{p^f})`. It sends `X`
to a non-unit Teichmüller lift `z = [ϖ^♭]`. It sends some `X^e V + p`, with `V` a unit, to a
generator `E` of `ker θ`. `S` is its image. `B⁺` (`New.Period.BPlus`) receives `A_inf` and maps to
`B_max` (`New.Period.Bmax`) and `B_dR`. Its `S`-subalgebra `S_B` (`New.Lift.Chart.bicommutant`)
consists of the elements whose multiplication commutes with every `S`-linear endomorphism of `B⁺`
that keeps the image of `A_max`. Put `μ = [ε] - 1`, with `ε` a compatible system of `p`-power roots
of unity, and `τ = φ⁻¹ μ`.

* Let `K` be the field fixed by an open subgroup `G_K` of `Gal(ℚ̄_p/ℚ_p)`. There is a Kummer chart
  (`New.Lift.KummerChart`) with `Λ` and `θ z` fixed by `G_K` and `e f = [K : ℚ_p]`
  (`New.Lift.exists_kummerChart`).
* Let `c` be a chart for `G_K` (`IsChartOf`). Let `T` be a crystalline `ℤ_p`-lattice with action
  `ρ`, whose jumps (the `k` with `New.Period.jump` nonzero) lie in `[-a, b]`. In a basis of `T`
  there are three objects. The first is `P`, invertible over `B_max`, with `ρ(g) · g P = P`. The
  second is a unit `v` with `E τ v = μ`. The third is `U` over `B⁺`, whose image in `B_max` is
  `(E τ)^a P`. This `U` satisfies the predicate `IsPeriodMatrix` with height `a + b` and Frobenius
  factor `v^a` (`New.Lift.Chart.IsChartOf.exists_isPeriodMatrixOf`).
* Take such a `U` of height `h` and factor `v`. There are `Q` and `Q'` over `A_inf`, `Z` over `S_B`
  and `B` over `S` with `Q Q' = τ^h`, `U Z = E^h Q` and `φ Q = v Q B`
  (`New.Lift.Chart.IsPeriodMatrix.exists_frame`).
* On a Kummer chart, let `h = jumpBound`. Let `N` be the `S`-module `kisinModule` and `M` its
  `A_inf`-span `kisinAinf`. Then `τ^h` maps `M` into `ainfLattice` and back, and `E^h φ N ⊆ N`. Take
  a crystalline form `λ` (`crysForms`, valued in `B_dR`). Then `E^h λ(N)` lies in the image of
  `S_B`. Suppose `d ∈ A_inf` is such that `d ∣ E^m r` in `B⁺` forces `d ∣ r`. Then `x ∈ M` lies in
  `d M` once, for one `n`, `E^n λ(x) ∈ d B⁺` for all such `λ`
  (`New.Lift.KummerChart.JumpLattice.mem_smul_kisinAinf_of_crysForms`).

This is a substitute, in the form needed here, for part of Kisin's theorem on the module of a
crystalline lattice (Kisin 2006; Bhatt–Morrow–Scholze 2018). The inclusion `E^n N ⊆ S φ N` and an
equivalence of categories are not stated.

Contents of the files. `Charts`: coordinates and an approximation lemma.
`Bicommutant`: extension to `B⁺`.
`PeriodMatrixBasis`: `U`, and `Q` with `det Q ≠ 0`. `PeriodMatrixFrame`: `p ∤ det Q`, hence the
frame. `KummerChartDeRham`: the different, and values in `B_dR`. `Modules`: `M`, `N` and the
`B_dR`-valued forms. `FrameTheorem`: `N` as the `S`-span of the columns of `τ^{-h} Q`, using
`Lib.PadicHodge.RadiusLemma`.

## Main definitions and results

* `New.Lift.KummerChart.JumpLattice.frame_theorem`: a relation `∑ c i • v i = 0` among vectors of
  `L.valueFieldPoints L.fracSpan` still holds after applying any `k.S`-linear `f : Ainf → k.S` to
  the coefficients (`New.Lift.KummerChart.JumpLattice.FrameProperties`).
* `New.Lift.KummerChart.JumpLattice.smul_mem_kisinAinf`: an element `g` that conjugates `Γ'` into
  itself preserves the module `New.Lift.KummerChart.JumpLattice.kisinAinf`. The reason is that
  conjugation by `g` keeps forms `Γ'`-equivariant
  (`New.Lift.KummerChart.JumpLattice.conjForm_mem_forms`).

Notions from other files:
* `New.Lift.KummerChart.JumpLattice`: A finite free O-module with an action of Γ, crystalline over
  Γ', together with a finite set of integers for each embedding of O in `ℂ_[p]` that contains the
  jumps at that embedding. It also carries finite sets of integers indexed by `Letter`, which this
  file does not use directly.
* `New.Lift.KummerChart.JumpLattice.Ambient`: The module W(C^♭)⊗L for the lattice underlying L;
  `DiagTensor.mk 1 t` is the vector 1 ⊗ t.
* `New.Lift.KummerChart.JumpLattice.kisinAinf`: The x in A_inf[1/τ] ⊗ L with μ(φ^n x) in B_dR^+ for
  all n ≥ 1 and all μ in `L.forms`, where τ = [ε^{1/p}] − 1. The Kisin module consists of those x on
  which all forms in `L.forms` take values in the subfield `k.valueField 0` of B_dR.

## Relation to the literature

Known; see `Lib.PadicHodge.Kisin.PeriodMatrixFrame` and `Lib.PadicHodge.Kisin.Modules` for sources.
-/

@[expose] public section

/-! ## The frame theorem: spanning and bounded height -/

section FrameTheorem

namespace New.Lift.KummerChart.JumpLattice

open Period Pointwise Submodule Set FrobGroup Module FaithfulSMul Matrix Algebra MulSemiringAction
  Finset LinearMap TensorProduct algebraMap
open Chart hiding φ

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
  {k : KummerChart Γ} {O : Coeffs} {L : JumpLattice O}

/-- Every `ℤ_[p]`-linear map `f` from the lattice `L` to `BdR` is the restriction of some
form `μ` to the vectors `1 ⊗ t`. -/
lemma exists_functional_extend (f : Rep.of (overZp L.ρ) →ₗ[ℤ_[p]] BdR) :
    ∃ μ : L.Functional, ∀ t : Rep.of (overZp L.ρ), μ (DiagTensor.mk 1 t) = f t := by
  -- Over the field `BdR`, some linear map `Ψ` on `BdR ⊗ WittCFlat` with values in
  -- `L.Carrier →ₗ BdR` sends the non-zero vector `1` to `f`. Its restriction to `WittCFlat` is
  -- `Ainf`-linear and defines `μ`.
  have h_nontrivial : Nontrivial (BdR ⊗[Ainf] WittCFlat) :=
    nontrivial_of_algebraMap_injective_of_isDomain Ainf BdR WittCFlat
      (algebraMap_injective Ainf BdR) (algebraMap_injective Ainf WittCFlat)
  obtain ⟨Ψ, -, hΨ⟩ :=
    exists_extend_of_notMem (K := BdR) (p := ⊥) (v := (1 : BdR ⊗[Ainf] WittCFlat)) 0 one_ne_zero f
  exact ⟨AlgebraTensorModule.lift ((liftBaseChangeEquiv BdR).symm Ψ), DFunLike.congr_fun hΨ⟩

/-- Let `μ` and `μ'` be forms, `g ∈ Γ`, and let `A` be an invertible matrix over `BdR` with
`ρ(g) * g(A) = A`, where `ρ(g)` is the matrix of `g` in the basis `finBasis ℤ_[p] L.Carrier`. Then
`μ'(1 ⊗ g t) = g • μ(1 ⊗ t)` for all `t` if and only if
`basisValues μ' ᵥ* A = g • (basisValues μ ᵥ* A)`; here `basisValues` is the vector of values
of a form on the basis vectors `1 ⊗ e i`. -/
lemma equivariant_iff_basisValues {μ : L.Functional} {g : GroupOverGp.G}
    {A : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) BdR}
    {μ' : L.Functional} (hA : IsUnit A)
    (h_cocycle : (repMatrix L.ρ (finBasis ℤ_[p] L.Carrier) g).map (algebraMap ℤ_[p] BdR) *
      A.map (fun x : BdR ↦ toGp g • x) = A) :
    (∀ t : L.Carrier, μ' (DiagTensor.mk 1 (L.ρ g t)) = toGp g • μ (DiagTensor.mk 1 t)) ↔
      basisValues μ' ᵥ* A = toGp g • basisValues μ ᵥ* A := by
  set P := (repMatrix L.ρ (finBasis ℤ_[p] L.Carrier) g).map (algebraMap ℤ_[p] BdR)
  set gA := A.map (fun x : BdR ↦ toGp g • x)
  -- Both sides of the matrix equation are products with the invertible matrix `gA = g • A`:
  -- the left one by `h_cocycle : P * gA = A`, the right one since `g` acts by a ring map.
  have h_left : basisValues μ' ᵥ* A = basisValues μ' ᵥ* P ᵥ* gA := by rw [vecMul_vecMul, h_cocycle]
  have h_right : toGp g • basisValues μ ᵥ* A = (toGp g • basisValues μ) ᵥ* gA :=
    funext ((toRingHom (Gp p) BdR (toGp g)).map_vecMul A (basisValues μ))
  have h_unit : IsUnit gA := hA.map (toRingHom (Gp p) BdR (toGp g)).mapMatrix
  have h_entry (l : Fin (finrank ℤ_[p] L.Carrier)) :
      (basisValues μ' ᵥ* P) l = μ' (.mk 1 (L.ρ g (finBasis ℤ_[p] L.Carrier l))) := by
    simp [P, repMatrix, toMatrixAlgEquiv_apply, ← smul_def', ← commutes, ← map_smul_of_tower,
      ← map_sum, -LinearMap.map_smulₛₗ, -map_smul, vecMul, dotProduct, basisValues]
  rw [h_left, h_right, (vecMul_injective_of_isUnit h_unit).eq_iff]
  simp only [funext_iff, h_entry]
  refine ⟨fun h l ↦ h (finBasis ℤ_[p] L.Carrier l), fun h t ↦ ?_⟩
  -- The forms `conjForm μ' g` and `μ` agree on a basis, so they agree on `L.fracSpan`.
  have h_row : basisValues (conjForm μ' g) = basisValues μ := funext fun l ↦ by
    simp [h, basisValues]
  simpa [inv_smul_eq_iff] using
    apply_eq_of_mem_fracSpan (conjForm μ' g) μ h_row
      (mem_saturateBy_of_mem (mk_one_mem_ainfLattice t))

/-- The module `L.kisinAinf` lies in `L.fracSpan`: a power of `τ` is a non-zero divisor of
`Ainf`. -/
lemma kisinAinf_le_fracSpan : L.kisinAinf ≤ L.fracSpan := by
  rintro x ⟨⟨_, ⟨N, rfl⟩, hτx⟩, -⟩
  exact ⟨tau ^ N, by simp, hτx⟩

/-- The module `W(C♭) ⊗ L` has no `Ainf`-torsion. -/
instance : IsTorsionFree Ainf L.Ambient := .trans_faithfulSMul _ WittCFlat (_ ⊗ _)

/-! ### A frame of the lattice

The proof of `frame_theorem` reads everything off a frame of `L` (`Frame`): the period matrix
`(E * τ) ^ a • M` of `L`, with `a = L.jumpBound`, and the frame `Q`, `Q'`, `Z`, `Y`, `B` that
`New.Lift.Chart.IsPeriodMatrix.exists_frame` gives for it. -/

/-- The vector `∑ i, t i • (1 ⊗ e i)` of `L.ainfLattice` with coordinates `t` in the basis
`e = finBasis ℤ_[p] L.Carrier`. -/
private noncomputable def latticeVec (L : JumpLattice O) :
    (Fin (finrank ℤ_[p] L.Carrier) → Ainf) →ₗ[Ainf] L.Ambient :=
  Fintype.linearCombination Ainf (DiagTensor.mk 1 ∘ finBasis ℤ_[p] L.Carrier)

private lemma ainfLattice_eq_range_latticeVec : L.ainfLattice = (latticeVec L).range := by
  simp [ainfLattice_eq_span_basis, latticeVec]

/-- The ring map `Bmax → BdR` that applies `φ ^ m` and then maps to `BdR`. -/
private noncomputable def frobPowToBdR (m : ℕ) : Bmax →+* BdR :=
  (algebraMap Bmax BdR).comp (toRingHom FrobGal Bmax (.ofAdd m, 1))

/-- A frame of the lattice `L`, with `a = L.jumpBound`: a period matrix `U` made from an invertible
matrix `M` (`New.Lift.Chart.IsPeriodMatrixOf`), the matrices `Q`, `Q'`, `Z`, `Y`, `B` of
`New.Lift.Chart.IsPeriodMatrix.exists_frame`, and vectors `n i` such that `τ ^ a • n i` is the
vector of `L.ainfLattice` with coordinates the column `i` of `Q`. -/
private structure Frame (L : JumpLattice O) where
  /-- An invertible matrix over `Bmax` with invariant columns. -/
  M : GL (Fin (finrank ℤ_[p] L.Carrier)) Bmax
  /-- The period matrix, over `BPlus`. -/
  U : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) BPlus
  /-- The unit `μ / (E * τ)` of `Ainf`. -/
  v : Ainfˣ
  /-- The period matrix is made from `M` by the factor `(E * τ) ^ a`, with unit `v`. -/
  isPeriodMatrixOf : k.chart.IsPeriodMatrixOf ((overZp L.ρ).comp k.subgroup.subtype) L.jumpBound
    L.jumpBound (finBasis ℤ_[p] L.Carrier) M.val U v
  /-- The frame matrix over `Ainf` whose columns give the basis. -/
  Q : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) Ainf
  /-- An inverse of `Q` up to `τ ^ (a + a)`. -/
  Q' : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) Ainf
  /-- The matrix over `BPlus` with entries in `k.bicommutant` that carries `U` to
  `E ^ (a + a) • Q`. -/
  Z : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) BPlus
  /-- An inverse of `Z` up to `E ^ (a + a)`. -/
  Y : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) BPlus
  /-- The matrix over `S` through which the Frobenius acts on `Q`. -/
  B : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) k.S
  /-- `Q * Q' = τ ^ (a + a)`. -/
  Q_mul_Q' : Q * Q' = tau ^ (L.jumpBound + L.jumpBound) • 1
  /-- The entries of `Z` lie in `k.bicommutant`. -/
  Z_mem : ∀ i j : Fin (finrank ℤ_[p] L.Carrier), Z i j ∈ k.bicommutant
  /-- `U * Z = E ^ (a + a) • Q`. -/
  U_mul_Z : U * Z = k.E.val ^ (L.jumpBound + L.jumpBound) • Q.map ainfToBPlus
  /-- `Y * Z = E ^ (a + a)`. -/
  Y_mul_Z : Y * Z = k.E.val ^ (L.jumpBound + L.jumpBound) • 1
  /-- The Frobenius acts on `Q` by `φ Q = v ^ a • (Q * B)`. -/
  map_frobEnd_Q : Q.map frobEnd = v ^ L.jumpBound • (Q * B.map (↑))
  /-- The elements of `FixesThetaZ` act on `Z` through matrices over `Ainf`. -/
  exists_smul_Z : ∀ g : Gp p, k.FixesThetaZ g →
    ∃ G : Matrix (Fin (finrank ℤ_[p] L.Carrier)) (Fin (finrank ℤ_[p] L.Carrier)) Ainf,
      g • Z = Z * G.map ainfToBPlus
  /-- The vectors `τ ^ (-a) • Qᵀ i`. -/
  n : Fin (finrank ℤ_[p] L.Carrier) → L.Ambient
  /-- `τ ^ a • n i` has the coordinates of the column `i` of `Q`. -/
  tau_pow_smul_n (i : Fin (finrank ℤ_[p] L.Carrier)) : tau ^ L.jumpBound • n i = latticeVec L (Qᵀ i)

/-- Every lattice has a frame. -/
private lemma nonempty_frame : Nonempty (Frame L) := by
  -- The period matrix comes from the crystalline basis, the frame from
  -- `New.Lift.Chart.IsPeriodMatrix.exists_frame`, and `n i` from the fact that `τ ^ a` acts
  -- bijectively on `W(C♭) ⊗ L`, as `p` does not divide `τ`.
  obtain ⟨h_adm, -, -⟩ := L.inClass
  obtain ⟨M, U, v, hM⟩ := isChartOf.exists_isPeriodMatrixOf L.jumpBound L.jumpBound
    (ρ := (overZp L.ρ).comp k.subgroup.subtype) (h_adm.mono le_sup_right :)
      (finBasis ℤ_[p] L.Carrier)
    (Nat.sInf_mem (s := {a : ℕ | ∀ u : ℤ, jump ((overZp L.ρ).comp k.subgroup.subtype)
      (ofId ℤ_[p] ℂ_[p]) u ≠ 0 → -a ≤ u ∧ u ≤ a}) exists_jump_bound)
  obtain ⟨Q, Q', Z, Y, B, hQQ', hZ, hUZ, hYZ, hφQ, hZ_gal⟩ := hM.isPeriodMatrix.exists_frame
  have h_surj (x : L.Ambient) : ∃ y : L.Ambient, tau ^ L.jumpBound • y = x := by
    simpa [← map_pow] using
      ((isUnit_algebraMap_wittCFlat_of_not_p_dvd not_p_dvd_tau).pow
        L.jumpBound).smul_bijective.surjective x
  choose n hn using fun i : Fin (finrank ℤ_[p] L.Carrier) ↦ h_surj (latticeVec L (Qᵀ i))
  exact ⟨⟨M, U, v, hM, Q, Q', Z, Y, B, hQQ', hZ, hUZ, hYZ, hφQ, hZ_gal, n, hn⟩⟩

namespace Frame

/-- The combination `F.comb m t = ∑ i, t i • φ ^ m • F.n i`. -/
private noncomputable def comb (F : Frame L) (m : ℕ) :
    (Fin (finrank ℤ_[p] L.Carrier) → Ainf) →ₗ[Ainf] L.Ambient :=
  Fintype.linearCombination Ainf ((fun x : L.Ambient ↦ φ • x)^[m] ∘ F.n)

/-- `(φ ^ m τ ^ a) • F.comb m t`, with `a = L.jumpBound`, is the vector of `L.ainfLattice` with
coordinates `φ ^ m Q * t`. -/
private lemma smul_comb_eq_latticeVec (F : Frame L) (m : ℕ)
    (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf) :
    (φ ^ m • tau ^ L.jumpBound) • F.comb m t =
      latticeVec L (F.Q.map (fun r : Ainf ↦ φ ^ m • r) *ᵥ t) := by
  -- `φ ^ m` fixes the vectors `1 ⊗ e j`, so it acts on `latticeVec L v` through the coordinates.
  have h_phi_col (j : Fin (finrank ℤ_[p] L.Carrier)) : φ ^ m • latticeVec L (F.Qᵀ j) =
      latticeVec L ((F.Q.map fun r : Ainf ↦ φ ^ m • r)ᵀ j) := by
    simp [latticeVec, smul_sum, Fintype.linearCombination_apply, frobGroup_smul_smul,
      MonoidHom.map_one]
  simp [comb, smul_sum, smul_comm _ (t _), ← frobGroup_smul_smul, F.tau_pow_smul_n, ↓mulVec_eq_sum,
    -smul_pow', h_phi_col, Fintype.linearCombination_apply]

/-- `τ ^ a • ∑ i, t i • F.n i`, with `a = L.jumpBound`, is the vector of `L.ainfLattice` with
coordinates `Q * t`. -/
private lemma tau_pow_smul_sum_eq_latticeVec (F : Frame L)
    (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf) :
    tau ^ L.jumpBound • ∑ i : Fin (finrank ℤ_[p] L.Carrier), t i • F.n i =
      latticeVec L (F.Q *ᵥ t) := by
  simpa [comb, Fintype.linearCombination_apply] using F.smul_comb_eq_latticeVec 0 t

/-- A form `μ` lies in `L.forms` if and only if, for any `m`, its coordinates
`basisValues μ ᵥ* φ ^ m M` in the frame are fixed by every `g ∈ Γ'`. The reason is that the
columns of `M` are invariant. -/
private lemma mem_forms_iff (F : Frame L) (m : ℕ) {μ : L.Functional} :
    μ ∈ L.forms ↔ ∀ (g : k.subgroup) (ν : Fin (finrank ℤ_[p] L.Carrier)),
      (basisValues μ ᵥ* (frobPowToBdR m).mapMatrix F.M) ν =
        (toGp g.val • basisValues μ ᵥ* (frobPowToBdR m).mapMatrix F.M) ν := by
  refine forall_comm.trans (forall_congr' fun g ↦ ?_)
  refine (equivariant_iff_basisValues (F.M.isUnit.map (frobPowToBdR m).mapMatrix) ?_).trans
    funext_iff
  -- The invariance of the columns of `M`, mapped by `frobPowToBdR m`, which commutes with `g`.
  have h_cols : (repMatrix L.ρ (finBasis ℤ_[p] L.Carrier) g.val).map (algebraMap ℤ_[p] Bmax) *
      F.M.val.map (fun x : Bmax ↦ toGp g.val • x) = F.M.val :=
    F.isPeriodMatrixOf.hasInvariantColumns g
  have h_mapped := congrArg (frobPowToBdR m).mapMatrix h_cols
  -- `using!`: the two actions of `g` on `BdR` agree only by unfolding their definitions.
  simpa [frobPowToBdR, smul_smul, ↓map_mul, @MulAction.compHom_smul_def _ _ Bmax, Function.comp_def,
    ← IsScalarTower.algebraMap_apply] using! h_mapped

/-- For a form `μ ∈ L.forms`, each coordinate `(basisValues μ ᵥ* φ ^ m M) ν` lies in `hodgeFil 0`
and in the field `valueField 0`, being fixed by `Γ'`. -/
private lemma coord_mem_hodgeFil_zero_and_mem_valueField (F : Frame L) (m : ℕ) {μ : L.Functional}
    (hμ : μ ∈ L.forms) (ν : Fin (finrank ℤ_[p] L.Carrier)) :
    (basisValues μ ᵥ* (frobPowToBdR m).mapMatrix F.M) ν ∈ hodgeFil 0 ∧
      (basisValues μ ᵥ* (frobPowToBdR m).mapMatrix F.M) ν ∈ valueField 0 :=
  mem_hodgeFil_zero_and_mem_valueField_zero_of_fixed fun g ↦ (F.mem_forms_iff m).mp hμ g ν

/-- The values of a form on `F.comb m t` in terms of the frame: with `a = L.jumpBound`,
`φ ^ m E ^ a • μ (F.comb m t)` is the product of the coordinates `basisValues μ ᵥ* φ ^ m M` with
`φ ^ m Z * t`. -/
private lemma frobE_pow_smul_apply_comb (F : Frame L) (μ : L.Functional) (m : ℕ)
    (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf) :
    (k.frobE m).val ^ L.jumpBound • μ (F.comb m t) =
      basisValues μ ᵥ* (frobPowToBdR m).mapMatrix F.M ⬝ᵥ
        (↑) ∘ (F.Z.map frobEnd^[m] *ᵥ ainfToBPlus ∘ t) := by
  -- Compare `smul_comb_eq_latticeVec` with `(E * τ) ^ a • M * Z = U * Z = E ^ (a + a) • Q`, and
  -- cancel the unit `φ ^ m ((E * τ) ^ a)`.
  set a : ℕ := L.jumpBound with ha
  have h_cmp : (k.frobE m).val ^ (a + a) • μ ((φ ^ m • tau ^ a) • F.comb m t) -
        basisValues μ ⬝ᵥ (frobPowToBdR m).mapMatrix ((F.U * F.Z).map (↑)) *ᵥ t • 1 =
      (k.frobE m).val ^ (a + a) • μ (latticeVec L (F.Q.map (fun r : Ainf ↦ φ ^ m • r) *ᵥ t)) -
        basisValues μ ⬝ᵥ (frobPowToBdR m).mapMatrix
          ((k.E.val ^ (a + a) • F.Q.map ainfToBPlus).map (↑)) *ᵥ t • 1 := by
    rw [F.smul_comb_eq_latticeVec, F.U_mul_Z]
  rw [Matrix.map_mul, F.isPeriodMatrixOf.map_eq_smul, ← ha, map_mul, ← mulVec_mulVec,
    dotProduct_mulVec] at h_cmp
  apply (((isUnit_smul_of_dvd_mu 1 ⟨_, F.isPeriodMatrixOf.E_mul_tau_mul.symm⟩).pow a).map
    (frobPowToBdR m)).mul_left_cancel
  -- The normalisation unfolds the maps and the coordinates; `ring_nf` then closes the goal.
  linear_combination (norm := (
    simp [latticeVec, frobPowToBdR, smul_def', ↓map_apply, val_frobE, phi_pow_smul, mul_sum,
      ↓RingHom.mapMatrix_apply, FrobGal.smul_def, sum_mul, mul_comm (μ _),
      ← IsScalarTower.algebraMap_apply, Fintype.linearCombination_apply, mulVec, dotProduct,
      basisValues, vecMul, sub_eq_zero]
    ring_nf)) h_cmp

/-- The case `t = Pi.single i 1` of `frobE_pow_smul_apply_comb`: the value of a form on
`φ ^ m • F.n i`. -/
private lemma frobE_pow_mul_apply_smul_n (F : Frame L) (μ : L.Functional) (m : ℕ)
    (i : Fin (finrank ℤ_[p] L.Carrier)) :
    algebraMap Ainf BdR (k.frobE m).val ^ L.jumpBound * μ (φ ^ m • F.n i) =
      ∑ ν : Fin (finrank ℤ_[p] L.Carrier), (basisValues μ ᵥ* (frobPowToBdR m).mapMatrix F.M) ν *
        algebraMap BPlus BdR (frobEnd^[m] (F.Z ν i)) := by
  simpa [comb, smul_def', dotProduct, Pi.single_apply, mulVec] using
    F.frobE_pow_smul_apply_comb μ m (Pi.single i 1)

/-- The frame vectors `F.n i` lie in `L.kisinAinf`. -/
private lemma n_mem_kisinAinf (F : Frame L) (i : Fin (finrank ℤ_[p] L.Carrier)) :
    F.n i ∈ L.kisinAinf := by
  have h_lat : tau ^ L.jumpBound • F.n i ∈ L.ainfLattice := by
    simp [F.tau_pow_smul_n, ainfLattice_eq_range_latticeVec]
  refine ⟨⟨tau ^ L.jumpBound, ⟨L.jumpBound, rfl⟩, h_lat⟩, fun m μ hμ ↦ ?_⟩
  -- The factor `frobE (m + 1) ^ a` is prime to `E`, so it does not affect the filtration.
  refine (mul_mem_hodgeFil_iff_of_not_frobE_dvd (not_frobE_dvd_frobE_of_ne m.succ_pos.ne)
    L.jumpBound).1 ?_
  have h_sum : ∑ ν, (basisValues μ ᵥ* (frobPowToBdR (m + 1)).mapMatrix F.M) ν *
      algebraMap BPlus BdR (frobEnd^[m + 1] (F.Z ν i)) ∈ hodgeFil (0 + 0) :=
    sum_mem fun ν _ ↦ mul_mem_hodgeFil
      (F.coord_mem_hodgeFil_zero_and_mem_valueField (m + 1) hμ ν).left algebraMap_mem_hodgeFil_zero
  simpa [F.frobE_pow_mul_apply_smul_n, phiInvToBdR] using h_sum

/-- Each vector `φ ^ l • F.n i` lies in `L.valueFieldPoints (L.frobKisinAinf l)`: all forms in
`L.forms` take values in the field `valueField 0` on it. -/
private lemma phi_pow_smul_n_mem_valueFieldPoints (F : Frame L) (l : ℕ)
    (i : Fin (finrank ℤ_[p] L.Carrier)) :
    φ ^ l • F.n i ∈ L.valueFieldPoints (L.frobKisinAinf l) := by
  refine ⟨by simp [frobKisinAinf, F.n_mem_kisinAinf], fun μ hμ ↦ ?_⟩
  -- All terms of `frobE_pow_mul_apply_smul_n` lie in the field `valueField 0`.
  have h_frob : MapsTo frobEnd (k.bicommutant : Set BPlus) k.bicommutant :=
    fun y hy ↦ k.frobEnd_mem_bicommutant hy
  have hZ_mem (ν : Fin (finrank ℤ_[p] L.Carrier)) :
      algebraMap BPlus BdR (frobEnd^[l] (F.Z ν i)) ∈ valueField 0 := by
    have h_iter : frobEnd^[l] (F.Z ν i) ∈ k.bicommutant := h_frob.iterate l (F.Z_mem ν i)
    -- `valueField 0` contains the image of `k.bicommutant`: its generators include `b * 1`.
    exact Subfield.subset_closure (.inr ⟨(⟨_, h_iter⟩, 1), by simp [RingHom.map_one]⟩)
  have h_mem : algebraMap Ainf BdR (k.frobE l).val ^ L.jumpBound * μ (φ ^ l • F.n i) ∈
      valueField 0 := by
    rw [F.frobE_pow_mul_apply_smul_n]
    exact sum_mem fun ν _ ↦
      mul_mem (F.coord_mem_hodgeFil_zero_and_mem_valueField l hμ ν).right (hZ_mem ν)
  simpa [phiInvToBdR] using div_mem h_mem (phiInvToBdR_mem_valueField (k.frobE l ^ L.jumpBound))

/-- Crystalline forms detect the coefficients of `F.comb m t`, up to the factor
`φ ^ m E ^ (a + a)` with `a = L.jumpBound`. Let `W` be a `BPlus`-submodule of `BdR`. If
`μ (F.comb m t) ∈ W` for every crystalline form `μ`, then `φ ^ m E ^ (a + a) * t i` maps into `W`
for every `i`. -/
private lemma phiInvToBdR_frobE_pow_mul_mem_of_forall_crysForms (F : Frame L) (m : ℕ)
    (W : Submodule BPlus BdR) (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf)
    (hW : ∀ μ ∈ L.crysForms, μ (F.comb m t) ∈ W) (i : Fin (finrank ℤ_[p] L.Carrier)) :
    phiInvToBdR 0 (k.frobE m ^ (L.jumpBound + L.jumpBound) * t i) ∈ W := by
  -- Test with the forms `σ ν` given by the rows of `φ ^ m M⁻¹`; their coordinates are the unit
  -- vectors. Then combine the values with row `i` of `φ ^ m Y` and use `Y * Z = E ^ (a + a)`.
  choose σ hσ using fun ν ↦ exists_functional_extend (L := L)
    ((algHom ℤ_[p] Bmax BdR).toLinearMap ∘ₗ
      (finBasis ℤ_[p] L.Carrier).constr ℕ (frobEnd^[m] ∘ F.M.inv ν))
  have h_unit (ν) : basisValues (σ ν) ᵥ* (frobPowToBdR m).mapMatrix F.M =
      (1 : Matrix _ _ BdR) ν := by
    funext l
    -- `using!`: `algHom ℤ_[p] Bmax BdR` and `algebraMap Bmax BdR` agree only by definition.
    simpa [frobPowToBdR, FrobGal.smul_def, hσ, Matrix.mul_apply, vecMul, dotProduct, basisValues,
      Matrix.one_apply] using! congrArg (fun X ↦ frobPowToBdR m (X ν l)) F.M.inv_val
  have h_eq : phiInvToBdR 0 (k.frobE m ^ (L.jumpBound + L.jumpBound) * t i) =
      ∑ ν, F.Y.map frobEnd^[m] i ν • (k.frobE m).val ^ L.jumpBound • σ ν (F.comb m t) := by
    simpa [↓F.frobE_pow_smul_apply_comb, ↓h_unit, ↓map_mul, ← mulVec_mulVec, val_frobE,
      algebraMap_eq_diagonal, phi_pow_smul, ↓mulVec.eq_1 (F.Y.map _), smul_def', phiInvToBdR,
      dotProduct, Matrix.one_apply, ← IsScalarTower.algebraMap_apply] using
      congr(algebraMap _ BdR (((frobEnd ^ m).mapMatrix $F.Y_mul_Z.symm *ᵥ ainfToBPlus ∘ t) i))
  refine h_eq ▸ sum_smul_mem W (F.Y.map frobEnd^[m] i) fun ν _ ↦
    W.smul_of_tower_mem _ (hW (σ ν) ⟨?_, _, hσ ν⟩)
  simp [F.mem_forms_iff m, ↓h_unit, Matrix.one_apply]

/-- For `x ∈ L.ainfLattice` and `a = L.jumpBound`, `τ ^ a • x` is a combination `F.comb 0 t` of
the `F.n i`. -/
private lemma exists_comb_eq_tau_pow_smul_of_mem_ainfLattice (F : Frame L) {x : L.Ambient}
    (hx : x ∈ L.ainfLattice) :
    ∃ t : Fin (finrank ℤ_[p] L.Carrier) → Ainf, F.comb 0 t = tau ^ L.jumpBound • x := by
  -- With `x = Σ α i (1 ⊗ e i)`, take `t = Q' * α` and use `Q * Q' = τ ^ (a + a)`.
  obtain ⟨α, rfl⟩ := ainfLattice_eq_range_latticeVec.le hx
  refine ⟨F.Q' *ᵥ α, ?_⟩
  simpa [comb, F.Q_mul_Q', pow_add, Fintype.linearCombination_apply, mul_smul, smul_mulVec] using
    F.tau_pow_smul_sum_eq_latticeVec (F.Q' *ᵥ α)

/-- Clause (a) of `frame_theorem`: an `S`-linear map `f : Ainf → S` carries a linear relation among
vectors of `L.valueFieldPoints L.fracSpan` to the relation with coefficients `f (c i)`. -/
private lemma sum_map_smul_eq_zero_of_sum_smul_eq_zero (F : Frame L) (f : Ainf →ₗ[k.S] k.S)
    {ι : Type} [Fintype ι] (v : ι → L.Ambient) (c : ι → Ainf)
    (hv : ∀ i : ι, v i ∈ L.valueFieldPoints L.fracSpan) (hc : ∑ i : ι, c i • v i = 0) :
    ∑ i : ι, f (c i) • v i = 0 := by
  -- A non-zero multiple of the sum is `F.comb 0 t`. The crystalline forms kill it, because
  -- `sum_phiInvToBdR_map_mul_mem_of_mem_valueField` carries the relation `μ (∑ i, c i • v i) = 0`
  -- through `f`; so `t = 0`.
  choose hv_frac hv_val using hv
  obtain ⟨r, hr, h_mem⟩ := fracSpan.sum_smul_mem (fun i ↦ f (c i)) (t := univ) fun i _ ↦ hv_frac i
  obtain ⟨t, ht⟩ := F.exists_comb_eq_tau_pow_smul_of_mem_ainfLattice h_mem
  have h_kill : ∀ μ ∈ L.crysForms, μ (F.comb 0 t) ∈ (⊥ : Submodule BPlus BdR) := by
    rintro μ ⟨hμ, -⟩
    have h_rel : ∑ i, phiInvToBdR 0 (c i) * μ (v i) ∈ (⊥ : Submodule BPlus BdR) := by
      simpa [smul_def', phiInvToBdR] using congrArg μ hc
    have h_zero : ∑ i, algebraMap Ainf BdR (f (c i)).val * μ (v i) = 0 := by
      simpa [phiInvToBdR] using
        sum_phiInvToBdR_map_mul_mem_of_mem_valueField f _ c (fun i ↦ hv_val i μ hμ) (W := ⊥) h_rel
    simp [ht, smul_def', h_zero]
  have ht_zero (i : Fin (finrank ℤ_[p] L.Carrier)) : t i = 0 := by
    simpa using F.phiInvToBdR_frobE_pow_mul_mem_of_forall_crysForms 0 ⊥ t h_kill i
  simpa [comb, nonZeroDivisors.ne_zero hr, ht_zero, smul_eq_val_smul,
    Fintype.linearCombination_apply] using
    ht.symm

/-- If `w` divides every coefficient `t i`, then `F.comb 0 t` is `w` times a combination of the
`F.n i`. -/
private lemma exists_smul_comb_eq_of_dvd (F : Frame L) (w : Ainf)
    (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf) (hw : ∀ i : Fin (finrank ℤ_[p] L.Carrier), w ∣ t i) :
    ∃ u : Fin (finrank ℤ_[p] L.Carrier) → Ainf, w • F.comb 0 u = F.comb 0 t := by
  obtain ⟨u, rfl⟩ : (fun _ : Fin (finrank ℤ_[p] L.Carrier) ↦ w) ∣ t := pi_dvd_iff.mpr hw
  exact ⟨u, (map_smul (F.comb 0) w u).symm⟩

/-- The test for `τ`: if every crystalline form sends `φ ^ (m + 1) • F.comb 0 t` into `hodgeFil 1`,
for every `m`, then `τ` divides every coefficient `t i`. -/
private lemma tau_dvd_of_forall_crysForms (F : Frame L) (t : Fin (finrank ℤ_[p] L.Carrier) → Ainf)
    (ht : ∀ m : ℕ, ∀ μ ∈ L.crysForms, μ (φ ^ (m + 1) • F.comb 0 t) ∈ hodgeFil 1)
    (i : Fin (finrank ℤ_[p] L.Carrier)) : tau ∣ t i := by
  -- By `tau_dvd_of_theta_frobEnd` it suffices that `E` divides every `φ ^ (m + 1) (t i)`. The
  -- factor `frobE (m + 1) ^ (a + a)` that the coefficient test leaves is prime to `E`.
  refine tau_dvd_of_theta_frobEnd fun m ↦ ?_
  have h_forms : ∀ μ ∈ L.crysForms, μ (F.comb (m + 1) fun j ↦ φ ^ (m + 1) • t j) ∈
      (hodgeFil 1).restrictScalars BPlus := by
    simpa [comb, smul_iterate, smul_sum, Fintype.linearCombination_apply, frobGroup_smul_smul,
      pow_succ, mul_smul]
      using ht m
  have h_fil : phiInvToBdR 0 (k.frobE (m + 1) ^ (L.jumpBound + L.jumpBound) * φ ^ (m + 1) • t i) ∈
      hodgeFil 1 :=
    F.phiInvToBdR_frobE_pow_mul_mem_of_forall_crysForms (m + 1) _ _ h_forms i
  have h_dvd : (k.frobE 0 : Ainf) ∣
      k.frobE (m + 1) ^ (L.jumpBound + L.jumpBound) * φ ^ (m + 1) • t i :=
    phiInvToBdR_mem_hodgeFil_one_iff.mp h_fil
  -- At index `0`, `thetaPhiInv` is `θ`; and `θ` does not kill `frobE (m + 1)`.
  have h_theta (r : Ainf) : thetaPhiInv 0 r = theta r := by simp [thetaPhiInv]
  have h_E_ne : theta (k.frobE (m + 1)).val ≠ 0 := by
    rw [← h_theta, Ne, ← frobE_dvd_iff]
    exact not_frobE_dvd_frobE_of_ne m.succ_pos.ne
  simpa [frobE_dvd_iff, phi_pow_smul, h_theta, h_E_ne] using h_dvd

/-- Let `x ∈ L.kisinAinf`. If `τ ^ N • x` is a combination `F.comb 0 t` of the `F.n i`, then so is
`x`: the powers of `τ` are removed one at a time by the test for `τ`. -/
private lemma exists_comb_eq_of_exists_comb_eq_tau_pow_smul (F : Frame L) {x : L.Ambient}
    (hx : x ∈ L.kisinAinf) (N : ℕ) :
    (∃ t : Fin (finrank ℤ_[p] L.Carrier) → Ainf, F.comb 0 t = tau ^ N • x) →
      ∃ t : Fin (finrank ℤ_[p] L.Carrier) → Ainf, F.comb 0 t = x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rintro ⟨t, ht⟩
    rw [pow_succ', mul_smul] at ht
    -- `E` divides `φ ^ (m + 1) τ`, so `τ ^ (N + 1) • x` passes the test for `τ`.
    have h_fil (m : ℕ) : ∀ μ ∈ L.crysForms, μ (φ ^ (m + 1) • F.comb 0 t) ∈ hodgeFil 1 := by
      rintro μ ⟨hμ, -⟩
      obtain ⟨-, hτx_forms⟩ := L.kisinAinf.smul_mem (tau ^ N) hx
      have h_tau : phiInvToBdR 0 (φ ^ (m + 1) • tau) ∈ hodgeFil 1 :=
        phiInvToBdR_mem_hodgeFil_one_iff.mpr (frobE_dvd_phi_pow_tau m.succ_pos)
      have h_forms : μ (φ ^ (m + 1) • tau ^ N • x) ∈ hodgeFil 0 := hτx_forms m μ hμ
      simpa [ht, smul_def', frobGroup_smul_smul, phiInvToBdR] using mul_mem_hodgeFil h_tau h_forms
    apply ih
    simpa [ht] using F.exists_smul_comb_eq_of_dvd tau t (F.tau_dvd_of_forall_crysForms t h_fil)

/-- The frame vectors `F.n i` span `L.kisinAinf` over `Ainf`. -/
private lemma span_n_eq_kisinAinf (F : Frame L) : span Ainf (Set.range F.n) = L.kisinAinf := by
  refine L.kisinAinf.span_eq_of_le (range_subset_iff.mpr F.n_mem_kisinAinf) fun x hx ↦ ?_
  -- Some `τ ^ N • x` lies in `L.ainfLattice`; then `τ ^ (a + N) • x` is a combination of the
  -- `F.n i`.
  obtain ⟨⟨_, ⟨N, rfl⟩, hτx⟩, -⟩ := Submodule.mem_inf.mp hx
  have h_comb : ∃ t : Fin (finrank ℤ_[p] L.Carrier) → Ainf,
      F.comb 0 t = tau ^ (L.jumpBound + N) • x := by
    simpa only [smul_smul, ← pow_add] using F.exists_comb_eq_tau_pow_smul_of_mem_ainfLattice hτx
  simpa [mem_span_range_iff_exists_fun, comb, Fintype.linearCombination_apply] using
    F.exists_comb_eq_of_exists_comb_eq_tau_pow_smul hx (L.jumpBound + N) h_comb

private lemma range_comb_zero (F : Frame L) : (F.comb 0).range = L.kisinAinf := by
  simpa [comb, Fintype.range_linearCombination] using F.span_n_eq_kisinAinf

/-- The vectors `φ ^ l • F.n i` span `L.valueFieldPoints (L.frobKisinAinf l)` over `S`. -/
private lemma span_phi_pow_smul_n_eq_valueFieldPoints (F : Frame L) (l : ℕ) :
    span k.S (Set.range fun i : Fin (finrank ℤ_[p] L.Carrier) ↦ φ ^ l • F.n i) =
      L.valueFieldPoints (L.frobKisinAinf l) := by
  refine (valueFieldPoints _).span_eq_of_le
    (range_subset_iff.mpr (F.phi_pow_smul_n_mem_valueFieldPoints l)) fun x hx ↦ ?_
  -- Write `φ ^ (-l) x = ∑ i, t i • n i` and apply the `S`-linear map `k.coord₀ : Ainf → S`, which
  -- sends `1` to `1`, to the relation `-x + ∑ i, φ ^ l (t i) • φ ^ l • n i = 0`.
  obtain ⟨hx_frob, hx_val⟩ := hx
  obtain ⟨t, ht⟩ := (mem_span_range_iff_exists_fun Ainf).mp (F.span_n_eq_kisinAinf.ge hx_frob)
  have h_le : L.frobKisinAinf l ≤ L.fracSpan :=
    fun y hy ↦ by simpa using smul_mem_fracSpan (φ ^ l) (kisinAinf_le_fracSpan hy)
  -- The vector `x` and the `φ ^ l • F.n i`, indexed by `Option`.
  let w : Option (Fin (finrank ℤ_[p] L.Carrier)) → L.Ambient :=
    fun o ↦ o.elim x fun i ↦ φ ^ l • F.n i
  have hw_frac : ∀ o, w o ∈ L.valueFieldPoints L.fracSpan := by
    rintro (_ | i)
    · exact ⟨h_le hx_frob, hx_val⟩
    · exact (F.phi_pow_smul_n_mem_valueFieldPoints l i).imp_left (h_le ·)
  have h_rel : ∑ o, k.coord₀ (φ ^ l • o.elim (-1) t) • w o = 0 := by
    refine F.sum_map_smul_eq_zero_of_sum_smul_eq_zero k.coord₀ w _ hw_frac ?_
    simp [w, ← frobGroup_smul_smul, ← smul_sum, ht]
  refine (mem_span_range_iff_exists_fun k.S).mpr ⟨fun i ↦ k.coord₀ (φ ^ l • t i), ?_⟩
  simpa [w, add_eq_zero_iff_eq_neg'] using h_rel

/-- The vectors `F.n i` are linearly independent over `Ainf`: crystalline forms detect the
coefficients. -/
private lemma linearIndependent_n (F : Frame L) : LinearIndependent Ainf F.n := by
  refine Fintype.linearIndependent_iff.mpr fun t ht i ↦ ?_
  have h_kill : ∀ μ ∈ L.crysForms, μ (F.comb 0 t) ∈ (⊥ : Submodule BPlus BdR) := by
    simp [comb, ht, Fintype.linearCombination_apply]
  simpa using F.phiInvToBdR_frobE_pow_mul_mem_of_forall_crysForms 0 ⊥ t h_kill i

/-- The frame vectors `F.n i` span the Kisin module over `S`. -/
private lemma span_n_eq_kisinModule (F : Frame L) : span k.S (Set.range F.n) = L.kisinModule := by
  simpa [frobKisinAinf_zero] using F.span_phi_pow_smul_n_eq_valueFieldPoints 0

/-- Clause (b) of `frame_theorem`. Let `3 e ≤ p ^ l` and `e A ≤ p ^ l δ`. Then `p ^ (4 δ)` times a
vector `x` of `L.valueFieldPoints (L.frobKisinAinf l)` lies in the `S`-span of the vectors `y`
of that module with `g • μ y - μ y ∈ hodgeFil A` for all `μ ∈ L.forms` and all `g ∈ Γ'`. -/
private lemma pow_smul_mem_span_of_mem_valueFieldPoints (F : Frame L) {l A δ : ℕ}
    (hl : 3 * k.e ≤ p ^ l) (hA : k.e * A ≤ p ^ l * δ) {x : L.Ambient}
    (hx : x ∈ L.valueFieldPoints (L.frobKisinAinf l)) :
    p ^ (4 * δ) • x ∈ span k.S
      {y ∈ L.valueFieldPoints (L.frobKisinAinf l) |
        ∀ μ ∈ L.forms, ∀ g : k.subgroup, toGp g.val • μ y - μ y ∈ hodgeFil A} := by
  -- The radius lemma writes `φ ^ l Z = frobE l ^ a • (D * V)` with `D` fixed by `Γ'`, and
  -- `p ^ (4 δ) • c` lies in the span of the `y` with `V * y` natural modulo `E ^ A`.
  simp only [← F.span_phi_pow_smul_n_eq_valueFieldPoints l, mem_span_range_iff_exists_fun] at hx ⊢
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨V, D, hD, hZV, h_rad⟩ :=
    radius_lemma (fixes _) (by simpa using (exists_smul_z 1).choose_spec) F.Z_mem F.Y_mul_Z
      (F.exists_smul_Z _ (fixes _)).choose_spec hl L.jumpBound
  rw [← Fintype.linearCombination_apply, ← map_nsmul]
  refine mapsTo_span (fun y hy ↦ ?_) (h_rad A δ hA c)
  refine ⟨⟨y, rfl⟩, fun μ hμ g ↦ ?_⟩
  -- Here `V * y = r + E ^ A • w` with `r` a vector of naturals.
  choose r w hw using mem_natCongruentSet.mp hy
  let coords : Fin (finrank ℤ_[p] L.Carrier) → BdR :=
    basisValues μ ᵥ* (frobPowToBdR l).mapMatrix F.M
  have h_val : ∑ i, (y i).val • μ (φ ^ l • F.n i) =
      coords ⬝ᵥ (↑) ∘ (D *ᵥ ((fun i ↦ (r i : BPlus)) + ainfToBPlus k.E.val ^ A • w)) := by
    simpa [coords, comb, hZV, ← mulVec_mulVec,
      eq_add_of_sub_eq' (funext hw : _ = (_ : BPlus) • w), algebraMap.smul, ← smul_sum, dotProduct,
      Function.comp_def, Fintype.linearCombination_apply, smul_mulVec] using
      F.frobE_pow_smul_apply_comb μ l fun i ↦ (y i : Ainf)
  -- The part with `r` is fixed by `g`, and the part with `E ^ A • w` lies in `hodgeFil A`.
  have h_coords_fix (ν : Fin (finrank ℤ_[p] L.Carrier)) : toGp g.val • coords ν = coords ν :=
    ((F.mem_forms_iff l).mp hμ g ν).symm
  have hD_fix (ν i : Fin (finrank ℤ_[p] L.Carrier)) : toGp g.val • D ν i = D ν i := by
    simpa using congrFun₂ (hD _ (fixes g).left) ν i
  have h_err : ∑ ν, coords ν *
      (phiInvToBdR 0 (k.frobE 0) ^ (A : ℤ) * algebraMap BPlus BdR (D ν ⬝ᵥ w)) ∈
        hodgeFil (0 + (A + 0)) :=
    sum_mem fun ν _ ↦ mul_mem_hodgeFil (F.coord_mem_hodgeFil_zero_and_mem_valueField l hμ ν).left
      (mul_mem_hodgeFil (phiInvToBdR_frobE_zpow_mem_hodgeFil 0 A) algebraMap_mem_hodgeFil_zero)
  simpa [h_val, ↓mulVec_add, mul_add, frobE, smul_sum, h_coords_fix, hD_fix,
    Fintype.linearCombination_apply, smul_eq_val_smul, dotProduct, mulVec_smul, mulVec,
    ← IsScalarTower.algebraMap_apply, sum_add_distrib, phiInvToBdR] using
    sub_mem (smul_mem_hodgeFil (toGp g) h_err) h_err

/-- Clause (d) of `frame_theorem`: for a crystalline form `μ` and `y` in the Kisin module,
`E ^ a • μ y` with `a = L.jumpBound` is the image of an element of `k.bicommutant`. -/
private lemma exists_mem_bicommutant_of_mem_kisinModule (F : Frame L) {μ : L.Functional}
    (hμ_crys : μ ∈ L.crysForms) {y : L.Ambient} (hy : y ∈ L.kisinModule) :
    ∃ s ∈ k.bicommutant, k.E.val ^ L.jumpBound • μ y = algebraMap BPlus BdR s := by
  -- The coordinates of `μ` are fixed elements of `Bmax`, so they come from `k.bicommutant`.
  obtain ⟨hμ, l, hl⟩ := hμ_crys
  rw [← F.span_n_eq_kisinModule] at hy
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun k.S).mp hy
  have h_fixed (ν : Fin (finrank ℤ_[p] L.Carrier)) (g : k.subgroup) :
      toGp g.val • ∑ i, l (finBasis ℤ_[p] L.Carrier i) * F.M i ν =
        ∑ i, l (finBasis ℤ_[p] L.Carrier i) * F.M i ν := by
    simpa [hl, frobPowToBdR, ← map_mul, ← map_sum, basisValues, Prod.mk_one_one, vecMul,
      dotProduct] using ((F.mem_forms_iff 0).mp hμ g ν).symm
  choose b hb_mem hb using fun ν ↦
    isChartOf.exists_mem_bicommutant_of_fixed
      (b := ∑ i, l (finBasis ℤ_[p] L.Carrier i) * F.M i ν) (h_fixed ν)
  refine ⟨b ⬝ᵥ F.Z *ᵥ ainfToBPlus ∘ fun i ↦ (c i : Ainf), ?_, ?_⟩
  · simp (maxDischargeDepth := 4) [sum_mem, mul_mem, hb_mem, F.Z_mem, dotProduct, mulVec]
  · simpa [hl, frobPowToBdR, ← map_mul, ← map_sum, ← hb, comb, Fintype.linearCombination_apply,
      frobE, smul_eq_val_smul,
      dotProduct, vecMul, basisValues, Prod.mk_one_one, ← IsScalarTower.algebraMap_apply] using
      F.frobE_pow_smul_apply_comb μ 0 fun i ↦ (c i : Ainf)

/-- Clause (e) of `frame_theorem`. Suppose `d` divides `r` whenever `d` divides `E ^ m r` in
`BPlus`. If every crystalline form `μ` has `E ^ n • μ x` in `BPlus ∙ d`, then `x ∈ L.kisinAinf` lies
in `d • L.kisinAinf`. -/
private lemma mem_smul_kisinAinf_of_forall_crysForms (F : Frame L) (d : Ainf)
    (hd : ∀ {m : ℕ} {r : Ainf}, ainfToBPlus d ∣ ainfToBPlus (k.E.val ^ m * r) → d ∣ r)
    {x : L.Ambient} (hx : x ∈ L.kisinAinf) {n : ℕ}
    (h_forms : ∀ μ ∈ L.crysForms, k.E.val ^ n • μ x ∈ BPlus ∙ algebraMap Ainf BdR d) :
    x ∈ d • L.kisinAinf := by
  -- Read off the coefficients of `x` modulo `d`; the two powers of `E` are dropped by `hd`.
  obtain ⟨t, rfl⟩ := F.range_comb_zero.ge hx
  have h_dvd (i : Fin (finrank ℤ_[p] L.Carrier)) : d ∣ t i := by
    have h_forms' (μ : L.Functional) (hμ : μ ∈ L.crysForms) :
        μ (F.comb 0 (k.E.val ^ n • t)) ∈ BPlus ∙ algebraMap Ainf BdR d := by
      rw [map_smul, map_smul]
      exact h_forms μ hμ
    obtain ⟨y, hy⟩ := mem_span_singleton.mp
      (F.phiInvToBdR_frobE_pow_mul_mem_of_forall_crysForms 0 _ (k.E.val ^ n • t) h_forms' i)
    have h_dvd_E : ainfToBPlus d ∣
        ainfToBPlus (k.E.val ^ (L.jumpBound + L.jumpBound) * (k.E.val ^ n * t i)) := by
      refine ⟨y, algebraMap_injective BPlus BdR ?_⟩
      simpa [frobE, commutes y, smul_def', ← IsScalarTower.algebraMap_apply, phiInvToBdR] using
        hy.symm
    exact hd (map_dvd ainfToBPlus (hd h_dvd_E))
  obtain ⟨u, hu⟩ := F.exists_smul_comb_eq_of_dvd d t h_dvd
  rw [← hu]
  exact smul_mem_pointwise_smul _ d _ (F.range_comb_zero.le ⟨u, rfl⟩)

/-- Clause (f) of `frame_theorem`: `τ ^ a`, with `a = L.jumpBound`, carries `L.kisinAinf` into
`L.ainfLattice`. -/
private lemma tau_pow_smul_mem_ainfLattice_of_mem_kisinAinf (F : Frame L) {x : L.Ambient}
    (hx : x ∈ L.kisinAinf) : tau ^ L.jumpBound • x ∈ L.ainfLattice := by
  obtain ⟨t, rfl⟩ := (mem_span_range_iff_exists_fun Ainf).mp (F.span_n_eq_kisinAinf.ge hx)
  simp [F.tau_pow_smul_sum_eq_latticeVec, ainfLattice_eq_range_latticeVec]

/-- Clause (g) of `frame_theorem`: `τ ^ a`, with `a = L.jumpBound`, carries `L.ainfLattice` into
`L.kisinAinf`. -/
private lemma tau_pow_smul_mem_kisinAinf_of_mem_ainfLattice (F : Frame L) {x : L.Ambient}
    (hx : x ∈ L.ainfLattice) : tau ^ L.jumpBound • x ∈ L.kisinAinf := by
  obtain ⟨t, ht⟩ := F.exists_comb_eq_tau_pow_smul_of_mem_ainfLattice hx
  exact F.range_comb_zero.le ⟨t, ht⟩

/-- Clause (h) of `frame_theorem`: `E ^ a • φ`, with `a = L.jumpBound` and `E` the unit
`k.frobEUnit 0` of `W(C♭)`, maps the Kisin module into itself. -/
private lemma frobEUnit_pow_smul_phi_smul_mem_kisinModule (F : Frame L) {x : L.Ambient}
    (hx : x ∈ L.kisinModule) : k.frobEUnit 0 ^ L.jumpBound • φ • x ∈ L.kisinModule := by
  -- We have `φ τ = E * τ * v` and `φ Q = v ^ a • (Q * B)`; cancel `τ ^ a` and `v ^ a`.
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun k.S).mp (F.span_n_eq_kisinModule.ge hx)
  refine F.span_n_eq_kisinModule.le ((mem_span_range_iff_exists_fun k.S).mpr ⟨F.B *ᵥ k.φ ∘ c, ?_⟩)
  simpa [mul_comm _ F.v.val, mul_comm _ tau, phi_smul_ainf, F.map_frobEnd_Q,
    ← F.isPeriodMatrixOf.E_mul_tau_mul, ← F.tau_pow_smul_sum_eq_latticeVec, ← mulVec_mulVec,
    mul_pow, ↓frobEUnit_pow_smul, Units.smul_def, smul_sum (r := φ), Chart.φ, frobE, comb, mulVec,
    dotProduct, smul_eq_val_smul, frobGroup_smul_smul, smul_mulVec, Fintype.linearCombination_apply,
    mul_smul] using
    (F.smul_comb_eq_latticeVec 1 fun i ↦ φ • (c i : Ainf)).symm

end Frame

/-- The properties of `L.kisinAinf` and of the Kisin module `L.kisinModule` given by the frame
theorem, with `a = L.jumpBound`, `S = k.S` the ring of the Kummer chart and `E = k.E`. -/
structure FrameProperties (L : JumpLattice O) : Prop where
  /-- (a) An `S`-linear map `f : Ainf → S` carries a relation `∑ i, c i • v i = 0` among vectors of
  `L.valueFieldPoints L.fracSpan` to the relation `∑ i, f (c i) • v i = 0`. -/
  sum_map_smul_eq_zero :
    ∀ (f : Ainf →ₗ[k.S] k.S) {ι : Type} [Fintype ι] (v : ι → L.Ambient) (c : ι → Ainf),
      (∀ i : ι, v i ∈ L.valueFieldPoints L.fracSpan) →
        ∑ i : ι, c i • v i = 0 → ∑ i : ι, f (c i) • v i = 0
  /-- (b) If `3 e ≤ p ^ l` and `e A ≤ p ^ l δ`, then `p ^ (4 δ)` times a vector of
  `L.valueFieldPoints (L.frobKisinAinf l)` lies in the `S`-span of the vectors `y` of that module
  with `g • μ y - μ y ∈ hodgeFil A` for every `μ ∈ L.forms` and every `g ∈ Γ'`. -/
  pow_smul_mem_span_of_mem_valueFieldPoints :
    ∀ l A δ : ℕ, 3 * k.e ≤ p ^ l → k.e * A ≤ p ^ l * δ →
      ∀ x ∈ L.valueFieldPoints (L.frobKisinAinf l),
        p ^ (4 * δ) • x ∈ span k.S
          {y ∈ L.valueFieldPoints (L.frobKisinAinf l) |
            ∀ μ ∈ L.forms, ∀ g : k.subgroup, toGp g.val • μ y - μ y ∈ hodgeFil A}
  /-- (c) `L.kisinAinf` is the `Ainf`-span of the Kisin module. -/
  kisinAinf_eq_span_kisinModule : L.kisinAinf = span Ainf (L.kisinModule : Set L.Ambient)
  /-- (d) For a crystalline form `μ` and `y` in the Kisin module, `E ^ a • μ y` is the image of an
  element of `k.bicommutant`. -/
  exists_mem_bicommutant_pow_smul_eq :
    ∀ μ ∈ L.crysForms, ∀ y ∈ L.kisinModule,
      ∃ s ∈ k.bicommutant, k.E.val ^ L.jumpBound • μ y = algebraMap BPlus BdR s
  /-- (e) Let `d ∈ Ainf` divide `r` whenever it divides `E ^ m r` in `BPlus`. Then `x ∈ L.kisinAinf`
  lies in `d • L.kisinAinf` once, for one `n`, `E ^ n • μ x ∈ BPlus ∙ d` for every crystalline form
  `μ`. -/
  mem_smul_kisinAinf_of_forall_crysForms :
    ∀ d : Ainf, (∀ {m : ℕ} {r : Ainf}, ainfToBPlus d ∣ ainfToBPlus (k.E.val ^ m * r) → d ∣ r) →
      ∀ x ∈ L.kisinAinf, ∀ n : ℕ,
        (∀ μ ∈ L.crysForms, k.E.val ^ n • μ x ∈ BPlus ∙ algebraMap Ainf BdR d) →
          x ∈ d • L.kisinAinf
  /-- (f) `τ ^ a` carries `L.kisinAinf` into `L.ainfLattice`. -/
  tau_pow_smul_mem_ainfLattice : ∀ x ∈ L.kisinAinf, tau ^ L.jumpBound • x ∈ L.ainfLattice
  /-- (g) `τ ^ a` carries `L.ainfLattice` into `L.kisinAinf`. -/
  tau_pow_smul_mem_kisinAinf : ∀ x ∈ L.ainfLattice, tau ^ L.jumpBound • x ∈ L.kisinAinf
  /-- (h) `E ^ a • φ`, with `E` the unit `k.frobEUnit 0` of `W(C♭)`, maps the Kisin module into
  itself. -/
  frobEUnit_pow_smul_phi_smul_mem_kisinModule :
    ∀ x ∈ L.kisinModule, k.frobEUnit 0 ^ L.jumpBound • φ • x ∈ L.kisinModule
  /-- (i) Some vectors `v i`, one for each index of a basis of `L`, span the Kisin module over `S`,
  span `L.kisinAinf` over `Ainf`, and are linearly independent over `Ainf`. -/
  exists_span_eq_kisinModule_linearIndependent :
    ∃ v : Fin (finrank ℤ_[p] L.Carrier) → L.Ambient,
      span k.S (Set.range v) = L.kisinModule ∧
      span Ainf (Set.range v) = L.kisinAinf ∧
      LinearIndependent Ainf v

/-- The frame theorem for the lattice `L` over the Kummer chart `k`: `L` has the nine properties of
`FrameProperties`. This gives part of Kisin's theorem: it shows `E ^ a φ N ⊆ N` but not the
finite-height inclusion `E ^ n N ⊆ S φ N`. That theorem concerns the module attached to a
crystalline lattice, for Kummer charts. -/
theorem frame_theorem : FrameProperties L := by
  -- Every field is read off a frame `F` of `L` (`Frame`). The vectors `F.n i` span `L.kisinAinf`
  -- over `Ainf`, and the `φ ^ l • F.n i` span `L.valueFieldPoints (L.frobKisinAinf l)` over `S`;
  -- the other fields are computations in these coordinates.
  obtain ⟨F⟩ : Nonempty (Frame L) := nonempty_frame
  exact
    { sum_map_smul_eq_zero := F.sum_map_smul_eq_zero_of_sum_smul_eq_zero
      pow_smul_mem_span_of_mem_valueFieldPoints l A δ hl hA x :=
        F.pow_smul_mem_span_of_mem_valueFieldPoints hl hA
      kisinAinf_eq_span_kisinModule := by
        rw [← F.span_n_eq_kisinModule, span_span_of_tower, F.span_n_eq_kisinAinf]
      exists_mem_bicommutant_pow_smul_eq μ hμ y := F.exists_mem_bicommutant_of_mem_kisinModule hμ
      mem_smul_kisinAinf_of_forall_crysForms d hd x hx n :=
        F.mem_smul_kisinAinf_of_forall_crysForms d hd hx
      tau_pow_smul_mem_ainfLattice x := F.tau_pow_smul_mem_ainfLattice_of_mem_kisinAinf
      tau_pow_smul_mem_kisinAinf x := F.tau_pow_smul_mem_kisinAinf_of_mem_ainfLattice
      frobEUnit_pow_smul_phi_smul_mem_kisinModule x := F.frobEUnit_pow_smul_phi_smul_mem_kisinModule
      exists_span_eq_kisinModule_linearIndependent :=
        ⟨F.n, F.span_n_eq_kisinModule, F.span_n_eq_kisinAinf, F.linearIndependent_n⟩ }

/-- `kisinAinf` is the A_inf-module of those x in A_inf[1/τ] ⊗ L with μ(φ^n x) ∈ B_dR⁺ for all n ≥ 1
and all Γ'-equivariant forms μ (`forms`). It equals the A_inf-span of the Kisin module
`kisinModule`, the S-module of its elements on which all these forms take values in the field
`k.valueField 0`. This is the field `kisinAinf_eq_span_kisinModule` of `frame_theorem`. -/
lemma kisinAinf_eq_span_kisinModule : L.kisinAinf = span Ainf (L.kisinModule : Set L.Ambient) :=
  frame_theorem.kisinAinf_eq_span_kisinModule

/-- Let `μ` be a crystalline invariant form of `L` (`crysForms`: an invariant functional
W(C^♭) ⊗ L → `BdR` whose restriction to 1 ⊗ L comes from a ℤ_p-linear map L → `Bmax`), and let `y`
be a vector of the Kisin module of `L`. Let `jumpBound` be the least a such that all Hodge–Tate
jumps of `L` lie in [−a, a]. Then `E ^ jumpBound • μ y` is the image in `BdR` of an element of
`bicommutant`, the ring S_B ⊂ `BPlus` of the chart. -/
lemma exists_mem_bicommutant_pow_smul_eq_of_mem_kisinModule {μ : L.Functional}
    (hμ : μ ∈ L.crysForms) {y : L.Ambient} (hy : y ∈ L.kisinModule) :
    ∃ s ∈ k.bicommutant, k.E.val ^ L.jumpBound • μ y = algebraMap BPlus BdR s :=
  frame_theorem.exists_mem_bicommutant_pow_smul_eq μ hμ y hy

/-- Crystalline forms detect divisibility in `kisinAinf`. Let powers of `E` cancel from `d`: if `d`
divides `E ^ m * r` in `BPlus`, then `d` divides `r` in `Ainf`. If `x` lies in `kisinAinf` and, for
one `n`, the values `E ^ n • μ x` of all crystalline invariant forms `μ` are `BPlus`-multiples of
`d`, then `x` lies in `d • kisinAinf`. -/
lemma mem_smul_kisinAinf_of_crysForms {d : Ainf}
    (h_cancel : ∀ {m : ℕ} {r : Ainf}, ainfToBPlus d ∣ ainfToBPlus (k.E.val ^ m * r) → d ∣ r)
    {x : L.Ambient} (hx : x ∈ L.kisinAinf) {n : ℕ}
    (h_val : ∀ μ ∈ L.crysForms, k.E.val ^ n • μ x ∈ BPlus ∙ algebraMap Ainf BdR d) :
    x ∈ d • L.kisinAinf :=
  frame_theorem.mem_smul_kisinAinf_of_forall_crysForms d h_cancel x hx n h_val

/-- Multiplication by `tau ^ jumpBound` maps `kisinAinf` into `ainfLattice`. -/
lemma tau_pow_jumpBound_smul_mem_ainfLattice_of_mem_kisinAinf {x : L.Ambient}
    (hx : x ∈ L.kisinAinf) : tau ^ L.jumpBound • x ∈ L.ainfLattice :=
  frame_theorem.tau_pow_smul_mem_ainfLattice x hx

/-- Multiplication by `tau ^ jumpBound` maps `ainfLattice` into `kisinAinf`. -/
lemma tau_pow_jumpBound_smul_mem_kisinAinf_of_mem_ainfLattice {x : L.Ambient}
    (hx : x ∈ L.ainfLattice) : tau ^ L.jumpBound • x ∈ L.kisinAinf :=
  frame_theorem.tau_pow_smul_mem_kisinAinf x hx

/-- For a jump lattice `L`, there is a family `v` in W(C^♭) ⊗ L, indexed by `Fin` of the ℤ_p-rank of
`L`, that is linearly independent over `Ainf`. Its `S`-span is the Kisin module of `L`, and its
`Ainf`-span is `kisinAinf`, the A_inf-module of the x in A_inf[1/τ] ⊗ L with μ(φ^n x) ∈ B_dR^+ for
all n ≥ 1 and all invariant forms μ. -/
lemma exists_span_eq_kisinModule_linearIndependent :
    ∃ v : Fin (finrank ℤ_[p] L.Carrier) → L.Ambient,
      span k.S (Set.range v) = L.kisinModule ∧
      span Ainf (Set.range v) = L.kisinAinf ∧
      LinearIndependent Ainf v :=
  frame_theorem.exists_span_eq_kisinModule_linearIndependent

private lemma mem_kisinAinf_of_mem_kisinModule {x : L.Ambient} (hx : x ∈ L.kisinModule) :
    x ∈ L.kisinAinf :=
  hx.left

/-- After inverting `tau`, the `Ainf`-span of the Kisin module and `ainfLattice` agree: they have
the same saturation by the powers of `tau`. This is a case of the comparison over `A_inf[1/μ]` for
Breuil–Kisin–Fargues modules (Bhatt–Morrow–Scholze 2018, Lemma 4.26), before the Frobenius twist. -/
lemma saturateBy_tau_span_kisinModule :
    saturateBy (Submonoid.powers tau) (span Ainf (L.kisinModule : Set L.Ambient)) =
      saturateBy (Submonoid.powers tau) L.ainfLattice := by
  -- `tau ^ jumpBound` carries each of `kisinAinf` and `ainfLattice` into the other.
  have h_le {M N : Submodule Ainf L.Ambient} (hMN : ∀ {x}, x ∈ M → tau ^ L.jumpBound • x ∈ N) :
      saturateBy (Submonoid.powers tau) M ≤ saturateBy (Submonoid.powers tau) N := by
    rintro x ⟨r, hr, hrx⟩
    exact ⟨tau ^ L.jumpBound * r, mul_mem ⟨L.jumpBound, rfl⟩ hr, by simpa [mul_smul] using hMN hrx⟩
  rw [← kisinAinf_eq_span_kisinModule]
  exact le_antisymm (h_le tau_pow_jumpBound_smul_mem_ainfLattice_of_mem_kisinAinf)
    (h_le tau_pow_jumpBound_smul_mem_kisinAinf_of_mem_ainfLattice)

/-- In W(C^♭) ⊗ L, `kisinAinf` is the A_inf-module of those `x` in A_inf[1/τ] ⊗ L with
μ(φ^n x) ∈ B_dR⁺ for all n ≥ 1 and all μ in `L.forms`. Then `x` lies in `kisinAinf` if
and only if two conditions hold. First, some power of `tau` = [ε^{1/p}] − 1 multiplies `x` into
`ainfLattice`, the A_inf-span of the elements 1 ⊗ y with y in L. Second, for some `n` and every `μ`
in `crysForms`, `E ^ n • μ x` is the image in `BdR` of an element of `BPlus`; here `crysForms` are
the invariant forms whose restriction to 1 ⊗ L comes from a Z_p-linear map L → `Bmax`, and `E` is
`k.E`. -/
theorem mem_kisinAinf_of_crysForms {x : L.Ambient}
    (hx_sat : x ∈ saturateBy (Submonoid.powers tau) L.ainfLattice) {n : ℕ}
    (h_val : ∀ μ ∈ L.crysForms, ∃ s : BPlus, k.E.val ^ n • μ x = algebraMap BPlus BdR s) :
    x ∈ L.kisinAinf := by
  -- Some `tau ^ N • x` lies in `kisinAinf`, and the crystalline forms show that it is divisible by
  -- `tau ^ N` there.
  rw [← saturateBy_tau_span_kisinModule, ← kisinAinf_eq_span_kisinModule] at hx_sat
  obtain ⟨_, ⟨N, rfl⟩, hx_tau⟩ := hx_sat
  obtain ⟨w, hw, hw_eq⟩ := (mem_smul_pointwise_iff_exists _ (tau ^ N) L.kisinAinf).mp <|
    mem_smul_kisinAinf_of_crysForms tau_pow_dvd_of_dvd_E_pow_mul hx_tau (n := n) fun μ hμ ↦
      (h_val μ hμ).elim fun s hs ↦ mem_span_singleton.mpr ⟨s, by
        rw [map_smul, smul_comm (k.E.val ^ n), hs, Algebra.smul_def, Algebra.smul_def, mul_comm]⟩
  rwa [← smul_right_injective L.Ambient (pow_ne_zero N tau_ne_zero) hw_eq]

/-- Let the vectors `v i` lie in the Kisin module of `L`, and let `u i ∈ Ainf`. Suppose that for
every `ν` in `crysForms` (the invariant A_inf-linear functionals to B_dR whose restriction to 1 ⊗ L
comes from a Z_p-linear map L → B_max), `E ^ n • ν (∑ i, u i • v i)` is the image in `BdR` of an
element of `bicommutant`, the elements of B^+ = A_max[1/p] whose multiplication commutes with every
S-linear endomorphism of B^+ preserving the image of A_max. Then every `μ` in `crysForms` vanishes
on `∑ i, (u i - k.coord₀ (u i)) • v i`, where `k.coord₀ (u i)` is the coordinate of `u i` in S for
the chosen topological basis of `Ainf` over S, i.e. the coordinate that is the identity on S. -/
lemma apply_sum_sub_coord₀_smul_eq_zero_of_mem_crysForms {μ : L.Functional} {ι : Type} [Fintype ι]
    {v : ι → L.Ambient} (hv_mem : ∀ i : ι, v i ∈ L.kisinModule) {u : ι → Ainf} {n : ℕ}
    (h_val : ∀ ν ∈ L.crysForms, ∃ s ∈ k.bicommutant,
      k.E.val ^ n • ν (∑ i : ι, u i • v i) = algebraMap BPlus BdR s)
    (hμ : μ ∈ L.crysForms) :
    μ (∑ i : ι, (u i - algebraMap k.S Ainf (k.coord₀ (u i))) • v i) = 0 := by
  -- Write `E ^ a • μ (v i)`, with `a = jumpBound`, as the image of `q i ∈ bicommutant`, and put
  -- `w i = E ^ n * q i`. In `BPlus`, `E ^ (a + n)` times the value on `∑ i, u i • v i` is
  -- `∑ i, u i * w i`, which lies in `bicommutant`. The extended coordinate at `1` fixes it and
  -- replaces each `u i` by its coordinate `c i`, so `E ^ (a + n)` kills the value on the
  -- difference.
  set a : ℕ := L.jumpBound
  set c : ι → Ainf := fun i ↦ algebraMap k.S Ainf (k.coord₀ (u i))
  choose q hq_mem hq using fun i : ι ↦
    exists_mem_bicommutant_pow_smul_eq_of_mem_kisinModule hμ (hv_mem i)
  obtain ⟨s, hs_mem, hs⟩ := h_val μ hμ
  let w : ι → BPlus := fun i ↦ ainfToBPlus (k.E.val ^ n) * q i
  have hw_mem (i : ι) : w i ∈ k.bicommutant :=
    mul_mem (ainfToBPlus_mem_bicommutant (k.E ^ n)) (hq_mem i)
  have h_value (r : ι → Ainf) : k.E.val ^ a • k.E.val ^ n • μ (∑ i, r i • v i) =
      algebraMap BPlus BdR (∑ i, ainfToBPlus (r i) * w i) := by
    simp only [map_sum, map_smul, Finset.smul_sum, smul_comm (k.E.val ^ a), a, hq]
    simp only [w, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def, mul_left_comm]
  have h_eq : ∑ i, ainfToBPlus (u i) * w i = ainfToBPlus (k.E.val ^ a) * s := by
    apply algebraMap_injective BPlus BdR
    rw [← h_value, hs, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  have h_mem : ainfToBPlus (k.E.val ^ a) * s ∈ k.bicommutant :=
    mul_mem (ainfToBPlus_mem_bicommutant (k.E ^ a)) hs_mem
  have h_coord (i : ι) :
      k.chart.extendedCoord k.oneIndex (ainfToBPlus (u i) * w i) = ainfToBPlus (c i) * w i := by
    rw [mul_comm, k.chart.extendToBPlus_mul _ (hw_mem i), k.chart.extendToBPlus_ainfToBPlus,
      LinearMap.comp_apply, Algebra.linearMap_apply, mul_comm]
  have h_fix : ∑ i, ainfToBPlus (c i) * w i = ∑ i, ainfToBPlus (u i) * w i := by
    simpa only [← h_eq, map_sum, h_coord] using k.chart.extendedCoord_oneIndex_eq_self h_mem
  have h_zero : k.E.val ^ a • k.E.val ^ n • μ (∑ i, (u i - c i) • v i) = 0 := by
    simp only [h_value, map_sub, sub_mul, Finset.sum_sub_distrib, h_fix, sub_self, map_zero]
  simpa only [smul_eq_zero, pow_ne_zero _ k.chart.E_ne_zero, false_or] using h_zero

/-- Let `x` be a vector of W(C^♭) ⊗ L, for a lattice `L` with jump sets over the Kummer chart `k`
with ring S. Then `x` lies in the Kisin module of `L` if and only if two conditions hold. First,
some power of `tau` = [ε^{1/p}] − 1 multiplies `x` into `ainfLattice`, the A_inf-span of the 1 ⊗ y
with y in L. Second, for some `n` and every `μ` in `crysForms` (the invariant A_inf-linear
functionals to B_dR whose restriction to 1 ⊗ L comes from a Z_p-linear map L → B_max), `E ^ n • μ x`
is the image in `BdR` of an element of `bicommutant`, the elements of B^+ = A_max[1/p] whose
multiplication commutes with every S-linear endomorphism of B^+ preserving the image of A_max. -/
theorem mem_kisinModule_iff_crysForms {x : L.Ambient} :
    x ∈ L.kisinModule ↔ x ∈ saturateBy (Submonoid.powers tau) L.ainfLattice ∧
      ∃ n : ℕ, ∀ μ ∈ L.crysForms, ∃ s ∈ k.bicommutant,
        k.E.val ^ n • μ x = algebraMap BPlus BdR s := by
  -- Forwards: crystalline forms on the Kisin module. Backwards: `x` lies in `kisinAinf`, so it is
  -- `∑ i, u i • v i` for a spanning family `v`. Replacing each `u i` by `coord₀ (u i)` changes `x`
  -- by a vector annihilated by every crystalline form, which is `0` by the `d = 0` divisibility
  -- test.
  obtain ⟨v, h_span_S, h_span_A, -⟩ := exists_span_eq_kisinModule_linearIndependent (L := L)
  refine ⟨fun hx ↦ ⟨(mem_kisinAinf_of_mem_kisinModule hx).left,
    L.jumpBound, fun μ hμ ↦ exists_mem_bicommutant_pow_smul_eq_of_mem_kisinModule hμ hx⟩, ?_⟩
  rintro ⟨hx_sat, n, h_val⟩
  obtain ⟨u, rfl⟩ := (mem_span_range_iff_exists_fun Ainf).mp <| h_span_A.ge <|
    mem_kisinAinf_of_crysForms hx_sat fun μ hμ ↦ (h_val μ hμ).imp fun _ h ↦ h.2
  have hv_mem i : v i ∈ L.kisinModule := h_span_S.le (subset_span ⟨i, rfl⟩)
  have h_diff : ∑ i, (u i - algebraMap k.S Ainf (k.coord₀ (u i))) • v i ∈
      (0 : Ainf) • L.kisinAinf := by
    refine mem_smul_kisinAinf_of_crysForms (fun {m r} h ↦ ?_)
      (sum_mem fun i _ ↦ L.kisinAinf.smul_mem _ (mem_kisinAinf_of_mem_kisinModule (hv_mem i)))
      (n := 0) fun μ hμ ↦ ?_
    · simpa only [map_zero, zero_dvd_iff, map_eq_zero_iff _ (algebraMap_injective Ainf BPlus),
        mul_eq_zero, pow_ne_zero m k.chart.E_ne_zero, false_or] using h
    · simp only [apply_sum_sub_coord₀_smul_eq_zero_of_mem_crysForms hv_mem h_val hμ, smul_zero,
        zero_mem]
  obtain ⟨y, -, hy⟩ := (mem_smul_pointwise_iff_exists _ (0 : Ainf) L.kisinAinf).mp h_diff
  rw [show ∑ i, u i • v i = ∑ i, k.coord₀ (u i) • v i by
    simpa only [zero_smul, sub_smul, Finset.sum_sub_distrib, algebraMap_smul, sub_eq_zero]
      using hy.symm]
  exact sum_mem fun i _ ↦ L.kisinModule.smul_mem (k.coord₀ (u i)) (hv_mem i)

end New.Lift.KummerChart.JumpLattice

end FrameTheorem

/-! ## Galois elements normalising a subgroup -/

namespace New.Lift.KummerChart.JumpLattice

open Period Submodule FrobGroup

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
  {k : KummerChart Γ} {O : Coeffs} {L : JumpLattice O} {x : L.Ambient} {μ : L.Functional}

/-- For the Kummer chart `k`, let `k.bicommutant` be its ring S_B: the elements of `BPlus` whose
multiplication commutes with every `k.S`-linear map of `BPlus` keeping the image of A_max. Let `E`
be the chart's element `k.E`. If `g ∈ G_p` and `d ∈ BPlus` are such that `d` divides `g • y - y` for
every `y` in `k.bicommutant`, and `x ∈ BdR` has `E ^ m • x` equal to the image of an element of
`k.bicommutant`, then `E ^ (2 * m) • (g • x - x)` is a `BPlus`-multiple of the image of `d` in
`BdR`. -/
lemma pow_smul_gal_sub_mem_span_of_dvd {g : Gp p} {d : BPlus} {m : ℕ} {x : BdR}
    (hd : ∀ {y : BPlus}, y ∈ k.bicommutant → d ∣ g • y - y)
    (hx_mem : ∃ s ∈ k.bicommutant, k.E.val ^ m • x = algebraMap BPlus BdR s) :
    k.E.val ^ (2 * m) • (g • x - x) ∈ BPlus ∙ algebraMap BPlus BdR d := by
  obtain ⟨s, hs, hx⟩ := hx_mem
  -- In `BdR` put `F = E ^ m`. As `g • E` is associate to `E`, `F = (g • F) v` for some `v`. As `g`
  -- moves elements of `bicommutant` by multiples of `d`, `g • F - F = d r` and `g • s - s = d t`.
  -- Then `F ^ 2 (g • x - x) = v (F (g • s - s) - (g • F - F) s) = v (F t - r s) d`.
  set F : BdR := algebraMap Ainf BdR (k.E.val ^ m) with hF
  set gF : BdR := algebraMap Ainf BdR ((g • k.E.val) ^ m) with hgF
  obtain ⟨v, hv⟩ : (g • k.E.val) ^ m ∣ k.E.val ^ m :=
    pow_dvd_pow_of_dvd (k.associated_smul_E g).dvd' m
  obtain ⟨r, hr⟩ :
      d ∣ g • algebraMap Ainf BPlus (k.E.val ^ m) - algebraMap Ainf BPlus (k.E.val ^ m) :=
    hd (k.ainfToBPlus_mem_bicommutant (k.E ^ m))
  obtain ⟨t, ht⟩ := hd hs
  have h_assoc : F = gF * algebraMap Ainf BdR v := by rw [hF, hgF, ← map_mul, ← hv]
  have h_x : F * x = algebraMap BPlus BdR s := by rw [hF, ← Algebra.smul_def, hx]
  have h_gx :
      gF * (g • x) = algebraMap BPlus BdR s + algebraMap BPlus BdR d * algebraMap BPlus BdR t :=
    calc gF * (g • x) = g • (F * x) := by simp [hF, hgF, smul_mul', smul_pow']
      _ = algebraMap BPlus BdR (g • s) := by rw [h_x, smul_algebraMap_eq_algebraMap_smul]
      _ = _ := by rw [eq_add_of_sub_eq' ht, map_add, map_mul]
  have h_gF : gF - F = algebraMap BPlus BdR d * algebraMap BPlus BdR r := by
    simpa [hF, hgF, ← IsScalarTower.algebraMap_apply, smul_pow'] using
      congrArg (algebraMap BPlus BdR) hr
  have h_key : F ^ 2 * (g • x - x) = algebraMap Ainf BdR v * (F * algebraMap BPlus BdR t -
      algebraMap BPlus BdR r * algebraMap BPlus BdR s) * algebraMap BPlus BdR d := by
    linear_combination (F * algebraMap Ainf BdR v) * h_gx + (F * g • x - algebraMap BPlus BdR s) *
      h_assoc - F * h_x - (algebraMap Ainf BdR v * algebraMap BPlus BdR s) * h_gF
  refine mem_span_singleton.mpr ⟨v • (k.E.val ^ m • t - r * s), ?_⟩
  simpa [hF, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, pow_mul'] using h_key.symm

/-- Let `g ∈ Γ` satisfy `g Γ' g⁻¹ ⊆ Γ'`, and let `μ` be a `Γ'`-equivariant form (`forms`). Then the
conjugate `conjForm μ g`, the form `y ↦ g⁻¹ • μ (g • y)`, is `Γ'`-equivariant. -/
lemma conjForm_mem_forms {g : GroupOverGp.G} (hg : ∀ γ ∈ k.subgroup, g * γ * g⁻¹ ∈ k.subgroup)
    (hμ : μ ∈ L.forms) : conjForm μ g ∈ L.forms := by
  -- For `γ ∈ Γ'`, use the equivariance of `μ` under `g γ g⁻¹ ∈ Γ'` at the vector `g t`.
  intro t γ
  simpa [mul_smul, inv_smul_eq_iff] using hμ (L.ρ g t) ⟨g * γ * g⁻¹, hg γ γ.prop⟩

/-- Let `g ∈ Γ` satisfy `g Γ' g⁻¹ ⊆ Γ'`. Then `g`, acting through `inr`, maps the module `kisinAinf`
of `L` into itself. -/
lemma smul_mem_kisinAinf {g : GroupOverGp.G} (hg : ∀ γ ∈ k.subgroup, g * γ * g⁻¹ ∈ k.subgroup)
    (hx : x ∈ L.kisinAinf) : inr g • x ∈ L.kisinAinf := by
  obtain ⟨⟨_, ⟨N, rfl⟩, hτx⟩, h_fil⟩ := hx
  refine ⟨?_, fun n μ hμ ↦ ?_⟩
  · -- `g • τ ^ N` multiplies `g • x` into `L.ainfLattice`, and it divides `τ ^ N`.
    have h_mem : (inr g • tau ^ N) • inr g • x ∈ L.ainfLattice := by
      simpa only [frobGroup_smul_smul] using smul_mem_ainfLattice (inr g) hτx
    have h_dvd : inr g • tau ^ N ∣ tau ^ N := by simp [associated_smul_tau.pow_pow.dvd]
    exact mem_saturateBy_of_smul h_dvd ⟨N, rfl⟩ (mem_saturateBy_of_mem h_mem)
  · -- The conjugate form `conjForm μ g` is again invariant, and `g` commutes with `φ`.
    have h_conj : conjForm μ g (φ ^ (n + 1) • x) ∈ hodgeFil 0 :=
      h_fil n (conjForm μ g) (conjForm_mem_forms hg hμ)
    have h_val : μ (inr g • φ ^ (n + 1) • x) ∈ hodgeFil 0 := by
      simpa using smul_mem_hodgeFil (toGp g) h_conj
    have h_comm : φ ^ (n + 1) * inr g = inr g * φ ^ (n + 1) :=
      ((FrobGroup.commute_phi (inr g)).pow_left (n + 1)).eq
    rwa [smul_smul, h_comm, ← smul_smul]

end New.Lift.KummerChart.JumpLattice
