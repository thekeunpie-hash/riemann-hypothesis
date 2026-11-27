module

import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
public import Lib.GaloisRep.Main.Defs
public import Lib.General.LinearAlgebra.MatrixPolynomials
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Lib.Shimura.HeckeTower.HeckeData
public import Lib.GaloisRep.Main.LocalConditions
public import Lib.GaloisRep.Pseudocharacter.SemisimpleRepresentations
public import Lib.PadicHodge.Limit.CrystallineLimit
import Lib.GaloisRep.Pseudocharacter.Pseudorepresentations
import Lib.General.LinearAlgebra.HermiteForm
import Lib.General.NumberTheory.SUnitsAndClassNumber
import Lib.PadicHodge.Characters
import Lib.PadicHodge.Crystalline.HodgeTateJumps
import Lib.PadicHodge.Limit.TraceLimit
public import Lib.ClassField.Avatar.HeckeBaseChange
public import Lib.Adelic.AutomorphicForms.SmoothAlgebraicForms
public import Lib.GaloisRep.Main.QuadraticStep
public import Lib.Shimura.TraceFormula.DefiniteTrace
import Lib.Adelic.Adeles.StrongApproximation
import Lib.General.LinearAlgebra.Eigenvalues
import Lib.General.NumberTheory.FrobeniusOrbits
import Lib.PadicHodge.Crystalline.HodgeTateForms
import Lib.Shimura.Eigenspace
import Lib.Shimura.IntegralModel.PELDataExistence
import Lib.Shimura.IntegralModel.TowerExistence
import Lib.Shimura.ThetaModuli.UniversalFamily
import Lib.Shimura.Transfer.WeightOccurs

section
/-!
# Free cocharacter weights force rank n and identify killing polynomials

A Galois representation that is only known to be killed, for most Frobenius elements (the filter
`New.mostFrobenii`), by monic polynomials of degree `n` is shown to have rank `n`, given that the
span of its image contains the diagonal matrices and that a one-parameter torus with `n` free
weights (`New.HasNoSmallRelations`) lies in the Zariski closure of a conjugate of the image of every
neighbourhood of `1`.

* `New.powMinor y m a`: a minor of order `m` of the matrix whose column `j < m` lists the entries of
  `y ^ j`. Over a field all of them vanish exactly when `1, y, …, y ^ (m - 1)` are linearly
  dependent.
* `New.exists_factor_charpoly`: over an integrally closed domain, if these minors all vanish, a
  factor of degree less than `m` of the characteristic polynomial of `y` kills `y`.
* `New.HasNoSmallRelations.inv_scalar_on_blocks`: if these minors vanish, with `m ≤ n + 1` and `c`
  surjective, for `diagonal (T ∘ e ∘ c) * x` over the Laurent polynomials, then `n < m` and on each
  fibre of `c` the block of `x⁻¹` is a scalar matrix.
* `New.card_eq_and_charpoly_eq`: the rank is `n` and the polynomials are the characteristic
  polynomials.

Notions from other files:
* `New.Ω`: the field `Ω` is an algebraic closure of `ℚ`: it has characteristic zero, is
  algebraically closed and is algebraic over `ℚ`.
* `New.HasNoSmallRelations e`: for `e : Fin n → ℤ`, distinct exponent vectors `α` of the same total
  degree at most `(n + 1) ^ 2` have distinct weights `∑ i, α i * e i`.
* `New.FrobeniusDatum E`: a place of degree one of `E` with a Frobenius element `frob` above it.
* `New.mostFrobenii E`: the filter of sets of such data that, inside every nonempty open set of
  `Gal(Ω/E)`, contain all data at almost all places whose Frobenius lies in a smaller nonempty open
  set.
* `T i`: the monomial of degree `i` in the Laurent polynomials `k[T;T⁻¹]`.

## Relation to the literature

Known result: Rank n and characteristic polynomials from Frobenius polynomial relations. Let a
continuous representation have image spanning the diagonal matrices, and let monic degree-n
polynomials kill it at most Frobenius elements. If a cocharacter with free (very different)
exponents constrains it, then its rank is n and the polynomials are its characteristic polynomials
at most Frobenius elements. This is one step inside the known construction of Galois representations
for definite unitary groups. In the literature, Frobenius polynomial relations on a dense set
determine a representation when the n-dimensional one is known and large. Related work:
Boston–Lenstra–Ribet 1991; Nekovář, Eichler–Shimura relations and semisimplicity, 2018;
Fayad–Nekovář 2019; Harris–Taylor 2001, VII.1.8.

See also `Lib.GaloisRep.Main.OddRank`.
-/

@[expose] public section

namespace New

open Matrix MvPolynomial Polynomial Finset Algebra Fintype Submodule Function ConjAct
  LaurentPolynomial Fin Filter

variable {k K N R S A : Type} [NormedField k] [Fintype N] [DecidableEq N] [CommRing R] [CommRing S]
  {m n : ℕ} {e : Fin n → ℤ}
  (y : Matrix N N R) [NormedField K] [NormedAlgebra K k] [CommRing A] [Algebra A R] [Algebra A S]

/-- The minor of order `m`, at the rows `a 0, …, a (m - 1)`, of the matrix with rows indexed by
`N × N` whose column `j < m` lists the entries of the square matrix `y ^ j`: its entry at `(i, j)`
is the entry of `y ^ j` at the place `a i`. -/
noncomputable abbrev powMinor (m : ℕ) (a : Fin m → N × N) : R :=
  (of (flip (fun j : Fin m ↦ uncurry (y ^ j.val)) ∘ a)).det

@[simp]
lemma map_powMinor (a : Fin m → N × N) (φ : R →ₐ[A] S) :
    φ (powMinor y m a) = powMinor (φ.mapMatrix y) m a := by
  have h_pow (j : ℕ) : y.map φ ^ j = (y ^ j).map φ := (map_pow φ.mapMatrix y j).symm
  rw [powMinor, powMinor, φ.map_det]
  congr 1
  ext i j
  simp [h_pow, flip, uncurry]

/-- Let `y` be a square matrix over an integrally closed domain `R`. If all minors `powMinor y m a`
of its first `m` powers vanish, then `y.charpoly = p * q` with `p` of degree less than `m` and
`p(y) = 0`. -/
lemma exists_factor_charpoly [IsDomain R] [IsIntegrallyClosed R]
    (h_minor : ∀ a : Fin m → N × N, powMinor y m a = 0) :
    ∃ p q : R[X], y.charpoly = p * q ∧ p.natDegree < m ∧ p.aeval y = 0 := by
  -- Over the fraction field the first `m` powers of `y` are dependent.
  let F : Type := FractionRing R
  let z : Matrix N N F := (ofId R F).mapMatrix y
  have h_lt : (minpoly F z).natDegree < m := by
    by_contra! h_le
    have hz_minor (a : Fin m → N × N) : powMinor z m a = 0 := by
      rw [← map_powMinor y a (ofId R F), h_minor a, map_zero]
    have h_pow : LinearIndependent F fun j : Fin m ↦ z ^ (j : ℕ) :=
      (linearIndependent_pow z).comp (castLE h_le) (castLE_injective h_le)
    exact det_eval_eq_zero_iff_not_linearIndependent.mp hz_minor
      (h_pow.of_comp (LinearEquiv.curry (R := F) (M := F) (V := N) (V₂ := N)).toLinearMap)
  -- By Gauss's lemma the minimal polynomial comes from a monic factor `p` of `y.charpoly`.
  have h_monic : (minpoly F z).Monic := minpoly.monic z.isIntegral
  have h_dvd : minpoly F z ∣ y.charpoly.map (algebraMap R F) :=
    z.minpoly_dvd_charpoly.trans (charpoly_map y (algebraMap R F)).dvd
  have h_lifts : minpoly F z ∈ lifts (algebraMap R F) := by
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd F y.charpoly_monic h_dvd
    exact (mem_lifts _).mpr ⟨g, by simpa [h_monic.leadingCoeff] using hg⟩
  obtain ⟨p, hp, hp_deg, hp_monic⟩ := lifts_and_natDegree_eq_and_monic h_lifts h_monic
  obtain ⟨q, hq⟩ : p ∣ y.charpoly :=
    (map_dvd_map (algebraMap R F) (IsFractionRing.injective R F) hp_monic).mp (by rwa [hp])
  -- The image of `p(y)` over `F` is `p(z)`, a value of the minimal polynomial of `z`.
  have hz_root : (ofId R F).mapMatrix (p.aeval y) = 0 := by
    rw [← aeval_algHom_apply, ← Polynomial.aeval_map_algebraMap F, hp, minpoly.aeval]
  exact ⟨p, q, hq, by lia, Matrix.map_injective (IsFractionRing.injective R F)
    (by simpa [ofId] using hz_root)⟩

/-- Let the weights `e : Fin n → ℤ` be free (`HasNoSmallRelations e`: distinct exponent vectors of
one total degree at most `(n + 1) ^ 2` have distinct weights `∑ i, α i * e i`), let `c : N → Fin n`,
let `x` be an invertible matrix over `k` and let `m ≤ n + 1`. If all minors `powMinor` of order `m`
of the product of the diagonal matrix with entries `T (e (c a))` and `x` over `k[T;T⁻¹]` vanish,
then so do those of the product of the diagonal matrix with entries `X (c a)` and `x` over the
polynomials in the variables `X i`. -/
private lemma powMinor_diagonal_X_mul_eq_zero {c : N → Fin n} (he : HasNoSmallRelations e)
    {x : GL N k} (hm_le : m ≤ n + 1)
    (h_vanish : ∀ a : Fin m → N × N,
      powMinor (diagonal (T ∘ e ∘ c) * (x : Matrix N N k).map LaurentPolynomial.C) m a = 0)
    (a : Fin m → N × N) :
    powMinor (diagonal (X ∘ c) * (x : Matrix N N k).map MvPolynomial.C) m a = 0 := by
  set y : Matrix N N (MvPolynomial (Fin n) k) :=
    diagonal (X ∘ c) * (x : Matrix N N k).map MvPolynomial.C
  -- Each entry of `y ^ j` is homogeneous of degree `j`.
  have hy (j : ℕ) : ∀ a b : N, ((y ^ j) a b).IsHomogeneous j := by
    induction j with
    | zero => simp [← totalDegree_zero_iff_isHomogeneous, Matrix.one_apply, apply_ite]
    | succ j ih =>
      simp_all [y, pow_add, Matrix.mul_apply, diagonal, mul_comm (X _), isHomogeneous_C_mul_X,
        IsHomogeneous.mul, IsHomogeneous.sum]
  -- The substitution `X i ↦ T (e i)` sends the minor to zero.
  let ψ : MvPolynomial (Fin n) k →ₐ[k] k[T;T⁻¹] :=
    AddMonoidAlgebra.mapDomainAlgHom k k (Finsupp.weight e)
  have hψ_X (i : Fin n) : ψ (X i) = T (e i) := by
    simp [ψ, MvPolynomial.X, ← MvPolynomial.single_eq_monomial, Finsupp.weight_single]
  have h_subst : ψ.mapMatrix y =
      diagonal (T ∘ e ∘ c) * (x : Matrix N N k).map LaurentPolynomial.C := by
    ext i j
    simp [y, hψ_X, LaurentPolynomial.algebraMap_apply]
  have h_zero : ψ (powMinor y m a) = 0 := by rw [map_powMinor, h_subst, h_vanish a]
  -- The monomials of the minor have one degree `≤ (n + 1) ^ 2`, so by freeness the substitution
  -- keeps them apart.
  have h_hom : (powMinor y m a).IsHomogeneous (∑ i : Fin m, (i : ℕ)) := by
    -- In the Leibniz formula each product `∏ i, (y ^ i) (a (σ i))` has degree `∑ i, i`.
    rw [powMinor, det_apply']
    refine IsHomogeneous.sum (h := fun σ _ ↦ ?_)
    rw [← map_intCast (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)]
    exact (IsHomogeneous.prod (h := fun (i : Fin m) _ ↦ hy i (a (σ i)).fst (a (σ i)).snd)).C_mul _
  have h_deg : ∑ i : Fin m, (i : ℕ) ≤ (n + 1) ^ 2 := by
    grw [isLt, ← hm_le]
    simp [sq]
  have h_inj : Set.InjOn (Finsupp.weight e) (powMinor y m a).support :=
    (he (∑ i : Fin m, (i : ℕ)) h_deg).mono
      ((homogeneousSubmodule_eq_finsupp_supported (Fin n) k (∑ i : Fin m, (i : ℕ))).le h_hom)
  -- As `ψ` is injective on the monomials of the minor, the minor is zero.
  have h_support : (ψ (powMinor y m a)).coeff.support =
      (powMinor y m a).support.image (Finsupp.weight e) :=
    Finsupp.mapDomain_support_of_injOn _ h_inj
  rw [h_zero] at h_support
  simpa using h_support.symm

/-- Let the weights `e : Fin n → ℤ` be free (`HasNoSmallRelations e`: distinct exponent vectors of
one total degree at most `(n + 1) ^ 2` have distinct weights `∑ i, α i * e i`), let `c : N → Fin n`
be onto, let `x` be an invertible matrix over `k`, let `m ≤ n + 1`, and let `y` be the product, over
the Laurent polynomials `k[T;T⁻¹]`, of the diagonal matrix with entries `T (e (c a))` and `x`.
Suppose every `powMinor y m a` vanishes, where `powMinor y m a` is the `m × m` minor at rows
`a 0, …, a (m - 1)` of the matrix with rows indexed by `N × N` whose column `j < m` lists the
entries of `y ^ j`. Then `n < m`, and for `a ≠ b` with `c a = c b` the inverse `x⁻¹` has entry `0`
at `(a, b)` and equal entries at `(a, a)` and `(b, b)`. -/
lemma HasNoSmallRelations.inv_scalar_on_blocks {c : N → Fin n} (he : HasNoSmallRelations e)
    (hc : Surjective c) {x : GL N k} (hm_le : m ≤ n + 1)
    (h_vanish : ∀ a : Fin m → N × N,
      powMinor (diagonal (T ∘ e ∘ c) * (x : Matrix N N k).map LaurentPolynomial.C) m a = 0) :
    n < m ∧
      ∀ {a b : N}, c a = c b → a ≠ b → x⁻¹ a b = 0 ∧ x⁻¹ a a = x⁻¹ b b := by
  -- Replace `T (e i)` by variables `X i`. The minors still vanish, so a factor `p` of the
  -- characteristic polynomial of the resulting matrix `y` has degree `< m` and kills `y`.
  -- Its constant term is divisible by every `X i`, which forces the degree `n` and the monomial
  -- `∏ i, X i`; the coefficient of this monomial in `p(y) x⁻¹ = 0` gives the entries of `x⁻¹`.
  let y : Matrix N N (MvPolynomial (Fin n) k) :=
    diagonal (X ∘ c) * (x : Matrix N N k).map MvPolynomial.C
  obtain ⟨p, q, hq, hp_deg, hp_root⟩ :=
    exists_factor_charpoly y (powMinor_diagonal_X_mul_eq_zero he hm_le h_vanish)
  -- As `det y ≠ 0`, the constant term of `p` contains a monomial `α`.
  have h_det : y.det ≠ 0 := by simpa [y, prod_eq_zero_iff] using (x.map _).det_ne_zero
  obtain ⟨hp_const, hq_const⟩ : p.coeff 0 ≠ 0 ∧ q.coeff 0 ≠ 0 := by
    simpa [det_eq_sign_charpoly_coeff, hq] using h_det
  obtain ⟨α, hα⟩ := ne_zero_iff.mp hp_const
  -- In its own variable and the `X i` together, `y.charpoly` has total degree at most `card N`,
  -- its degree in its own variable.
  have h_total : ((optionEquivLeft k (Fin n)).symm y.charpoly).totalDegree ≤ card N := by
    -- In the Leibniz formula each of the `card N` factors has total degree at most one.
    suffices h : MvPolynomial.totalDegree (∑ σ : Equiv.Perm N, Equiv.Perm.sign σ • ∏ i : N,
        ((if σ i = i then MvPolynomial.X none else 0) -
          MvPolynomial.X (some (c (σ i))) *
            MvPolynomial.C ((x : Matrix N N k) (σ i) i))) ≤ card N by
      simpa [charpoly, det_apply, y, charmatrix, diagonal_apply, apply_ite] using h
    grw (transparency := .default) [totalDegree_finsetSum, totalDegree_smul_le,
      totalDegree_finsetProd, totalDegree_sub, totalDegree_mul]
    simp [ite_apply, apply_ite]
  set Φ : (MvPolynomial (Fin n) k)[X] ≃ₐ[k] MvPolynomial (Option (Fin n)) k :=
    (optionEquivLeft k (Fin n)).symm with hΦ
  have hp_ne : Φ p ≠ 0 := by aesop
  have hq_ne : Φ q ≠ 0 := by aesop
  -- Total degrees add, that of `α` is at most that of `p`, and that of `q` is at least
  -- `q.natDegree`; so `α` has degree at most `p.natDegree`.
  have hα_p : ∑ i, α i ≤ (Φ p).totalDegree := calc
    ∑ i, α i ≤ (p.coeff 0).totalDegree := by
      simpa [α.sum_fintype] using le_totalDegree (mem_support_iff.mpr hα)
    _ ≤ (Φ p).totalDegree := by
      simpa [hΦ] using totalDegree_coeff_optionEquivLeft_le (p := Φ p) (i := 0)
  have hq_le : q.natDegree ≤ (Φ q).totalDegree := by
    simpa [hΦ, ← natDegree_optionEquivLeft] using degreeOf_le_totalDegree (Φ q) none
  have hα_le : ∑ i, α i ≤ p.natDegree := by
    have h_add : (Φ p).totalDegree + (Φ q).totalDegree ≤ p.natDegree + q.natDegree := by
      rw [← totalDegree_mul_of_isDomain hp_ne hq_ne, ← map_mul, ← hq]
      grw [h_total, ← y.charpoly_natDegree_eq_dim, hq, natDegree_mul_le]
    lia
  -- Write `0 = p(y) = y * (r(y) * y + p₁) + p₀` with `r = p.divX.divX`. Row `a` of `y` is
  -- divisible by `X (c a)`, so `p₀` is, and every variable occurs in `α`.
  have hp_split : p = Polynomial.X * (p.divX.divX * Polynomial.X + Polynomial.C (p.divX.coeff 0)) +
      Polynomial.C (p.coeff 0) := by rw [p.divX.divX_mul_X_add, p.X_mul_divX_add]
  have hα_pos : 1 ≤ ⇑α := by
    refine hc.forall.mpr fun a ↦ Nat.pos_of_ne_zero fun hα_zero ↦ hα ?_
    -- If `α` missed the variable `X (c a)`, only `p₀` would contribute to the coefficient of `α`.
    have h_coeff : ((p.aeval y) a a).coeff α = 0 := by simp [hp_root]
    rw [hp_split] at h_coeff
    simpa [y, algebraMap, comp_def, mul_assoc, coeff_X_mul', hα_zero] using h_coeff
  -- Now `n ≤ ∑ i, α i ≤ p.natDegree < m ≤ n + 1`, so each variable occurs once.
  have h_card : n ≤ ∑ i, α i := by simpa using sum_mono hα_pos
  have hα_one : ⇑α = 1 := by
    by_contra h_ne
    have : n < ∑ i, α i := by simpa using sum_strictMono (hα_pos.lt_of_ne' h_ne)
    lia
  refine ⟨by lia, fun {a b} hab hne ↦ ?_⟩
  -- The entry `(a, b)` of `y * r(y) * y * x⁻¹` is divisible by `X (c a) * X (c b)`, so it does not
  -- contain `α` if `c a = c b`; the term `y * p₁ * x⁻¹` is diagonal and depends only on `c a`;
  -- the last term is `p₀ * x⁻¹`, and `α` occurs in `p₀`.
  have h_entry (a b : N) : ((p.aeval y * (x : Matrix N N k)⁻¹.map MvPolynomial.C :
      Matrix N N (MvPolynomial (Fin n) k)) a b).coeff α = 0 := by simp [hp_root]
  rw [hp_split] at h_entry
  -- Two passes normalize the coefficient equation (they use `mul_assoc` in opposite directions);
  -- its normal form is unreadable, so the three entries used are stated just below.
  simp [y, add_mul, mul_add, algebraMap, map_add, comp_def, mul_assoc, coeff_X_mul'] at h_entry
  simp [← mul_assoc, coeff_mul_X', mul_comm (p.coeff _), hα_one] at h_entry
  have h_ab : (x : Matrix N N k)⁻¹ a b = 0 ∨ (p.coeff 0).coeff α = 0 := by
    simpa [hab, hne] using h_entry a b
  have h_diag (a' : N) (ha' : c a' = c b) : (MvPolynomial.X (c b) * p.coeff 1).coeff α +
      (x : Matrix N N k)⁻¹ a' a' * (p.coeff 0).coeff α = 0 := by
    simpa [ha'] using h_entry a' a'
  rw [Matrix.coe_units_inv]
  exact ⟨h_ab.resolve_right hα,
    mul_right_cancel₀ hα (by linear_combination h_diag a hab - h_diag b rfl)⟩

/-- Let the weights `e : Fin n → ℤ` be free, let `c : N → Fin n` be onto, let `x` be an invertible
matrix over `k` and let `m ≤ n + 1`. If all minors `powMinor` of order `m` of the product of the
diagonal matrix with entries `T (e (c a))` and `x` over `k[T;T⁻¹]` vanish, then `n < m`. -/
private lemma HasNoSmallRelations.lt_of_powMinor_eq_zero {c : N → Fin n}
    (he : HasNoSmallRelations e) (hc : Surjective c) {x : GL N k} (hm_le : m ≤ n + 1)
    (h_vanish : ∀ a : Fin m → N × N,
      powMinor (diagonal (T ∘ e ∘ c) * (x : Matrix N N k).map LaurentPolynomial.C) m a = 0) :
    n < m :=
  (he.inv_scalar_on_blocks hc hm_le h_vanish).left

/-- Let the weights `e : Fin n → ℤ` be free, let `c : N → Fin n` be onto, let `x` be an invertible
matrix over `k` and let `m ≤ n + 1`. If all minors `powMinor` of order `m` of the product of the
diagonal matrix with entries `T (e (c a))` and `x` over `k[T;T⁻¹]` vanish, then for `a ≠ b` with
`c a = c b` the inverse `x⁻¹` has entry `0` at `(a, b)` and equal entries at `(a, a)` and `(b, b)`.
-/
private lemma HasNoSmallRelations.inv_apply_eq_zero_and_eq_of_powMinor_eq_zero {c : N → Fin n}
    (he : HasNoSmallRelations e) (hc : Surjective c) {x : GL N k} (hm_le : m ≤ n + 1)
    (h_vanish : ∀ a : Fin m → N × N,
      powMinor (diagonal (T ∘ e ∘ c) * (x : Matrix N N k).map LaurentPolynomial.C) m a = 0)
    {a b : N} (hab : c a = c b) (hne : a ≠ b) : x⁻¹ a b = 0 ∧ x⁻¹ a a = x⁻¹ b b :=
  (he.inv_scalar_on_blocks hc hm_le h_vanish).2 hab hne

/-- If a nonzero polynomial `p` of degree less than `m` kills the matrix `M` over `K`, then all
minors `powMinor (φ M) m a` vanish, for any `K`-algebra map `φ` into the matrices over `k`. -/
private lemma powMinor_eq_zero_of_aeval_eq_zero (φ : Matrix N N K →ₐ[K] Matrix N N k)
    {M : Matrix N N K} {p : K[X]} (hp : p ≠ 0) (h_root : p.aeval M = 0)
    (h_deg : p.natDegree < m) : powMinor (φ M) m = 0 := by
  -- The coefficients of `p` give a relation among the first `m` powers of `φ M`.
  have h_sum : ∑ i : Fin m, p.coeff i • φ M ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ p.coeff i • φ M ^ i), ← aeval_eq_sum_range' h_deg,
      aeval_algHom_apply, h_root, map_zero]
  have h_dep : ¬LinearIndependent K fun i : Fin m ↦ uncurry (φ M ^ (i : ℕ)) := by
    refine not_linearIndependent_iff.mpr
      ⟨fun i ↦ p.coeff i, funext fun ⟨a, b⟩ ↦ ?_, ⟨p.natDegree, h_deg⟩, by simpa using hp⟩
    simpa [uncurry, Matrix.sum_apply] using congrFun₂ h_sum a b
  exact funext (det_eval_eq_zero_iff_not_linearIndependent.mpr fun h_ind ↦
    h_dep (h_ind.restrict_scalars' K))

/-- Let `N` have `n ≥ 1` elements and let a monic polynomial `P` of degree `n` kill the matrix `M`
over `K`. If some minor `powMinor (φ M) n a` is nonzero, for a `K`-algebra map `φ` into the
matrices over `k`, then `P` is the characteristic polynomial of `M`: otherwise `M.charpoly - P`
would be a nonzero polynomial of degree less than `n` that kills `M`. -/
private lemma charpoly_eq_of_powMinor_ne_zero [NeZero n] (φ : Matrix N N K →ₐ[K] Matrix N N k)
    (hN : card N = n) {M : Matrix N N K} {P : K[X]} (h_root : P.aeval M = 0)
    (h_monic : P.IsMonicOfDegree n) (h_minor : powMinor (φ M) n ≠ 0) : M.charpoly = P := by
  have h_char : M.charpoly.IsMonicOfDegree n :=
    ⟨by rw [charpoly_natDegree_eq_dim, hN], charpoly_monic M⟩
  by_contra hne
  have h_sub_root : (M.charpoly - P).aeval M = 0 := by simp [h_root, aeval_self_charpoly]
  exact h_minor (powMinor_eq_zero_of_aeval_eq_zero φ (sub_ne_zero.mpr hne) h_sub_root
    (h_char.natDegree_sub_lt NeZero.out h_monic))

/-- Free weights `e : Fin n → ℤ` are pairwise distinct: apply freeness to the exponent vectors of
degree one. -/
private lemma HasNoSmallRelations.injective (he : HasNoSmallRelations e) : e.Injective := by
  intro i j h_eq
  have h_deg (i : Fin n) : Finsupp.single i 1 ∈ {α : Fin n →₀ ℕ | Finsupp.degree α = 1} := by simp
  exact Finsupp.single_left_injective one_ne_zero
    (he 1 (Nat.one_le_pow 2 (n + 1) n.succ_pos) (h_deg i) (h_deg j)
      (by simpa [Finsupp.weight_single] using h_eq))

/-- Let `e : Fin n → ℤ` be injective, `κ : N → ℤ` and `l : Fin n → N` with `κ (l i) = e i`. If all
minors of order `n + 1` of the first `n + 1` powers of the diagonal matrix with entries `T (κ j)`
vanish, then every `κ j` is one of the `e i`: otherwise the minor at the diagonal places
`j, l 0, …, l (n - 1)` would be a Vandermonde determinant of distinct monomials. -/
private lemma exists_eq_of_powMinor_diagonal_eq_zero (he_inj : e.Injective) {κ : N → ℤ}
    {l : Fin n → N} (hl : ∀ i : Fin n, κ (l i) = e i)
    (h_minor : ∀ a : Fin (n + 1) → N × N,
      powMinor (diagonal (T ∘ κ) : Matrix N N k[T;T⁻¹]) (n + 1) a = 0)
    (j : N) : ∃ i : Fin n, e i = κ j := by
  let a : Fin (n + 1) → N := cons j l
  obtain ⟨i, i', h_T_eq, h_ne⟩ : ∃ i i', (T (κ (a i)) : k[T;T⁻¹]) = T (κ (a i')) ∧ i ≠ i' := by
    apply det_vandermonde_eq_zero_iff.mp
    simpa [powMinor, diagonal_pow, flip_def, uncurry, vandermonde, comp_def] using
      h_minor (Function.diag ∘ a)
  -- `T` is unfolded to compare monomials; `single_eq_C_mul_T` would fold it back, a loop.
  have hκ_eq : κ (a i) = κ (a i') := by
    simpa [T, AddMonoidAlgebra.single_inj, -single_eq_C_mul_T] using h_T_eq
  -- The equal weights are at `j` and some `l i`, or at two `l i`, which `e` injective rules out.
  have h_not_inj : ¬Injective (cons (κ j) e : Fin (n + 1) → ℤ) := by
    rw [← show κ ∘ l = e from funext hl, ← comp_cons]
    exact fun h_inj ↦ h_ne (h_inj hκ_eq)
  simpa [cons_injective_iff, he_inj] using h_not_inj

/-- Let `Q` be an invertible matrix over `k`, let `φ` send a matrix `M` over `K` to `Q * M * Q⁻¹`
over `k`, and let the `K`-subspace `V` contain every diagonal matrix. Then the matrices `φ x`,
`x ∈ V`, do not all have entry `0` at `(a, b)` and equal entries at `(a, a)` and `(b, b)`: for the
diagonal units `Eₜₜ` this would make each `Q a t * Q⁻¹ t a` zero, while their sum over `t` is
`1`. -/
private lemma not_forall_conj_entries_of_diagonal_mem (Q : GL N k)
    {φ : Matrix N N K →ₐ[K] Matrix N N k}
    (hφ : ∀ M : Matrix N N K,
      φ M = (Q : Matrix N N k) * (M.map (algebraMap K k) * (Q : Matrix N N k)⁻¹))
    {V : Submodule K (Matrix N N K)} (h_diag : ∀ v : N → K, diagonal v ∈ V) (a b : N) :
    ¬∀ x ∈ V, φ x a b = 0 ∧ φ x a a = φ x b b := by
  intro h_block
  have h_unit (t : N) : Q a t * (Q : Matrix N N k)⁻¹ t a = 0 := by
    obtain ⟨h_off, h_diag_eq⟩ := h_block (diagonal (Pi.single t 1)) (h_diag (Pi.single t 1))
    have h_off' : (Q : Matrix N N k) a t = 0 ∨ (Q : Matrix N N k)⁻¹ t b = 0 := by
      simpa [hφ, Matrix.mul_apply, diagonal, apply_ite, Pi.single_apply] using h_off
    have h_diag' : (Q : Matrix N N k) a t * (Q : Matrix N N k)⁻¹ t a =
        (Q : Matrix N N k) b t * (Q : Matrix N N k)⁻¹ t b := by
      simpa [hφ, Matrix.mul_apply, diagonal, apply_ite, Pi.single_apply] using h_diag_eq
    rcases h_off' with h_Q | h_Qinv
    · rw [h_Q, zero_mul]
    · rw [h_diag', h_Qinv, mul_zero]
  simpa [Matrix.mul_apply, h_unit] using congrFun₂ Q.val_inv a a

/-- Let `E` be a number field inside `Ω` (`EmbeddedNumberField E`), and let `p` be a property of the
elements of `Gal(Ω/E)`. If every nonempty open set `V` contains a nonempty open set on which `p`
holds, then `p` holds at the Frobenius elements of most Frobenius data. -/
private lemma eventually_mostFrobenii_of_open {E : Type} [Field E] [EmbeddedNumberField E]
    {p : Gal(Ω/E) → Prop}
    (h : ∀ V : Set Gal(Ω/E), IsOpen V → V.Nonempty →
      ∃ O ⊆ V, IsOpen O ∧ O.Nonempty ∧ ∀ g ∈ O, p g) :
    ∀ᶠ y : FrobeniusDatum E in mostFrobenii E, p y.frob := by
  intro V hV hV_ne
  obtain ⟨O, hOV, hO, hO_ne, h_O⟩ := h V hV hV_ne
  refine ⟨O, hOV, hO, hO_ne, .of_forall ?_⟩
  rintro - - s - - - hs_O
  exact h_O s hs_O

/-- Let `e : Fin n → ℤ` be injective and let every `e i` be a value of `κ : N → ℤ`. If all minors
of order `n + 1` of the powers of `diagonal (T ∘ κ)` vanish, then `κ = e ∘ c` for an onto `c`. -/
private lemma exists_surjective_comp_eq_of_powMinor_diagonal_eq_zero (he_inj : e.Injective)
    {κ : N → ℤ} (hκ : ∀ i : Fin n, e i ∈ Set.range κ)
    (h_minor : ∀ a : Fin (n + 1) → N × N,
      powMinor (diagonal (T ∘ κ) : Matrix N N k[T;T⁻¹]) (n + 1) a = 0) :
    ∃ c : N → Fin n, Surjective c ∧ e ∘ c = κ := by
  choose l hl using hκ
  choose c hc using exists_eq_of_powMinor_diagonal_eq_zero he_inj hl h_minor
  exact ⟨c, fun i ↦ ⟨l i, he_inj ((hc (l i)).trans (hl i))⟩, funext hc⟩

/-- Let `E` be a number field inside `Ω`, a fixed algebraic closure of `ℚ`, let `r` be a continuous
representation of `Gal(Ω/E)` on `K ^ N`, and let `k` be a normed field over `K`. Suppose:
* the span of the image of `r` contains every diagonal matrix;
* for most Frobenius data `v` (the filter `mostFrobenii E`) the polynomial `P v` is monic of degree
  `n ≥ 1` and kills `r v.frob`;
* the free integers `e i` (`HasNoSmallRelations e`: distinct exponent vectors of one total degree at
  most `(n + 1) ^ 2` have distinct weights) all occur among the integers `κ j`;
* for an invertible matrix `Q` over `k`, every polynomial in the entries that vanishes at `Q * r g`
  for all `g` near `1` also vanishes at `diagonal (T ∘ κ) * Q` over `k[T;T⁻¹]`.

Then `N` has `n` elements and `P v` is the characteristic polynomial of `r v.frob` for most
Frobenius data `v`. -/
lemma card_eq_and_charpoly_eq [NeZero n] {E : Type} [Field E] [NumberField E] [Algebra E Ω]
    (r : Gal(Ω/E) →* GL N K) (hr : Continuous r)
    (h_span : ∀ v : N → K, diagonal v ∈ span K (Set.range fun g : Gal(Ω/E) ↦ (r g : Matrix N N K)))
    {P : FrobeniusDatum E → K[X]}
    (hP : ∀ᶠ v : FrobeniusDatum E in mostFrobenii E,
      (P v).aeval (r v.frob : Matrix N N K) = 0 ∧ (P v).IsMonicOfDegree n)
    (Q : GL N k) (κ : N → ℤ) (he : HasNoSmallRelations e) (hκ : ∀ i : Fin n, e i ∈ Set.range κ)
    (h_torus : ∀ h : MvPolynomial (N × N) k,
      (∀ᶠ g : Gal(Ω/E) in nhds 1,
        h.aeval ((Q : Matrix N N k) * (r g : Matrix N N K).map (algebraMap K k)).uncurry = 0) →
      h.aeval (diagonal (T ∘ κ) * (Q : Matrix N N k).map LaurentPolynomial.C).uncurry = 0) :
    Fintype.card N = n ∧
      ∀ᶠ v : FrobeniusDatum E in mostFrobenii E, (r v.frob : Matrix N N K).charpoly = P v := by
  -- Work with the conjugate `φ (r g) = Q * r g * Q⁻¹` over `k` and the minors of its powers.
  let φ : Matrix N N K →ₐ[K] Matrix N N k :=
    (MulSemiringAction.toAlgHom K (Matrix N N k) (toConjAct Q)).comp (ofId K k).mapMatrix
  have h_φ (M : Matrix N N K) :
      φ M = (Q : Matrix N N k) * (M.map (algebraMap K k) * (Q : Matrix N N k)⁻¹) := by
    simp [φ, units_smul_def, mul_assoc, ofId]
  let ρ (g : Gal(Ω/E)) : GL N k := Units.map φ (r g)
  have h_closed (m : ℕ) : IsClosed {g : Gal(Ω/E) | powMinor (φ (r g)) m = 0} := by
    refine isClosed_eq ?_ continuous_zero
    simp only [h_φ]
    fun_prop [flip]
  -- Minors that vanish near `x` vanish on the translate of the torus: apply `h_torus` to the
  -- polynomial `Y ↦ powMinor (Y * Q⁻¹ * ρ x) m a`.
  have h_near {m : ℕ} (x : Gal(Ω/E)) (h : ∀ᶠ g : Gal(Ω/E) in nhds x, powMinor (φ (r g)) m = 0)
      (a : Fin m → N × N) :
      powMinor (diagonal (T ∘ κ) * (ρ x : Matrix N N k).map LaurentPolynomial.C) m a = 0 := by
    set M : Matrix N N (MvPolynomial (N × N) k) :=
      mvPolynomialX N N k * ((Q⁻¹ * ρ x : GL N k) : Matrix N N k).map MvPolynomial.C
    rw [← map_mul_right_nhds_one x, eventually_map] at h
    have h_poly : (powMinor M m a).aeval
        (diagonal (T ∘ κ) * (Q : Matrix N N k).map LaurentPolynomial.C).uncurry = 0 :=
      h_torus (powMinor M m a) <| h.mono fun g hg ↦ by
        have h_eval (A : Matrix N N k) :
            (mvPolynomialX N N k).map (MvPolynomial.eval A.uncurry) = A :=
          mvPolynomialX_map_eval₂ (RingHom.id k) A
        simpa [M, φ, ρ, h_eval, units_smul_def, mul_assoc, ofId, comp_def] using congrFun hg a
    simp only [M, map_powMinor, AlgHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_map, comp_def,
      MvPolynomial.aeval_C] at h_poly
    let B := diagonal (T ∘ κ) * (Q : Matrix N N k).map LaurentPolynomial.C
    have h_eval : (mvPolynomialX N N k).map (MvPolynomial.aeval B.uncurry) = B :=
      mvPolynomialX_map_eval₂ (algebraMap k k[T;T⁻¹]) B
    let C := ((Q⁻¹ * ρ x : GL N k) : Matrix N N k).map LaurentPolynomial.C
    have h_minor : powMinor (B * C) m a = 0 :=
      (congrArg (fun X ↦ powMinor (X * C) m a) h_eval).symm.trans h_poly
    simpa [B, C, mul_assoc, ← Matrix.map_mul] using h_minor
  -- The minors of order `n + 1` vanish at most Frobenius elements, hence everywhere.
  have h_all (g : Gal(Ω/E)) : powMinor (φ (r g)) (n + 1) = 0 := by
    refine (h_closed (n + 1)).closure_subset (dense_of_mostFrobenii (hP.mono ?_) g)
    intro v ⟨h_root, h_monic⟩
    have h_deg : (P v).natDegree < n + 1 := by simp [h_monic.natDegree_eq]
    exact powMinor_eq_zero_of_aeval_eq_zero φ h_monic.ne_zero h_root h_deg
  have h_top (x : Gal(Ω/E)) : ∀ a : Fin (n + 1) → N × N,
      powMinor (diagonal (T ∘ κ) * (ρ x : Matrix N N k).map LaurentPolynomial.C) (n + 1) a = 0 :=
    h_near x (.of_forall h_all)
  -- The weights `κ` are exactly the `e i`: write `κ = e ∘ c` with `c` onto.
  obtain ⟨c, hc_surj, rfl⟩ := exists_surjective_comp_eq_of_powMinor_diagonal_eq_zero
    (HasNoSmallRelations.injective he) hκ fun a ↦ by simpa [ρ] using h_top 1 a
  -- If `c a = c b` with `a ≠ b`, then by
  -- `HasNoSmallRelations.inv_apply_eq_zero_and_eq_of_powMinor_eq_zero` all `φ (r g)`, and so all
  -- elements of their span, have entry `0` at `(a, b)` and equal entries at `(a, a)`, `(b, b)`.
  have hc_inj : Injective c := by
    intro a b hab
    by_contra hne
    refine not_forall_conj_entries_of_diagonal_mem Q h_φ h_span a b fun x hx ↦ ?_
    refine span_induction (p := fun x _ ↦ φ x a b = 0 ∧ φ x a a = φ x b b) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨g, rfl⟩
      simpa [ρ] using
        he.inv_apply_eq_zero_and_eq_of_powMinor_eq_zero hc_surj le_rfl (h_top g⁻¹) hab hne
    all_goals simp +contextual
  have hN : card N = n := by simpa using card_of_bijective ⟨hc_inj, hc_surj⟩
  -- The minors of order `n` do not all vanish on a nonempty open set `V`, since
  -- `HasNoSmallRelations.lt_of_powMinor_eq_zero` would give `n < n`; so `V` meets the open set
  -- where they do not.
  have h_most : ∀ᶠ v : FrobeniusDatum E in mostFrobenii E, powMinor (φ (r v.frob)) n ≠ 0 := by
    refine eventually_mostFrobenii_of_open (p := fun g ↦ powMinor (φ (r g)) n ≠ 0) ?_
    rintro V hV ⟨x, hx⟩
    set Z : Set Gal(Ω/E) := {g | powMinor (φ (r g)) n = 0}
    have hV_not_sub : ¬V ⊆ Z := fun h_sub ↦ lt_irrefl n <| he.lt_of_powMinor_eq_zero hc_surj
      n.le_succ (h_near x (mem_nhds_iff.mpr ⟨V, h_sub, hV, hx⟩))
    exact ⟨V \ Z, Set.sdiff_subset, hV.sdiff (h_closed n), Set.sdiff_nonempty.mpr hV_not_sub,
      fun _ ⟨_, hg_Z⟩ ↦ hg_Z⟩
  refine ⟨hN, ?_⟩
  filter_upwards [hP, h_most] with v ⟨h_root, h_monic⟩ hv
  exact charpoly_eq_of_powMinor_ne_zero φ hN h_root h_monic hv

end New
end
end

section
/-!
# Cuspidal types, multiplicity-free sums and the Hodge–Tate cocharacter

The file proves four results on unitary groups and Galois representations. Here `O_w` is the ring of
integers at a place `w` of `E` with uniformiser `ϖ`, and `χ` is the cyclotomic character.

## Main definitions and results

* `New.Variety.exists_isCuspidalType`: a character of `1 + ϖ M_N(O_w)`, trivial on
  `1 + ϖ² M_N(O_w)`, that is nontrivial on every unipotent radical. It is
  `k ↦ exp (2πi u (tr (b (k - 1))))` for an integral matrix `b` with irreducible characteristic
  polynomial modulo `w` and an additive character `u : E_w / ϖ² → ℚ/ℤ` with `u ϖ ≠ 0`.
* `New.Variety.exists_levelGU_invTransposeGL_le`: an open subgroup that contains the integral points
  trivial at a finite set `S` of places contains a principal level `𝔑` (up to inverse transpose).
  The primes of `𝔑` are those of a given `N` and of a set `B` meeting each pair `w, w̄` of `S`.
* `New.GaloisRep.exists_rep_span_diagonal`: Galois representations `ρ τ`, one for each embedding `τ`
  of `E` in `ℂ`, combine into one representation `r`. This `r` is multiplicity free (the span of its
  image contains the diagonal matrices) and has the prescribed integers among its Hodge–Tate jumps
  at every `τ`. It is built from the semisimplification of the sum of the `ρ τ`, keeping each
  irreducible constituent once.
* `New.Period.aeval_cocharacter_eq_zero`: let `x i ∈ ℂ_p` and integers `κ i` be given. A polynomial
  over `ℂ_p` that vanishes at `(χ(g) ^ (-κ i) g(x i))_i` for all `g ∈ G_p` near `1` also vanishes at
  `(T ^ (κ i) x i)_i`, with `T` the variable of the Laurent polynomials over `ℂ_p`.

Notions from other files:
* `New.localCongruence n w m`: the subgroup of `GL_n(E_w)` of integral matrices congruent to `1`
  modulo `ϖ ^ (m + 1)`; so `m = 0` gives `1 + ϖ M_n(O_w)` and `m = 1` gives `1 + ϖ² M_n(O_w)`.
* `New.stdLevel E n`: the integral points of the finite adelic unitary group, the stabiliser of
  `Ô ^ n`.
* `New.Variety.IsCuspidalType`: for every idempotent matrix ε ≠ 0, 1, the character is nontrivial on
  the elements of its group that lie in 1 + εM_n(1 − ε).
* `New.Variety.levelGU`: the principal level K(𝔑), the similitudes in `GL_n(Ô E)` that are congruent
  to `1` modulo `𝔑`.
* `New.Gf`: The finite adelic unitary group G_f: matrices g in GL_n(𝔸_f) with gᴴg = 1;
  `New.Gf.trivialOn n S` is the subgroup of elements with component 1 at every place of `S`.
* `New.Period.hodgeTateMaps`: The γ-semilinear maps f : T → ℂ_ℓ with f(gx) = χ(g)^(−u)·g f(x) for g
  near 1; their dimension is the multiplicity `New.Period.jump` of the jump u at γ.

## Relation to the literature

Known result: The Hodge-Tate cocharacter lies in the algebraic monodromy group. It is stated on
coordinates in C_p as the fact that a polynomial that vanishes at the cyclotomically twisted Galois
translates of a point, near the identity, vanishes along the one-parameter torus. No algebraic
groups or Tannakian categories are used. Source: Serre, Groupes algébriques associés aux modules de
Hodge-Tate, Astérisque 65 (1979), §1; Sen, Ann. of Math. 97 (1973).

See also `Lib.GaloisRep.WeightCongruence`, `Lib.Adelic.Unitary.CongruenceLevels` and
`Lib.GaloisRep.Main.OddRank`.
-/

@[expose] public section

/-! ## Existence of a cuspidal type and of a principal level -/

namespace New.Variety

open Matrix IsLocalRing Valued Gf FiniteField IsDedekindDomain.HeightOneSpectrum QuotientAddGroup QZ
  Polynomial Ideal Fintype IsPrime NumberField

variable {E n : Type} [Field E] [NumberField E] [Fintype n] [DecidableEq n] (w : FinPlace E)

/-- Some `N × N` matrix over `LocInt w` (the integers `O_w` of the completion `LocField w = E_w`)
has irreducible characteristic polynomial modulo `w`: lift the matrix of multiplication by a
generator of the extension of degree `N` of the residue field. -/
lemma exists_irreducible_charpoly_residue (N : ℕ) [NeZero N] :
    ∃ b : Matrix (Fin N) (Fin N) (LocInt w), Irreducible (b.map (residue (LocInt w))).charpoly := by
  have h_char_prime : Fact (ringChar (ResField w)).Prime := ⟨CharP.prime_ringChar (ResField w)⟩
  let basis : PowerBasis (ResField w) (Extension (ResField w) (ringChar (ResField w)) N) :=
    Field.powerBasisOfFiniteOfSeparable (ResField w)
      (Extension (ResField w) (ringChar (ResField w)) N)
  rw [← show basis.dim = N from basis.finrank.symm.trans (finrank_extension ..)]
  -- Lift the matrix of multiplication by the generator entry by entry.
  obtain ⟨b, hb⟩ : ∃ b : Matrix (Fin basis.dim) (Fin basis.dim) (LocInt w),
      b.map (residue (LocInt w)) = Algebra.leftMulMatrix basis.basis basis.gen :=
    residue_surjective.comp_left.comp_left _
  refine ⟨b, ?_⟩
  rw [hb, charpoly_leftMulMatrix basis]
  exact minpoly.irreducible basis.isIntegral_gen

/-- A matrix with irreducible characteristic polynomial is not block triangular: if `p` holds for
some indices but not for all, some entry in a row with `p` and a column without `p` is nonzero. -/
lemma exists_ne_zero_of_irreducible_charpoly {F : Type*} [Field F] {A : Matrix n n F}
    (hA : Irreducible A.charpoly) {p : n → Prop} (h₁ : ∃ j : n, p j) (h₂ : ∃ i : n, ¬p i) :
    ∃ j i : n, p j ∧ ¬p i ∧ A j i ≠ 0 := by
  classical
  let := Prop.linearOrder
  by_contra! h_zero
  have h_block : A.BlockTriangular p := by
    -- On `Prop`, `p i' < p j'` says that `p j'` holds and `p i'` does not.
    intro j' i' (h_lt : p i' < p j')
    obtain ⟨hj', hi'⟩ : p j' ∧ ¬p i' := Classical.not_imp.mp h_lt.not_ge
    exact h_zero j' i' hj' hi'
  -- The characteristic polynomial factors along the two blocks, and neither block is empty.
  -- `h_factor`: `det (charmatrix A)` is the product of the determinants of its blocks on and off
  -- `p`. Untyped: a written type gets other decidability instances than `det_fintype`.
  have h_factor := h_block.charmatrix.det_fintype.trans (Fintype.prod_Prop _)
  -- A block with at least one row has a characteristic polynomial of positive degree, not a unit.
  rcases hA.isUnit_or_isUnit h_factor with h_unit | h_unit <;>
    simp_all [← charmatrix_toSquareBlock, ← charpoly.eq_1, card_subtype, isUnit_iff_degree_eq_zero]

/-- Let `b` be an integral `N × N` matrix whose characteristic polynomial modulo `w` is
irreducible, and let `u` be an additive map from `E_w / ϖ² O_w` to `QZ = ℚ/ℤ` with `u a ≠ 0` for
some `a` whose valuation `v a` is `exp (-1)`. Then for every idempotent matrix `ε ≠ 0, 1` over
`E_w`, some `k` in `1 + ϖ M_N(O_w)` has the form `1 + ε Y (1 - ε)` and satisfies
`u (tr (b (k - 1))) ≠ 0`. -/
lemma exists_eq_one_add_mul_mul_and_map_trace_ne_zero (N : ℕ) {a : LocField w}
    (ha : v a = .exp (-1)) {b : Matrix (Fin N) (Fin N) (LocInt w)}
    (hb : Irreducible (b.map (residue (LocInt w))).charpoly)
    {u : LocField w ⧸ v.leAddSubgroup (.exp (-2)) →+ QZ} (hu : u a ≠ 0)
    {ε : Matrix (Fin N) (Fin N) (LocField w)} (h_idem : IsIdempotentElem ε) (hε₀ : ε ≠ 0)
    (hε₁ : ε ≠ 1) :
    ∃ (k : localCongruence (Fin N) w 0) (Y : Matrix (Fin N) (Fin N) (LocField w)),
      1 + ε * Y * (1 - ε) = (k : GL (Fin N) (LocField w)).val ∧
      u (b.map Subtype.val * ((k : GL (Fin N) (LocField w)).val - 1)).trace ≠ 0 := by
  -- Smith normal form `ε = K * diagonal d * q`, with `K` the image of an integral `k`.
  obtain ⟨K, ⟨k, hk⟩, q, -, d, rfl⟩ : ∃ K ∈ intGL (Fin N) (LocInt w).toSubring,
      ∃ q ∈ intGL (Fin N) (LocInt w).toSubring, ∃ d : Fin N → LocField w,
        ε = K.val * diagonal d * q.val :=
    (isValuationPair_valuationSubring (LocInt w)).smith_normal_form ε
  rw [charpoly_map, ← charpoly_units_conj' k, ← charpoly_map] at hb
  -- As `ε ≠ 0, 1`, some but not all `d i` vanish (an idempotent unit is `1`), so `k⁻¹ b k` has a
  -- unit entry across the blocks.
  have h_some : ∃ j : Fin N, d j = 0 := by
    by_contra! h_ne
    simp_all [Pi.isUnit_iff, IsIdempotentElem.iff_eq_one_of_isUnit]
  obtain ⟨j, i, hj, hi, h_entry_ne⟩ := exists_ne_zero_of_irreducible_charpoly hb h_some <| by
    by_contra! h_eq
    simp_all [funext h_eq]
  have h_unit_val : v ((k⁻¹ * b * k) j i : LocField w) = 1 := by
    simpa [adicCompletionIntegers.isUnit_iff_valued_eq_one] using h_entry_ne
  -- Write `a = (k⁻¹ b k) j i * d i * t` in the field `LocField w`; then `d i * t` has the
  -- valuation of `a`. The test element is `K (1 + single i j (d i * t)) K⁻¹`, where the
  -- trace is `a`.
  have h_entry_val_ne : ((k⁻¹ * b * k) j i : LocField w) ≠ 0 :=
    v.ne_zero_iff.mp (ne_of_eq_of_ne h_unit_val one_ne_zero)
  obtain ⟨t, rfl⟩ : ∃ t : LocField w, a = (k⁻¹ * b * k) j i * d i * t :=
    ⟨_, (mul_inv_cancel_left₀ (mul_ne_zero h_entry_val_ne hi) a).symm⟩
  have h_ne : i ≠ j := ne_of_apply_ne d fun h ↦ hi (h.trans hj)
  have h_dt_val : v (d i * t) = .exp (-1) := by
    rwa [mul_assoc, map_mul, h_unit_val, one_mul] at ha
  have h_dt_int : d i * t ∈ v.integer := by simp +decide [v.mem_integer_iff, h_dt_val]
  have h_transv_mem : transvectionGL h_ne (d i * t) ∈ localCongruence (Fin N) w 0 := by
    refine ⟨transvectionGL_mem_intGL h_ne h_dt_int, fun i' j' ↦ ?_⟩
    aesop (add simp [transvection, single_apply])
  obtain ⟨h_int', h_red⟩ := mem_localCongruence_zero.mp h_transv_mem
  have h_conj : K * transvectionGL h_ne (d i * t) * K⁻¹ ∈ localCongruence (Fin N) w 0 :=
    mem_localCongruence_zero.mpr ⟨_, reduceGL.normal_ker.conj_mem _ h_red ⟨K, k, hk⟩⟩
  let s : Matrix (Fin N) (Fin N) (LocField w) := Matrix.single i j t
  have hs_mul_diag : s * diagonal d = 0 := by aesop (add simp single_apply)
  have hs_single : Matrix.single i j (d i * t) = diagonal d * s := by aesop (add simp single_apply)
  -- With `Y = q⁻¹ * s * K⁻¹` one has `ε * Y * (1 - ε) = K * (diagonal d * s) * K⁻¹`, as
  -- `s * diagonal d = 0`.
  refine ⟨⟨_, h_conj⟩, q⁻¹ * s * K⁻¹, ?_, ?_⟩
  · simp [mul_add, add_mul, mul_sub, mul_assoc, ← s.mul_assoc, -coe_units_inv, hs_mul_diag,
      hs_single, transvection]
  · -- At the test element `k - 1 = K * (diagonal d * s) * K⁻¹`, and the trace against `b` is `a`.
    suffices h_ne_zero : u (b.map Subtype.val * (K.val * (diagonal d * (s * K⁻¹.val)))).trace ≠ 0 by
      simpa [mul_add, add_mul, mul_assoc, -coe_units_inv, hs_mul_diag, hs_single, transvection]
        using h_ne_zero
    have h_trace : (b.map Subtype.val * (K.val * (diagonal d * (s * K⁻¹.val)))).trace =
        (k⁻¹ * b * k) j i * d i * t := by
      simp [s, ← hk, ← mul_assoc, trace_mul_cycle _ s, trace_mul_single, Matrix.mul_apply,
        ← map_inv, diagonal]
    rwa [h_trace]

/-- For N ≥ 1 and a finite place w, some character of 1 + ϖM_N(O_w) is nontrivial on every
unipotent radical (`New.Variety.IsCuspidalType`) and trivial on 1 + ϖ²M_N(O_w). -/
lemma exists_isCuspidalType (N : ℕ) [NeZero N] :
    ∃ θ : localCongruence (Fin N) w 0 →* ℂ,
      IsCuspidalType (localCongruence (Fin N) w 0) θ ∧
      ∀ k : localCongruence (Fin N) w 0, k.val ∈ localCongruence (Fin N) w 1 → θ k = 1 := by
  -- Put `θ k = expUnit (u (tr (b (k - 1))))`, where `b` is integral with irreducible characteristic
  -- polynomial modulo `w`, and `u` is an additive character of `E_w / ϖ²` nontrivial at `a = ϖ`.
  obtain ⟨a, ha⟩ : ∃ a : LocField w, v a = .exp (-1) := ⟨_, v_uniformizer w⟩
  obtain ⟨b, hb⟩ := exists_irreducible_charpoly_residue w N
  -- `a` is not in `ϖ² O_w`, so some additive character of `E_w / ϖ²` does not vanish at `a`.
  obtain ⟨u, hu⟩ : ∃ u : LocField w ⧸ v.leAddSubgroup (.exp (-2)) →+ QZ, u a ≠ 0 := by
    have h_a_ne : (a : LocField w ⧸ v.leAddSubgroup (.exp (-2))) ≠ 0 := by simp -dsimp +decide [ha]
    by_contra! h_zero
    exact h_a_ne (eq_zero_of_forall_hom_eq_zero h_zero)
  -- `u` kills the trace of `b * Z` when every entry of `Z` lies in `ϖ² O_w`.
  have h_small {Z : Matrix (Fin N) (Fin N) (LocField w)}
      (hZ : ∀ i j : Fin N, v (Z i j) ≤ .exp (-2)) : u (b.map Subtype.val * Z).trace = 0 := by
    have h_mem : (b.map Subtype.val * Z).trace ∈ v.leAddSubgroup (.exp (-2)) :=
      sum_mem fun i _ ↦ (v_matrix_mul_le (fun i j ↦ (b i j).prop) hZ i i).trans_eq (one_mul _)
    rw [(eq_zero_iff _).2 h_mem, map_zero]
  -- `mat k` is the matrix of `k`.
  let mat (k : localCongruence (Fin N) w 0) : Matrix (Fin N) (Fin N) (LocField w) :=
    (k : GL (Fin N) (LocField w))
  refine ⟨(Units.coeHom ℂ).comp (expUnit.comp
      (.mk' (fun k ↦ .ofAdd (u (b.map Subtype.val * (mat k - 1)).trace)) fun x y ↦ ?_)),
    fun ε h_idem hε₀ hε₁ ↦ ?_, fun k hk ↦ ?_⟩
  · -- Multiplicativity: `xy - 1 = (x - 1) + (y - 1) + (x - 1)(y - 1)`, the last term being `O(ϖ²)`.
    have hx : ∀ i j : Fin N, v ((mat x - 1) i j) ≤ .exp (-1) := x.prop.right
    have hy : ∀ i j : Fin N, v ((mat y - 1) i j) ≤ .exp (-1) := y.prop.right
    have h_xy : mat (x * y) - 1 = (mat x - 1) + (mat y - 1) + (mat x - 1) * (mat y - 1) := by
      simp only [mat, Subgroup.coe_mul, Units.val_mul]
      noncomm_ring
    have h_cross : u (b.map Subtype.val * ((mat x - 1) * (mat y - 1))).trace = 0 :=
      h_small (v_matrix_mul_le hx hy)
    simp only [h_xy, mul_add, trace_add, mk_add, map_add, h_cross, add_zero, ofAdd_add]
  · -- Cuspidality: the test element for `ε` has `θ ≠ 1`.
    obtain ⟨k, Y, hY, h_trace_ne⟩ :=
      exists_eq_one_add_mul_mul_and_map_trace_ne_zero w N ha hb hu h_idem hε₀ hε₁
    exact ⟨k, Y, hY, by simpa [expUnit_eq_one_iff] using h_trace_ne⟩
  · -- On `1 + ϖ² M_N(O_w)` the entries of `k - 1` lie in `ϖ² O_w`, so the trace term vanishes.
    have hk_entries : ∀ i j : Fin N, v ((mat k - 1) i j) ≤ .exp (-2) := hk.right
    simpa [expUnit_eq_one_iff] using h_small hk_entries

/-- Let `H` be an open subgroup of the finite adelic unitary group `Gf E n` that contains every
element of `stdLevel E n` (the stabiliser of the standard lattice) that is trivial at each place of
`S`, and suppose each `w ∈ S` has `w` or its conjugate in `B`. Then for every `N : 𝓞 E` there is a
multiple `𝔑` of `N` that (a) lies in exactly the primes that contain `N` or belong to `B`, and (b)
satisfies `u ∈ H` whenever the inverse transpose of `u` lies in `levelGU n 𝔑`, the group of
similitudes in `GL_n(Ô E)` congruent to `1` modulo `𝔑`. -/
lemma exists_levelGU_invTransposeGL_le [IsCMField E] {H : Subgroup (Gf E n)} (hH : H.IsOpen)
    {S B : Finset (FinPlace E)} (hS : stdLevel E n ⊓ trivialOn n S ≤ H)
    (hB : ∀ w ∈ S, w ∈ B ∨ star w ∈ B) (N : 𝓞 E) :
    ∃ 𝔑 : 𝓞 E,
      N ∣ 𝔑 ∧
      (∀ w : FinPlace E, 𝔑 ∈ w.asIdeal ↔ N ∈ w.asIdeal ∨ w ∈ B) ∧
      ∀ u : Gf E n, invTransposeGL u.val ∈ levelGU n 𝔑 → u ∈ H := by
  -- By compactness there are exponents `k w` such that an integral point lying in
  -- `localCongruence n w (k w)` at every `w ∈ B` belongs to `H`: the compact image of
  -- `stdLevel ∖ H` in the components at `B` misses `1`, hence misses a box of neighbourhoods of
  -- `1`.
  obtain ⟨k, hk⟩ :
      ∃ k : B → ℕ, ∀ g ∈ stdLevel E n,
        (∀ w : B, g.atPlace w.val ∈ localCongruence n w.val (k w)) → g ∈ H := by
    let comp (g : Gf E n) (w : B) : GL n (LocField w.val) := g.atPlace w
    have h_closed : IsClosed (comp '' (stdLevel E n \ H)) :=
      ((isCompact_stdLevel.diff hH).image
        (continuous_pi fun w : B ↦ continuous_atPlace w.val)).isClosed
    -- An integral point that is `1` at every place of `B` is `1` at every place of `S`, since `w`
    -- or `star w` lies in `B`; so it lies in `stdLevel E n ⊓ trivialOn n S ≤ H`.
    have h_one : 1 ∉ comp '' (stdLevel E n \ H) := by
      rintro ⟨g, ⟨hg_int, hg_not⟩, hg_one⟩
      have hg_B (w : FinPlace E) (hw : w ∈ B) : g.atPlace w = 1 := congrFun hg_one ⟨w, hw⟩
      refine hg_not (hS ⟨hg_int, ?_⟩)
      suffices hg_S : ∀ w ∈ S, g.atPlace w = 1 by simpa [trivialOn] using hg_S
      intro w hw
      rcases hB w hw with hw_B | hw_star
      · exact hg_B w hw_B
      · grind [atPlace_star_eq_one_iff]
    obtain ⟨t, ht, h_box⟩ : ∃ t : (w : B) → Set (GL n (LocField w.val)),
        (∀ w : B, IsOpen (t w) ∧ (1 : (w : B) → GL n (LocField w.val)) w ∈ t w) ∧
        Set.univ.pi t ⊆ (comp '' (stdLevel E n \ H))ᶜ :=
      isOpen_pi_iff'.mp h_closed.isOpen_compl 1 h_one
    have h_exists_k (w : B) :
        ∃ m : ℕ, (localCongruence n w.val m : Set (GL n (LocField w.val))) ⊆ t w :=
      (eventually_localCongruence_subset ((ht w).1.mem_nhds (ht w).2)).exists
    choose k hk using h_exists_k
    refine ⟨k, fun g hg h_near ↦ ?_⟩
    by_contra hg_not
    exact h_box (fun w _ ↦ hk w (h_near w)) ⟨g, ⟨hg, hg_not⟩, rfl⟩
  -- A positive power of `∏ w ^ (k w + 1)` is principal, generated by `y`; take `𝔑 = N * y`.
  obtain ⟨m, hm, y, hy⟩ :
      ∃ m ≠ 0, ∃ y : 𝓞 E, (∏ w : B, w.val.asIdeal ^ (k w + 1)) ^ m = span {y} :=
    exists_ideal_pow_eq_span_singleton _
  have hy_mem (w : FinPlace E) : y ∈ w.asIdeal ↔ w ∈ B := by
    simp [← span_singleton_le_iff_mem, ← hy, prod_le, pow_le_iff, hm,
      IsMaximal.out.le_iff_eq ne_top', asIdeal_injective.eq_iff]
  have hy_val (w : B) : v (algebraMap E (LocField w.val) y) ≤ .exp (-(k w).succ) := by
    rw [v_algebraMap_eq_intValuation, intValuation_le_pow_iff_dvd, ← hy]
    exact (Finset.dvd_prod_of_mem (fun w' : B ↦ w'.val.asIdeal ^ (k w' + 1))
      (Finset.mem_univ w)).pow hm
  refine ⟨N * y, dvd_mul_right N y, fun w ↦ ?_, ?_⟩
  · -- The primes of `N * y` are those of `N` and those of `y`.
    simp [mul_mem_iff_mem_or_mem, hy_mem]
  · -- `invTransposeGL u` is the transpose of `u⁻¹`, so we show `u⁻¹ ∈ H`.
    intro u hu
    obtain ⟨-, hu_int, hu_cong⟩ : invTransposeGL u.val ∈ GU E n ∧ u.val ∈ intGL n (Ô E) ∧
        ∀ (i j : n) (w : FinPlace E),
          v ((invTransposeGL u.val).val i j w - (if i = j then (1 : 𝔸f E) else 0) w) ≤
            v (algebraMap (𝓞 E) (𝔸f E) N w) * v (algebraMap (𝓞 E) (𝔸f E) y w) := by
      simpa [levelGU, congruenceGL, Subgroup.ofDiv, Matrix.one_apply, exists_eq_mul_iff_v_le]
        using hu
    have h_int : u⁻¹ ∈ stdLevel E n := inv_mem (show u ∈ stdLevel E n from hu_int)
    refine inv_mem_iff.mp (hk _ h_int fun w ↦ ⟨mem_stdLevel_iff.mp h_int w, fun i j ↦ ?_⟩)
    calc v (((u⁻¹.atPlace w).val - 1) i j)
      _ ≤ v (algebraMap E (LocField w.val) N) * v (algebraMap E (LocField w.val) y) := by
        -- the entry of `u⁻¹` at `w` is that of `(u at w)⁻¹` only after unfolding `atPlace`
        simpa [← evalAt_apply, eq_comm, -coe_units_inv] using! hu_cong j i w
      _ ≤ .exp (-(k w).succ) := mul_le_of_le_one_of_le (coe_algebraMap_mem ..) (hy_val w)

end New.Variety

/-!
## Multiplicity-free sums of irreducible constituents with all jumps

`New.GaloisRep.IsSphericalAbove r R J w P` says three things at every place over `w`. The
representation `r` is unramified (crystalline above `ℓ`). `R` relates the multiplicity of each
integer in `J τ` to its multiplicity as a jump at `τ`. `P` kills geometric Frobenius. With
`R = OccursIn` the middle condition reads: every element of `J τ` occurs as a jump.
-/

section MultiplicityFreeSum

open Matrix New Period Metric Filter Submodule Polynomial

/-- Let `f` and `f'` be algebra maps from a product of matrix algebras `∏ M_{d i}(k)` to matrix
algebras, with `k` algebraically closed of characteristic `0`. If `f` kills no block unit
`piMatrixUnit i` (the matrix unit `E₀₀` in factor `i`, zero in the other factors) and every
`f' (piMatrixUnit i)` has trace `1`, then `f'` is a retract of `f`: some `B` with a left inverse `C`
satisfies `f z * B = B * f' z` for all `z`. -/
lemma New.exists_retract_of_trace_map_piMatrixUnit_eq_one {k N n : Type} [Field k] [CharZero k]
    [Fintype N] [DecidableEq N] [Fintype n] [DecidableEq n] {b : ℕ}
    {d : Fin b → ℕ} [∀ i : Fin b, NeZero (d i)] (f : PiMatrix k d →ₐ[k] Matrix N N k)
    (f' : PiMatrix k d →ₐ[k] Matrix n n k) (f_ne : ∀ i : Fin b, f (piMatrixUnit i) ≠ 0)
    (f'_trace : ∀ i : Fin b, (f' (piMatrixUnit i)).trace = 1) :
    ∃ (B : Matrix N n k) (C : Matrix n N k), C * B = 1 ∧ ∀ z : PiMatrix k d,
      f z * B = B * f' z := by
  -- The rank of an idempotent is its trace, so each block has rank `1` under `f'` and positive
  -- rank under `f`.
  refine exists_piMatrix_retract f f' fun i ↦ ?_
  -- `trace_of_idempotent`: the trace of an idempotent is its rank, and is `0` only for `0`.
  obtain ⟨h_trace', -⟩ := trace_of_idempotent (isIdempotentElem_map_piMatrixUnit f' i)
  obtain ⟨h_trace, h_zero_iff⟩ := trace_of_idempotent (isIdempotentElem_map_piMatrixUnit f i)
  have rank_one : (f' (piMatrixUnit i)).rank = 1 := mod_cast h_trace'.symm.trans (f'_trace i)
  have rank_ne_zero : (f (piMatrixUnit i)).rank ≠ 0 := fun h_rank ↦
    f_ne i (by rw [h_zero_iff, h_trace, h_rank, Nat.cast_zero])
  omega

/-- If the image of `s` spans the product of matrix algebras `∏ M_{d i}(k)`, then every diagonal
matrix lies in the span of the image of `s` under the block diagonal embedding, whose rows
`Σ i, Fin (d i)` are renumbered as `Fin (∑ i, d i)`. -/
lemma New.diagonal_mem_span_range_blockDiagonal {k G : Type} [Field k] [Monoid G] {b : ℕ}
    {d : Fin b → ℕ} (s : G →* PiMatrix k d) (s_span : span k (Set.range s) = ⊤)
    (v : Fin (∑ i, d i) → k) :
    diagonal v ∈ span k (Set.range fun g : G ↦
      (reindexAlgEquiv k k (finSigmaFinEquiv (n := d))).toAlgHom.comp blockDiagonalAlgHom
        (s g)) := by
  let f' : PiMatrix k d →ₐ[k] Matrix (Fin (∑ i, d i)) (Fin (∑ i, d i)) k :=
    (reindexAlgEquiv k k (finSigmaFinEquiv (n := d))).toAlgHom.comp blockDiagonalAlgHom
  -- A diagonal matrix is block diagonal, so it is the image under `f'` of an element of the span.
  have h_block : f' (fun i ↦ diagonal fun x ↦ v (finSigmaFinEquiv ⟨i, x⟩)) = diagonal v := by
    simp [f']
  rw [show (Set.range fun g : G ↦ f' (s g)) = f'.toLinearMap '' Set.range s from
    Set.range_comp f'.toLinearMap s, span_image, s_span, ← h_block]
  exact mem_map_of_mem mem_top

/-- Let `ρ τ` be continuous representations of `Gal(Ω/E)` by matrices over `ℚ̄_ℓ = PadicAlgCl ℓ`
(`(ρ τ).rep`, rows indexed by `(ρ τ).Index`), one for each index `τ` of a finite type. Some
continuous representation `σ` with non-degenerate trace form has as trace the sum of the traces of
the `ρ τ`; it acts on the rows `Σ τ, (ρ τ).Index` of their block diagonal sum. -/
lemma New.GaloisRep.exists_continuous_isTraceNondeg_trace_eq_sum {ℓ : ℕ} [ThePrime ℓ]
    {E ι : Type} [Field E] [EmbeddedNumberField E] [Fintype ι] [DecidableEq ι]
    (ρ : ι → PadicRep Gal(Ω/E) ℓ) (ρ_cont : ∀ τ : ι, Continuous (ρ τ).rep) :
    ∃ σ : GalRep ℓ E (Σ τ : ι, (ρ τ).Index),
      Continuous σ ∧
      IsTraceNondeg σ ∧
      ∀ g : Gal(Ω/E), (σ g).val.trace = ∑ τ : ι, ((ρ τ).rep g).val.trace := by
  -- `ρ_sum g` is the block diagonal matrix with the blocks `ρ τ g`. Its trace satisfies all trace
  -- identities, so it is the trace of a semisimple `σ`.
  let ρ_sum : GalRep ℓ E (Σ τ : ι, (ρ τ).Index) := .toHomUnits
    (.comp blockDiagonalAlgHom.toRingHom.toMonoidHom (.pi fun τ ↦ (Units.coeHom _).comp (ρ τ).rep))
  obtain ⟨σ, σ_ss, σ_trace⟩ : ∃ σ : GalRep ℓ E (Σ τ : ι, (ρ τ).Index),
      IsTraceNondeg σ ∧ ∀ g : Gal(Ω/E), (σ g).val.trace = (ρ_sum g).val.trace :=
    exists_rep_of_trace_identities fun _ h_vanish ↦ h_vanish ρ_sum
  replace σ_trace (g : Gal(Ω/E)) : (σ g).val.trace = ∑ τ, ((ρ τ).rep g).val.trace := by
    simp [σ_trace, ρ_sum, trace_blockDiagonal']
  refine ⟨σ, σ_ss.continuous_of_trace ?_, σ_ss, σ_trace⟩
  simp only [σ_trace]
  fun_prop

/-- Let `s` be a homomorphism from `Gal(Ω/E)` to a product `∏ᵢ M_{d i}(ℚ̄_ℓ)` of matrix algebras,
and let `f` and `f'` be `ℚ̄_ℓ`-algebra maps out of this product with `σ = f ∘ s`, where `f'` lands
in square matrices of size `∑ i, d i`. Suppose each `f' (piMatrixUnit i)` has trace `1`, where
`piMatrixUnit i` is the matrix unit `E₀₀` in factor `i` and zero elsewhere. If `u` is not a
Hodge–Tate jump at `γ` of the representation `f' ∘ s` restricted to the decomposition group of `A`,
then it is not a jump at `γ` of `σ` restricted to that group. -/
lemma New.GaloisRep.jump_eq_zero_of_jump_eq_zero_of_trace_eq_one {ℓ : ℕ} [ThePrime ℓ]
    {E m : Type} [Field E] [EmbeddedNumberField E] [Fintype m] [DecidableEq m] {b : ℕ}
    {d : Fin b → ℕ} [∀ i : Fin b, NeZero (d i)] {σ : GalRep ℓ E m}
    {s : Gal(Ω/E) →* PiMatrix (PadicAlgCl ℓ) d}
    (f : PiMatrix (PadicAlgCl ℓ) d →ₐ[PadicAlgCl ℓ] Matrix m m (PadicAlgCl ℓ))
    (f' : PiMatrix (PadicAlgCl ℓ) d →ₐ[PadicAlgCl ℓ]
      Matrix (Fin (∑ i, d i)) (Fin (∑ i, d i)) (PadicAlgCl ℓ))
    (hf : ∀ g : Gal(Ω/E), f (s g) = (σ g).val)
    (f'_trace : ∀ i : Fin b, (f' (piMatrixUnit i)).trace = 1) {A : ClosurePlace}
    [PadicPlaceEmbedding E A ℓ] {γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ]} {u : ℤ}
    (h_jump : jump (decompRep (.toHomUnits (.comp f' s) : GalRep ℓ E (Fin (∑ i, d i))) A) γ u = 0) :
    jump (decompRep σ A) γ u = 0 := by
  -- Let `r = f' ∘ s`. As `r` has no jump `u`, a period map `ψ` of `σ` vanishes on the images of all
  -- intertwiners from `r` to `σ`, and these images span.
  let r : GalRep ℓ E (Fin (∑ i, d i)) := .toHomUnits (.comp f' s)
  rw [jump_eq_zero_iff] at h_jump ⊢
  intro ψ hψ
  refine ψ.ext fun v ↦ ?_
  let I (i : Fin b) (c : Fin (d i)) (x : Fin (∑ i, d i)) :
      Matrix _ (Fin (∑ i, d i)) (PadicAlgCl ℓ) :=
    intertwiner f f' fun _ ↦ vecMulVec (f (piMatrixUnit i 0 c) *ᵥ v) (Pi.single x 1)
  have I_equiv (i : Fin b) (c : Fin (d i)) (x : Fin (∑ i, d i)) :
      ∀ᶠ g in nearOne (decompGroup Gal(Ω/E) A), ∀ y : Fin (∑ i, d i) → PadicAlgCl ℓ,
        (I i c x).toLin' (decompRep r A g y) = decompRep σ A g ((I i c x).toLin' y) := by
    simp [I, r, ← hf, ← mul_intertwiner]
  -- `ψ` after an intertwiner `I i c x` from `r` to `σ` is a period map of `r`, hence `0`.
  have ψ_I (i : Fin b) (c : Fin (d i)) (x : Fin (∑ i, d i)) (y : Fin (∑ i, d i) → PadicAlgCl ℓ) :
      ψ (I i c x *ᵥ y) = 0 :=
    LinearMap.congr_fun
      (h_jump _ (hodgeTateMaps.pull (I i c x).toLin' (I_equiv i c x) ⟨ψ, hψ⟩).prop) y
  have v_eq : ∑ i, ∑ c, ∑ x, I i c x *ᵥ f' (piMatrixUnit i c) *ᵥ Pi.single x 1 = v := by
    -- Each term is `f' (piMatrixUnit i) x x • f (piMatrixUnit i c c) *ᵥ v`. The sum over `x` is the
    -- trace `1`, and the units `piMatrixUnit i c c` add up to `1`.
    have term_eq (i : Fin b) (c : Fin (d i)) (x : Fin (∑ i, d i)) :
        I i c x *ᵥ f' (piMatrixUnit i c) *ᵥ Pi.single x 1 =
          f' (piMatrixUnit i) x x • f (piMatrixUnit i c c) *ᵥ v := by
      simp [I, -mulVec_single, intertwiner_mul_map_piMatrixUnit, mul_vecMulVec, vecMulVec_mul,
        vecMulVec_mulVec, ← map_mul, ← Pi.single_mul]
    simp [-mulVec_single, term_eq, ← Finset.sum_smul,
      fun i ↦ show ∑ x, f' (piMatrixUnit i) x x = 1 from f'_trace i, ← sum_mulVec, ← map_sum,
      sum_piMatrixUnit]
  simp only [← v_eq, map_sum, ψ_I, Finset.sum_const_zero, LinearMap.zero_apply]

/-- Suppose that for each embedding `τ` there is a continuous `ρ` which, at `F`-almost all places
`w`, is unramified or crystalline, has every member of `J τ` among its jumps at `τ`, and has
geometric Frobenius killed by `P w`. (`Set.indicator {τ} J` is `J τ` at `τ` and the empty multiset,
no condition, elsewhere.) Then there is one continuous `r` such that (a) every diagonal matrix is
in the span of its image, and (b) the same conditions hold at `F`-almost all `w`, with the jumps
`J τ` at all `τ` at once. -/
lemma New.GaloisRep.exists_rep_span_diagonal {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E : Type} [Field E]
    [EmbeddedNumberField E] (F : Filter (FinPlace E)) (J : (E →+* ℂ) → Multiset ℤ)
    (P : FinPlace E → (PadicAlgCl ℓ)[X])
    (h_each : ∀ τ : E →+* ℂ, ∃ ρ : PadicRep Gal(Ω/E) ℓ,
      Continuous ρ.rep ∧
      ∀ᶠ w in F, IsSphericalAbove ρ.rep OccursIn (Set.indicator {τ} J) w (P w)) :
    ∃ (b : ℕ) (r : GalRep ℓ E (Fin b)),
      Continuous r ∧
      -- (a)
      (∀ v : Fin b → PadicAlgCl ℓ,
        diagonal v ∈ span (PadicAlgCl ℓ) (Set.range fun g : Gal(Ω/E) ↦ (r g).val)) ∧
      -- (b)
      ∀ᶠ w in F, IsSphericalAbove r OccursIn J w (P w) := by
  classical
  -- Let `σ` be semisimple with the trace of the sum of the `ρ τ`; the clauses pass to `σ` by
  -- `local_clauses_of_trace_limit`. Take for `r` the sum of the distinct irreducible constituents
  -- of `σ`, each once: a retract of `σ`, in which all the jumps of `σ` still occur.
  choose ρ ρ_cont hρ using h_each
  obtain ⟨σ, σ_cont, σ_ss, σ_trace⟩ := exists_continuous_isTraceNondeg_trace_eq_sum ρ ρ_cont
  -- By Wedderburn, `σ = f ∘ s`, where the image of `s` spans a product of matrix algebras and `f`
  -- kills no block unit `piMatrixUnit i`.
  obtain ⟨b, d, d_ne_zero, s, f, f_ne, s_span, hf : ∀ g : Gal(Ω/E), f (s g) = (σ g).val⟩ :=
    exists_wedderburn _ (MonoidHom.id Gal(Ω/E)) σ_ss.hasSemiprimeSpan ⟨by simp⟩
  -- `f'` is the block diagonal embedding of the product.
  let f' : PiMatrix (PadicAlgCl ℓ) d →ₐ[PadicAlgCl ℓ]
      Matrix (Fin (∑ i, d i)) (Fin (∑ i, d i)) (PadicAlgCl ℓ) :=
    (reindexAlgEquiv _ (PadicAlgCl ℓ) (finSigmaFinEquiv (n := d))).toAlgHom.comp blockDiagonalAlgHom
  have f'_trace (i : Fin b) : trace (f' (piMatrixUnit i)) = 1 := by
    simp +contextual [f', -coe_reindexAlgEquiv, Fintype.sum_eq_single i, trace_blockDiagonal']
  -- Each factor occurs in `f` and occurs once in `f'`, so `f'` is a retract of `f`.
  obtain ⟨incl, proj, h_proj_incl, h_incl⟩ :=
    exists_retract_of_trace_map_piMatrixUnit_eq_one f f' f_ne f'_trace
  let r : GalRep ℓ E (Fin (∑ i, d i)) := .toHomUnits (.comp f' s)
  have intertwine (g : Gal(Ω/E)) : (σ g).val * incl = incl * (r g).val :=
    (congrArg (· * incl) (hf g).symm).trans (h_incl (s g))
  refine ⟨_, r, .of_coeHom_comp ?_, diagonal_mem_span_range_blockDiagonal s s_span, ?_⟩
  · -- `r g = proj * σ g * incl`
    refine .congr (f := fun g ↦ proj * ((σ g).val * incl)) (by fun_prop) fun g ↦ ?_
    simp [intertwine, ← proj.mul_assoc, h_proj_incl]
  -- Fix `w` where the clauses hold for every `ρ τ`, and a place `A` over `w`.
  filter_upwards [eventually_all.mpr hρ] with w h_spherical A hA
  -- The clauses for each `ρ τ` at `A`.
  have hρ_at (τ : E →+* ℂ) :
      IsGoodAt (ρ τ).rep A ∧
      JumpsRelAt (ρ τ).rep A OccursIn (Set.indicator {τ} J) ∧
      ∀ s : Gal(Ω/E), IsFrob A w.q s⁻¹ → PolyKillsAt (ρ τ).rep A s (P w) :=
    h_spherical τ hA
  choose hρ_good hρ_jumps hρ_poly using hρ_at
  -- The clauses for `σ`, by `local_clauses_of_trace_limit` for a family with one member: an element
  -- of `J τ` is a jump of `ρ τ`, so the sum of the multiplicities is not `0`.
  have σ_limit : IsTraceLimit σ A (pure ()) 1 fun _ ↦ ρ :=
    { continuous_limit := σ_cont
      isTraceNondeg := σ_ss
      continuous_approx := fun _ ↦ ρ_cont
      isGoodAt_approx := fun _ τ ↦ hρ_good τ
      finite_or_hasJumpsAt := .inl inferInstance
      tendstoUniformly_trace := by simp [σ_trace, tendstoUniformly_iff] }
  obtain ⟨σ_good, (σ_jump : JumpsRelAt σ A OccursIn J), σ_poly⟩ :=
    local_clauses_of_trace_limit σ_limit (R := OccursIn) (J := J) (fun _ τ ↦ hρ_jumps τ)
    fun τ u x n h_occ h_tendsto hu_count hn_zero ↦ by
      have h_count_ne : (Set.indicator {τ} J τ).count u ≠ 0 := by simpa using hu_count
      -- the limit `n = 0` is the sum of the natural numbers `x () τ'`, so each of them is `0`
      have hx_zero : x () τ = 0 := by simp_all [Tendsto, ← Nat.cast_sum]
      exact h_occ () τ h_count_ne hx_zero
  -- Finite type and killing polynomials pass to the retract `r`.
  obtain ⟨(r_finite : IsFiniteTypeAt σ A → IsFiniteTypeAt r A), -, r_poly⟩ :=
    local_clauses_of_retract (A := A) (c := 1) (i := 1) (φ := .id _) (hi := by simp) (hφ := by simp)
      (hφ_open := .id) (hS := univ_mem) (h_comm := fun g _ ↦ intertwine g) (hP := h_proj_incl)
  replace r_poly (s : Gal(Ω/E)) (Q : (PadicAlgCl ℓ)[X]) :
      PolyKillsAt σ A s Q → PolyKillsAt r A s Q :=
    r_poly s ⟨⟩
  refine ⟨?_, ?_, fun s hs ↦ ?_⟩
  · obtain ⟨σ_finite, σ_inertia⟩ := (isGoodAt_iff ..).mp σ_good
    exact (isGoodAt_iff ..).mpr ⟨r_finite σ_finite, fun s hs ↦ r_poly s _ (σ_inertia s hs)⟩
  · -- A jump of `σ` is a jump of its retract `r`.
    intro L γ g hg u hu
    exact mt (jump_eq_zero_of_jump_eq_zero_of_trace_eq_one f f' hf f'_trace) (σ_jump hg u hu)
  · refine r_poly s _ (σ_poly .refl (fun _ τ ↦ ⟨.refl, hρ_poly τ s hs⟩) ?_)
    simp [σ_trace, Finset.mul_sum, tendstoUniformly_iff]

end MultiplicityFreeSum

/-! ## The Hodge–Tate cocharacter and the Zariski closure of the image -/

section HodgeTateCocharacter

open Finset Matrix LaurentPolynomial

/-- Let `p` be a prime, `x i ∈ ℂ_p` and `κ i` integers. The absolute Galois group `G_p = Gp p` of
`ℚ_p` (that is, Gal(Q̄_p/Q_p)) acts on `ℂ_p` by `g • ·`, and `χ = cyclotomicGp` is its p-adic
cyclotomic character. If a polynomial `F` over `ℂ_p` vanishes at `(χ(g) ^ (-κ i) g(x i))_i` for all
`g ∈ G_p` near `1`, then `F` vanishes at `(T ^ (κ i) x i)_i` in the Laurent polynomials over
`ℂ_p`. -/
lemma New.Period.aeval_cocharacter_eq_zero {p : ℕ} [ThePrime p] {n : Type _} [Fintype n] (κ : n → ℤ)
    (x : n → ℂ_[p]) (F : MvPolynomial n ℂ_[p])
    (h : ∀ᶠ g : Gp p in nhds 1, F.aeval (fun i : n ↦ (cyclotomicGp g ^ (-κ i)).val • g • x i) = 0) :
    F.aeval (fun i : n ↦ T (κ i) * C (x i)) = 0 := by
  -- View `F` as the vector of its coefficients, indexed by its monomials `ν`. The vectors that
  -- vanish at the twisted translates form a space `W` stable under the twisted Galois action, so
  -- by `le_of_hodgeTate_stable` it suffices to treat vectors of pure weight.
  simp only [F.aeval_def, F.eval₂_eq', ← F.support.sum_coe_sort, ← Algebra.smul_def] at h ⊢
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _ h
  -- `u ν` is the weight of the monomial `ν`; `W` consists of the vectors that vanish at the
  -- translates by all `g` in the open subgroup `V`, and `W'` of those that vanish at `T ^ κ * x`.
  let u (ν : F.support) : ℤ := ∑ i, ν.val i * κ i
  let W : Submodule ℂ_[p] (F.support → ℂ_[p]) := (of fun (ν : F.support) (g : V) ↦
    ∏ i, ((cyclotomicGp g ^ (-κ i)).val • (g : Gp p) • x i) ^ ν.val i).vecMulLinear.ker
  let W' : Submodule ℂ_[p] (F.support → ℂ_[p]) := (Fintype.linearCombination ℂ_[p]
    fun ν : F.support ↦ ∏ i, (T (κ i) * C (x i)) ^ ν.val i).ker
  refine le_of_hodgeTate_stable le_rfl u W W'
    (fun a ha ↦ ?_) (fun v ν hv _ h_supp _ _ ↦ ?_) (funext fun g ↦ hV g.prop)
  · -- Stability: for `k ∈ V`, apply `k` to the equation of `W` at `k⁻¹ * g`.
    filter_upwards [V.mem_nhds_one] with k hk
    refine LinearMap.mem_ker.mpr (funext fun g ↦ ?_)
    have zpow_sum (f : n → ℤ) : cyclotomicGp k ^ ∑ i, f i = ∏ i, cyclotomicGp k ^ f i := by
      simpa [-map_prod] using map_prod (zpowersHom _ (cyclotomicGp k)) (.ofAdd ∘ f) univ
    simpa [u, mul_pow, smul_smul, smul_prod', dotProduct, _root_.zpow_mul', vecMul, smul_sum,
      zpow_sum, mul_zpow, smul_pow, prod_smul, smul_comm k, prod_mul_distrib] using
      congrArg (k • ·) (congrFun (LinearMap.mem_ker.mp ha) (⟨k, hk⟩⁻¹ * g))
  · -- For `v` of pure weight `u ν`, the equation of `W'` is that of `W` at `1`, times `T (u ν)`.
    have h_one : ∑ l, (v l : ℂ_[p]) * ∏ i, x i ^ (l : n →₀ ℕ) i = 0 := by
      simpa [vecMul, dotProduct] using congrFun (LinearMap.mem_ker.mp hv) 1
    calc ∑ l, (v l : ℂ_[p]) • ∏ i, (T (κ i) * C (x i)) ^ (l : n →₀ ℕ) i
        = ∑ l, ((v l : ℂ_[p]) * ∏ i, x i ^ (l : n →₀ ℕ) i) • T (u ν) :=
          sum_congr rfl fun l _ ↦ (h_supp l).elim
            (fun hl ↦ by simp [← hl, u, T, C, -single_eq_C_mul_T]) (fun hl ↦ by simp [hl])
      _ = 0 := by rw [← sum_smul, h_one, zero_smul]

end HodgeTateCocharacter
end
end

/-!
# Seed representations: odd rank, a cuspidal type and free jumps

The Galois representation of a form `f` of odd rank on the definite unitary group, under two extra
local hypotheses: a cuspidal type at a split place and free jumps.

* `New.GaloisRep.exists_rep_of_cuspidal_type`: under these hypotheses, there is a continuous
  representation with the characteristic polynomials of Frobenius given by the Hecke polynomials of
  `f`, spherical at a further split place outside the ramification.

The proof transfers `f` to a form on the definite frames on which the centre acts by a character
(`New.GaloisRep.exists_central_eigenform`), realizes its Hecke eigenvalues in the cohomology of a
PEL model for each complex embedding of `E`, and joins the representations so obtained into one of
rank `a` (`New.GaloisRep.exists_galRep_charpoly_eq_of_forall_embedding`).

Notions from other files:
* `New.jumps κ N σ`: the multiset {j − 1 − λ_j} if σ is in the CM type, else {λ_j + N − j},
  1 ≤ j ≤ N, with λ the highest weight of κ at the place v of σ: λ_j = `κ.2 v` + Σ_{j ≤ h < N}
  `κ.1 v h`.
* `New.Variety.definiteForms 𝔑 ξ`: the functions `φ` on `GL n (𝔸f E)` with `φ (y x) = ξ y (φ x)` for
  rational `y`, zero off the definite frames, and right invariant under the level `levelGU n 𝔑`.
* `New.Variety.IsSafe 𝔑 w`: the place of `QuadField d` below `w` satisfies `IsSplitPrimeToDisc`, and
  `𝔑` lies neither in `w` nor in any place above the conjugate of that place.
* `New.GaloisRep.IsSphericalAbove r R J w P`: at every place above `w`, `r` is unramified or
  crystalline, its jumps are related to the multisets `J` by `R` (`OccursIn`: each member of `J` is
  among its jumps; `Eq`: they are exactly its jumps), and `P` kills its geometric Frobenius
  elements.
* `New.HasNoSmallRelations e`: two families of natural numbers with the same sum, at most
  `(n + 1) ^ 2`, and the same sum weighted by the `e i`, are equal.

## Relation to the literature

Known; see `Lib.GaloisRep.Main.OddRank` for sources.
-/

@[expose] public section

open NumberField Matrix New Variety Period IsLocalization RingHom Subgroup Gf

/-- Moving a coset representative at a split place. Let the cosets modulo the level `levelGU n 𝔑`
of `toFinGL y₀ * invTransposeGL u₀` and of `x` agree, and let `𝔑 ∉ star w` for the split place `w`.
Then for some `c` at `w` and all `y : GL n E` and `g` at `w`, the cosets of
`toFinGL (y * y₀) * invTransposeGL (u₀ * ofSplitPlace w (c * g))` and of
`toFinGL y * (x * conjAtSplit w g)` agree. -/
private lemma New.GaloisRep.exists_forall_mk_eq_mk_mul_conjAtSplit {E : Type} [Field E] [CMBase E]
    {n : Type} [Fintype n] [DecidableEq n] {𝔑 : 𝓞 E} {y₀ : GL n E} {u₀ : Gf E n}
    {x : GL n (𝔸f E)}
    (h_coset : (⟦toFinGL y₀ * invTransposeGL u₀.val⟧ : GL n (𝔸f E) ⧸ levelGU n 𝔑) = ⟦x⟧)
    {w : SplitFinPlace E} (hw : 𝔑 ∉ (star w.val).asIdeal) :
    ∃ c : GL n (LocField (w : FinPlace E)),
      ∀ (y : GL n E) (g : GL n (LocField (w : FinPlace E))),
        (⟦toFinGL (y * y₀) * invTransposeGL (u₀ * ofSplitPlace w.prop (c * g)).val⟧ :
            GL n (𝔸f E) ⧸ levelGU n 𝔑) =
          ⟦toFinGL y * (x * conjAtSplit w g)⟧ := by
  set κ : GL n (𝔸f E) := (toFinGL y₀ * invTransposeGL u₀.val)⁻¹ * x
  have h_mem : κ ∈ levelGU n 𝔑 := QuotientGroup.eq.mp h_coset
  -- This level element is its component `conjAtSplit w c` at `w`, `star w`, itself in the level,
  -- times an element that commutes with every `conjAtSplit w g`.
  obtain ⟨h_loc, h_comm⟩ := conjAtSplit_dualComponent hw h_mem
  set c : GL n (LocField (w : FinPlace E)) := dualComponent w κ
  refine ⟨c, fun y g ↦ QuotientGroup.eq.mpr ?_⟩
  have h_elt : (toFinGL (y * y₀) * invTransposeGL (u₀ * ofSplitPlace w.prop (c * g)).val)⁻¹ *
      (toFinGL y * (x * conjAtSplit w g)) = (conjAtSplit w c)⁻¹ * κ := by
    simpa [mul_assoc, κ] using!
      (h_comm g).symm.inv_mul_cancel
  rw [h_elt]
  exact mul_mem (inv_mem h_loc) h_mem

/-- Extension of a function `f` on `Gf E n`, on which rational unitary matrices act through `ξ`
(`h_rat`) and which is invariant at level `𝔑` (`h_level`), to a function `φ` on `GL n (𝔸f E)`. `φ`
agrees with `f` on `Gf E n` embedded by `invTransposeGL`, is right invariant under `levelGU n 𝔑`,
and vanishes off the definite frames (`IsSignedFrame x 1`: frames of totally positive definite
rational forms). At each split place `w` with `𝔑 ∉ star w` and each `x`,
`φ (y * x * conjAtSplit w g)` is `ξ y` of one linear map `L` applied to the translate of `f` by
`ofSplitPlace w g`. -/
lemma New.GaloisRep.exists_frame_extension {E : Type} [Field E] [CMBase E] {n W : Type} [Fintype n]
    [DecidableEq n] [Nonempty n] [AddCommGroup W] [Module ℂ W] (ξ : Representation ℂ (GL n E) W)
    {f : Gf E n → W} {𝔑 : 𝓞 E}
    (h_rat : ∀ y ∈ U (1 : Matrix n n E), ∃ c : Gf E n,
      (∀ u : Gf E n, f (c * u) = ξ y (f u)) ∧ invTransposeGL c.val = toFinGL y)
    (h_level : ∀ u : Gf E n, invTransposeGL u.val ∈ levelGU n 𝔑 → u ∈ rightStabilizer f) :
    ∃ φ : GL n (𝔸f E) → W,
      (∀ g : Gf E n, φ (invTransposeGL g.val) = f g) ∧
      (∀ x : GL n (𝔸f E), ∀ k ∈ levelGU n 𝔑, φ (x * k) = φ x) ∧
      (∀ x : GL n (𝔸f E), ¬IsSignedFrame x 1 → φ x = 0) ∧
      ∀ w : SplitFinPlace E, 𝔑 ∉ (star w.val).asIdeal → ∀ x : GL n (𝔸f E),
        ∃ L : (Gf E n → W) →ₗ[ℂ] W, ∀ (y : GL n E) (g : GL n (LocField (w : FinPlace E))),
        φ (toFinGL y * (x * conjAtSplit w g)) =
          ξ y (L (rightRegular ℂ (Gf E n) W (ofSplitPlace w.property g) f)) := by
  have h_frame (u : Gf E n) : IsSignedFrameFor (invTransposeGL u.val) 1 1 :=
    isSignedFrameFor_one (entryConj u)
  let Q (p : GL n E × Gf E n) : GL n (𝔸f E) ⧸ levelGU n 𝔑 := ⟦toFinGL p.1 * invTransposeGL p.2.val⟧
  let φ (x : GL n (𝔸f E)) : W := Q.extend (fun p ↦ ξ p.1 (f p.2)) 0 ⟦x⟧
  -- Well defined: if `(z * y, u)` and `(z, t)` give the same coset, then `y` is unitary, since
  -- `u` and `t` both give definite frames for the form `1`.
  have h_factors : (fun p : GL n E × Gf E n ↦ ξ p.1 (f p.2)).FactorsThrough Q := by
    rintro ⟨z, t⟩ ⟨z', u⟩ h_eq
    obtain ⟨y, rfl⟩ : ∃ a : GL n E, z * a = z' := mul_left_surjective z z'
    have h_mem : (invTransposeGL t.val)⁻¹ * (toFinGL y * invTransposeGL u.val) ∈ levelGU n 𝔑 := by
      simpa [mul_assoc] using QuotientGroup.eq.mp h_eq
    have h_scalar :
        IsScalarFrame ((invTransposeGL t.val)⁻¹ * toFinGL y * invTransposeGL u.val)⁻¹ 1 := by
      simpa [mul_assoc] using levelGU.isScalarFrame_inv_one h_mem
    have hy : y ∈ U (1 : Matrix n n E) := mem_unitaryGroupOf_iff.2 <|
      ((h_frame u).conjTranspose_mul_mul_eq_smul (h_frame t) h_scalar).trans (by simp)
    obtain ⟨c, hc_f, hc⟩ := h_rat y hy
    have h_stab : t⁻¹ * c * u ∈ rightStabilizer f :=
      h_level _ (by simpa [← hc, mul_assoc] using h_mem)
    have h_fix : f (t * (t⁻¹ * c * u)) = f t := h_stab t
    have h_ft : f t = ξ y (f u) := by simpa [← hc_f u, mul_assoc] using h_fix.symm
    simp [h_ft]
  have hφ {p : GL n E × Gf E n} {x : GL n (𝔸f E)} (h : Q p = ⟦x⟧) : φ x = ξ p.1 (f p.2) := by
    simp [φ, ← h, h_factors.extend_apply]
  have hφ_zero {x : GL n (𝔸f E)} (h : ¬∃ p : GL n E × Gf E n, Q p = ⟦x⟧) : φ x = 0 :=
    Q.extend_apply' (fun p : GL n E × Gf E n ↦ ξ p.1 (f p.2)) 0 ⟦x⟧ h
  have h_move {p : GL n E × Gf E n} {x : GL n (𝔸f E)} (h : Q p = ⟦x⟧) {w : SplitFinPlace E}
      (hw : 𝔑 ∉ (star w.val).asIdeal) :
      ∃ c : GL n (LocField (w : FinPlace E)),
        ∀ (y : GL n E) (g : GL n (LocField (w : FinPlace E))),
          Q (y * p.1, p.2 * ofSplitPlace w.prop (c * g)) = ⟦toFinGL y * (x * conjAtSplit w g)⟧ :=
    exists_forall_mk_eq_mk_mul_conjAtSplit h hw
  refine ⟨φ, fun g ↦ ?_, fun x k hk ↦ ?_, fun x hx ↦ ?_, fun w hw x ↦ ?_⟩
  · simpa using hφ (p := (1, g)) (by simp [Q])
  · simp [φ, hk]
  · -- A coset of `toFinGL y * invTransposeGL u` consists of definite frames.
    refine hφ_zero fun ⟨⟨y, u⟩, hp⟩ ↦ hx ?_
    simpa [ratConj, mul_assoc] using
      IsSignedFrame.mul ⟨1, h_frame u⟩ y (QuotientGroup.eq.mp hp).left
  · -- The linear map at `x`: evaluate a translate at `p.2` and apply `ξ p.1`, or `0` off the
    -- cosets.
    by_cases hx : ∃ p : GL n E × Gf E n, Q p = ⟦x⟧
    · obtain ⟨p, hp⟩ := hx
      obtain ⟨c, hc⟩ := h_move hp hw
      refine ⟨ξ p.1 ∘ₗ LinearMap.proj p.2 ∘ₗ rightRegular ℂ (Gf E n) W (ofSplitPlace w.prop c),
        fun y g ↦ ?_⟩
      simpa [mul_assoc] using hφ (hc y g)
    · refine ⟨0, fun y g ↦ ?_⟩
      have h_none : ¬∃ p : GL n E × Gf E n, Q p = ⟦toFinGL y * (x * conjAtSplit w g)⟧ := by
        -- Otherwise, moving back by `y⁻¹` and `g⁻¹` puts `x` on one of the cosets.
        rintro ⟨p, hp⟩
        obtain ⟨c, hc⟩ := h_move hp hw
        exact hx ⟨_, (hc y⁻¹ g⁻¹).trans (by simp [mul_assoc])⟩
      simp [hφ_zero h_none]

/-- Let `f ≠ 0` on `Gf E n` take values in a finite-dimensional `W`, let rational unitary matrices
act on `f` through `ξ`, let `f` be invariant at the neat level `𝔑`, and let some split place `w₀`
have `𝔑 ∉ star w₀`. Then some nonzero `ψ` in `definiteForms 𝔑 ξ` exists. This means `ψ` is left
`ξ`-equivariant under `GL n E`, zero off the definite frames, and right `levelGU n 𝔑`-invariant. It
has a central character `ω` (the finite ideles of `QuadField d` act through `centralScalar` by `ω`),
and at each split `w` with `𝔑 ∉ star w`, its translates are the images of those of `f` under one
linear map `L`. -/
lemma New.GaloisRep.exists_central_eigenform {E : Type} [Field E] [CMBase E] {d : ℕ}
    [HasQuadSubfield d E] {n W : Type} [Fintype n] [DecidableEq n] [Nonempty n] [AddCommGroup W]
    [Module ℂ W] [Module.Finite ℂ W] (ξ : Representation ℂ (GL n E) W) {f : Gf E n → W} (hf : f ≠ 0)
    {𝔑 : 𝓞 E} (h_neat : IsNeat n 𝔑) (w₀ : SplitFinPlace E) (hw₀ : 𝔑 ∉ (star w₀.val).asIdeal)
    (h_rat : ∀ y ∈ U (1 : Matrix n n E), ∃ c : Gf E n,
      (∀ u : Gf E n, f (c * u) = ξ y (f u)) ∧ invTransposeGL c.val = toFinGL y)
    (h_level : ∀ u : Gf E n, invTransposeGL u.val ∈ levelGU n 𝔑 → u ∈ rightStabilizer f) :
    ∃ ψ ∈ Variety.definiteForms 𝔑 ξ,
      ψ ≠ 0 ∧
      (∃ ω : (𝔸f (QuadField d))ˣ →* ℂ, ∀ x : (𝔸f (QuadField d))ˣ,
        rightRegular ℂ (GL n (𝔸f E)) W (centralScalar x) ψ = ω x • ψ) ∧
      ∀ w : SplitFinPlace E, 𝔑 ∉ (star w.val).asIdeal → ∃ L : (Gf E n → W) →ₗ[ℂ] GL n (𝔸f E) → W,
        ∀ g : GL n (LocField (w : FinPlace E)),
        rightRegular ℂ (GL n (𝔸f E)) W (conjAtSplit w g) ψ =
          L (rightRegular ℂ (Gf E n) W (ofSplitPlace w.property g) f) := by
  obtain ⟨φ, hφ, hφ_level, hφ_zero, hφ_loc⟩ := exists_frame_extension ξ h_rat h_level
  choose L hL using hφ_loc
  let s : (𝔸f (QuadField d))ˣ →* GL n (𝔸f E) := centralScalar
  let ρ : (𝔸f (QuadField d))ˣ →* (GL n (𝔸f E) → W) →ₗ[ℂ] GL n (𝔸f E) → W :=
    (rightRegular ℂ (GL n (𝔸f E)) W).comp s
  have h_central (x : (𝔸f (QuadField d))ˣ) (g : GL n (𝔸f E)) : g * s x = s x * g :=
    commute_scalar_GL ..
  have hL_one (w : SplitFinPlace E) (hw : 𝔑 ∉ (star (w : FinPlace E)).asIdeal) (x : GL n (𝔸f E))
      (g : GL n (LocField (w : FinPlace E))) :
      φ (x * conjAtSplit w g) = L w hw x (rightRegular ℂ (Gf E n) W (ofSplitPlace w.prop g) f) := by
    simpa using hL w hw x 1 g
  have hφ_rat (x : GL n (𝔸f E)) (y : GL n E) : φ (toFinGL y * x) = ξ y (φ x) := by
    have h_x : φ x = L w₀ hw₀ x f := by simpa using hL_one w₀ hw₀ x 1
    simpa [h_x] using hL w₀ hw₀ x y 1
  -- The central translates of `φ` span a nonzero subspace of the finite-dimensional space of forms.
  have h_le : cyclicSpan ρ φ ≤ Variety.definiteForms 𝔑 ξ := by
    -- Each central translate `ρ x φ` is equivariant, vanishes off the definite frames and is
    -- invariant under the level.
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun x ↦ ⟨⟨?_, ?_⟩, ?_⟩)
    · intro y z
      simp [ρ, hφ_rat, mul_assoc]
    · refine fun z hz ↦ hφ_zero _ fun h_frame ↦ hz ?_
      simpa [s, ratConj] using h_frame.mul 1 (inv_mem (mem_GU_centralScalar x))
    · simp +contextual [ρ, funext_iff, h_central, ← mul_assoc, hφ_level]
  have : Module.Finite ℂ (Variety.definiteForms 𝔑 ξ) := finite_definiteForms ξ h_neat
  have : Module.Finite ℂ (cyclicSpan ρ φ) := .of_fg (.of_le .of_finite h_le)
  have hφ_ne : φ ≠ 0 := fun h_zero ↦ hf (funext fun g ↦ by simp [← hφ g, h_zero])
  have h_ne : ¬cyclicSpan ρ φ ≤ ⊥ := fun h_bot ↦ hφ_ne (h_bot self_mem_cyclicSpan)
  obtain ⟨ω, ψ, hψ_mem, hψ_ne, hω⟩ := exists_eigencharacter ρ apply_mem_cyclicSpan h_ne
  refine ⟨ψ, h_le hψ_mem, hψ_ne, ⟨ω, hω⟩, fun w hw ↦ ?_⟩
  -- `ψ` is a combination of central translates of `φ`; the same combination of the `L w hw` works.
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hψ_mem
  refine ⟨c.sum fun x r ↦ r • LinearMap.pi fun y ↦ L w hw (s x * y), fun g ↦ ?_⟩
  simp [ρ, funext_iff, Finsupp.sum, ← mul_assoc, h_central, hL_one w hw]

/-- A place `w` of `E` whose residue field has prime order and which does not contain `d` lies above
a place of `QuadField d` with `IsSplitPrimeToDisc`: that place contains `betaK d - b` for an integer
`b`, and this element is coprime to its conjugate. -/
lemma New.GaloisRep.isSplitPrimeToDisc_below_of_prime_norm {E : Type} [Field E] [NumberField E]
    {d : ℕ}
    [HasQuadSubfield d E] {w : FinPlace E} (hq_prime : w.q.Prime) (hd_notMem : ↑d ∉ w.asIdeal) :
    IsSplitPrimeToDisc (w.below (QuadField d)) := by
  -- The residue field at `w` has prime order and the class of `d` is nonzero, so it generates the
  -- additive group: `betaK d ≡ c * d` modulo `w` for an integer `c`.
  obtain ⟨c, hc⟩ :
      Ideal.Quotient.mk w.asIdeal (algebraMap (𝓞 (QuadField d)) (𝓞 E) (QuadField.betaK d)) ∈
        AddSubgroup.zmultiples (Ideal.Quotient.mk w.asIdeal (d : 𝓞 E)) :=
    mem_zmultiples_of_prime_card (hp := ⟨hq_prime⟩) (Ideal.absNorm_eq_natCard _).symm
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hd_notMem)
  have hx_mem :
      QuadField.betaK d - ((c * d : ℤ) : 𝓞 (QuadField d)) ∈ (w.below (QuadField d)).asIdeal :=
    Ideal.mem_comap.mpr (by simpa using Ideal.Quotient.eq.mp hc.symm)
  refine ⟨c * d, hx_mem, 1 - 2 * c * QuadField.sqrtNegDInt d,
    2 * c * QuadField.sqrtNegDInt d + 1, ?_⟩
  -- A Bézout relation, from `star (betaK d) = 1 - betaK d` and `(2 * betaK d - 1) ^ 2 = -d`.
  have h_sq : (2 * QuadField.betaK d - 1) ^ 2 = -(d : 𝓞 (QuadField d)) := QuadField.sqrtNegDInt_sq d
  simp only [star_sub, QuadField.star_betaK, QuadField.sqrtNegDInt, Int.cast_mul, Int.cast_natCast,
    star_mul', star_intCast, star_natCast]
  linear_combination (-2 * (c : 𝓞 (QuadField d))) * h_sq

/-- Rank and characteristic polynomials from a Hodge–Tate frame: if the image of `r` spans the
diagonal matrices, `P w`, monic of degree `a`, kills `r` along `mostFrobenii E`, and `r` is
good at the place of `ε` with the free jumps `e i` of `κ` among its jumps, then `r` has rank `a` and
characteristic polynomials `P w` along `mostFrobenii E`: near `1` the cocharacter of the frame lies
in the Zariski closure of the image of `r`, and `card_eq_and_charpoly_eq` applies. -/
private lemma New.GaloisRep.card_eq_and_eventually_charpoly_eq_of_hasNoSmallRelations {ℓ : ℕ}
    {E : Type} {a b : ℕ} [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E]
    [NeZero a] (κ : Weight E) {P : FinPlace E → Polynomial (PadicAlgCl ℓ)} (r : GalRep ℓ E (Fin b))
    (hr : Continuous r)
    (h_diag : ∀ v : Fin b → PadicAlgCl ℓ,
      diagonal v ∈ Submodule.span (PadicAlgCl ℓ) (Set.range fun g : Gal(Ω/E) ↦ (r g).val))
    (h_kill : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      (P y.place).aeval (r y.frob).val = 0 ∧ (P y.place).IsMonicOfDegree a)
    {ε : Ω →+* PadicAlgCl ℓ} {e : Fin a → ℤ} (he_free : HasNoSmallRelations e)
    (he_jumps : ∀ i : Fin a, e i ∈ jumps κ a (RingHom.comp ιℓ.symm (ε.comp (algebraMap E Ω))))
    (h_good : IsGoodAt r ((intQpBar ℓ).comap ε))
    (h_jump : JumpsRelAt r ((intQpBar ℓ).comap ε) OccursIn (jumps κ a)) :
    Fintype.card (Fin b) = a ∧
      ∀ᶠ y : FrobeniusDatum E in mostFrobenii E, (r y.frob).val.charpoly = P y.place := by
  -- A Hodge–Tate frame `T` at the place `A` of `ε`; its weights `k` include the `e i`.
  let A : ValuationSubring Ω := (intQpBar ℓ).comap ε
  obtain ⟨j, h_induces, hj_open, hj_range⟩ := exists_inducesPlace E Gal(Ω/E) (ι := ε) rfl
  -- The embedding `ε` and the open embedding `j` of the decomposition group, bundled.
  let chart : PadicPlaceEmbedding E A ℓ :=
    .mk (toOverGp := ⟨_, ⟨hj_open.isOpen_range⟩⟩) _ ⟨h_induces, hj_open, hj_range⟩
  obtain ⟨-, h_crys⟩ := h_good
  obtain ⟨T, k, hT, hk, -⟩ :=
    h_crys.isPotentiallyCrystalline.exists_isHodgeTateFrame (Pi.basisFun ..)
      (IsScalarTower.toAlgHom ..)
  -- Each `e i` is a jump of `κ` at `ε`, hence a jump of `r` at `A`: a weight `k`.
  have h_weights (i : Fin a) : e i ∈ Set.range k := by
    have h_jump_ne :
        jump (decompRep r A) (IsScalarTower.toAlgHom ℤ_[ℓ] (PadicAlgCl ℓ) ℂ_[ℓ]) (e i) ≠ 0 := by
      refine h_jump (L := chart) (g := 1) (fun _ ↦ rfl) (e i) ?_
      -- The embedding that `chart` induces through `g = 1` is the one of `ε`.
      convert Multiset.count_ne_zero.mpr (he_jumps i)
      ext x
      simp [chart]
      rfl -- `chart.e` is `ε` by definition
    rw [hk (e i), Multiset.count_ne_zero] at h_jump_ne
    simpa using h_jump_ne
  -- Near `1` the entries of `T⁻¹ * r g` are twisted translates of the entries of `T⁻¹`.
  have h_entries : ∀ᶠ g : decompGroup Gal(Ω/E) A in nearOne (decompGroup Gal(Ω/E) A),
      (T⁻¹.val * (r g).val.map (algebraMap ..)).uncurry = fun i : Fin b × Fin b ↦
        (cyclotomicGp (j g) ^ (-k i.1)).val • j g • T⁻¹.val.uncurry i := by
    refine hT.mono fun g hg ↦ funext fun i ↦ ?_
    refine Eq.trans ?_ (inv_mul_apply_of_isHodgeTateFrame hg i.1 i.2)
    simp [Matrix.mul_apply, Function.uncurry]
  -- So the cocharacter with weights `k` lies in the Zariski closure of the image of `r`, and
  -- `card_eq_and_charpoly_eq` gives the rank of `r` and its characteristic polynomials.
  refine card_eq_and_charpoly_eq r hr h_diag h_kill T⁻¹ k he_free h_weights fun G hG ↦ ?_
  -- `G` vanishes at `T⁻¹ * r g` near `1`, so at the translates, so at the cocharacter.
  have h_near : ∀ᶠ g : decompGroup Gal(Ω/E) A in nearOne (decompGroup Gal(Ω/E) A),
      G.aeval (T⁻¹.val * (r g).val.map (algebraMap (PadicAlgCl ℓ) ℂ_[ℓ])).uncurry = 0 := by
    rw [nearOne_eq_nhds_one hj_open]
    exact continuousAt_subtypeVal (x := (1 : decompGroup Gal(Ω/E) A)) hG
  have h_twisted : ∀ᶠ g : decompGroup Gal(Ω/E) A in nearOne (decompGroup Gal(Ω/E) A),
      G.aeval (fun i : Fin b × Fin b ↦
        (cyclotomicGp (j g) ^ (-k i.1)).val • j g • T⁻¹.val.uncurry i) = 0 := by
    filter_upwards [h_entries, h_near] with g h_eq h_zero using by rwa [← h_eq]
  -- `convert`: the entries of the cocharacter matrix `diagonal (LaurentPolynomial.T ∘ k)` times
  -- `T⁻¹` appear only after the matrix product is expanded inside `aeval`.
  convert aeval_cocharacter_eq_zero (fun i : Fin b × Fin b ↦ k i.1) T⁻¹.val.uncurry G
    (nhds_one_le_map_nearOne _ h_twisted)
  simp [Function.uncurry]

/-- One representation from one for each embedding. Let `P w` be monic of degree `a` along the
filter `mostFrobenii E` (each nonempty open set of the Galois group has a nonempty open part whose
Frobenii have the property at almost all places).
Let the `a` jumps of `κ` at `ε` be free integers `e i` (`HasNoSmallRelations`), with
the place of `ε` in `F`. Suppose that for each embedding `τ₀` some continuous `ρ`, eventually along
those places and `F`, satisfies `IsSphericalAbove` with `OccursIn`: it is good above `w`, the jumps
of `κ` at `τ₀` occur in `ρ`, and `P w` kills its geometric Frobenii. Then one continuous `r` of rank
`a` has characteristic polynomial `P w` along `mostFrobenii E` and, eventually along `F`, exactly
the jumps of `κ`. -/
lemma New.GaloisRep.exists_galRep_charpoly_eq_of_forall_embedding {ℓ : ℕ} {E : Type} {a : ℕ}
    [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [NeZero a] (κ : Weight E)
    {P : FinPlace E → Polynomial (PadicAlgCl ℓ)}
    (h_monic : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      ↑ℓ ∉ y.place.asIdeal ∧ (P y.place).IsMonicOfDegree a)
    {ε : Ω →+* PadicAlgCl ℓ} {e : Fin a → ℤ} (he_free : HasNoSmallRelations e)
    (he_jumps : ∀ i : Fin a, e i ∈ jumps κ a (RingHom.comp ιℓ.symm (ε.comp (algebraMap E Ω))))
    {F : Filter (FinPlace E)} (hF : pure (placeOfEmb (ε.comp (algebraMap E Ω))) ≤ F)
    (h_one : ∀ τ₀ : E →+* ℂ, ∃ ρ : PadicRep Gal(Ω/E) ℓ,
      Continuous ρ.rep ∧
      ∀ᶠ w : FinPlace E in (mostFrobenii E).map (fun y : FrobeniusDatum E ↦ y.place) ⊔ F,
        IsSphericalAbove ρ.rep OccursIn (Set.indicator {τ₀} (jumps κ a)) w (P w)) :
    ∃ r : GalRep ℓ E (Fin a),
      Continuous r ∧
      (∀ᶠ y : FrobeniusDatum E in mostFrobenii E, (r y.frob).val.charpoly = P y.place) ∧
      ∀ᶠ w : FinPlace E in F, IsSphericalAbove r Eq (jumps κ a) w (P w) := by
  obtain ⟨b, r, hr, h_diag, h_frob, h_F⟩ := exists_rep_span_diagonal _ (jumps κ a) P h_one
  -- At the place of `ε`, which `F` contains: `r` is good there and the jumps of `κ` occur.
  obtain ⟨h_good, h_jump, -⟩ := Filter.eventually_pure.mp (hF h_F) (isPlaceOver_placeOfEmb ε)
  have h_kill : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      (P y.place).aeval (r y.frob).val = 0 ∧ (P y.place).IsMonicOfDegree a := by
    filter_upwards [h_frob, h_monic] with y h_sph ⟨hyℓ, hy⟩
    obtain ⟨-, -, h_kills⟩ := h_sph y.isPlaceOver
    exact ⟨(h_kills _ y.isFrob_inv).left (y.isPlaceOver.valuation_natCast_eq_one_iff.mpr hyℓ), hy⟩
  obtain ⟨h_card, h_charpoly⟩ := card_eq_and_eventually_charpoly_eq_of_hasNoSmallRelations κ r hr
    h_diag h_kill he_free he_jumps h_good h_jump
  obtain rfl : a = b := by simpa using h_card.symm
  refine ⟨r, hr, h_charpoly, Filter.Eventually.mono h_F fun w hw A hA ↦ ?_⟩
  obtain ⟨h_good', h_occ, h_poly⟩ := hw hA
  refine ⟨h_good', fun L γ g hγ u ↦ ?_, h_poly⟩
  -- The `a` distinct jumps of `κ` occur among the jumps of `r`, of which there are only `a`.
  obtain ⟨K, hK_card, hK⟩ := h_good'.right.isPotentiallyCrystalline.exists_hasJumps γ
  let σ : E →+* PadicAlgCl ℓ := .comp ↑g⁻¹ (L.e.comp (algebraMap E Ω))
  have h_le : jumps κ a (RingHom.comp ιℓ.symm σ) ≤ K :=
    (Multiset.le_iff_subset (κ.nodup_jumps ..)).mpr fun z ↦ by
      simpa [hK _, OccursIn] using h_occ hγ z
  have h_card_le : K.card ≤ (jumps κ a (RingHom.comp ιℓ.symm σ)).card := by simp [hK_card, jumps]
  rw [hK, Multiset.eq_of_le_of_card_le h_le h_card_le]

/-- The submonoid of the integers of `E` that lie in no place `u` with `G u` is disjoint from the
place `w` exactly when `G w` holds. -/
lemma New.GaloisRep.disjoint_iInf_primeCompl_iff {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : FinPlace E → Prop) (w : FinPlace E) :
    Disjoint (⨅ (u : FinPlace E) (_ : G u), u.asIdeal.primeCompl : Submonoid (𝓞 E)).carrier
        w.asIdeal ↔ G w := by
  -- An element `y` lying in `w` and in no other place is such an integer unless `G w` holds.
  -- It is a level with prescribed places `{w}`, for the whole group and the integer `N = 1`.
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, ∀ u : FinPlace E, y ∈ u.asIdeal ↔ u = w := by
    obtain ⟨y, -, hy_mem, -⟩ :=
      exists_levelGU_invTransposeGL_le (n := Unit) isOpen_univ le_top (S := {w})
        (fun u hu ↦ Or.inl hu) 1
    exact ⟨y, by simpa [Ideal.one_notMem] using hy_mem⟩
  simp only [Set.disjoint_left, Submonoid.mem_carrier, SetLike.mem_coe, Submonoid.mem_iInf,
    Ideal.mem_primeCompl_iff]
  refine ⟨fun h_disj ↦ ?_, fun hG_w z hz ↦ hz w hG_w⟩
  by_contra hG_w
  exact h_disj (fun u hu hyu ↦ hG_w ((hy u).1 hyu ▸ hu)) ((hy w).2 rfl)

/-- Let `ψ ≠ 0` lie in `definiteForms 𝔑 ξ`, with `𝔑 ≠ 0`, and let the ideles `x` of `QuadField d`
act on `ψ` through the central scalars by `ω x` (`hψ_cen`). Let the scalar matrix of `x̄`, for `x`
in `(QuadField d)ˣ`, act in `ξ` by `∏ s, s x ^ (-A s)` (`hξ_centre`). Then `(ω, A)` is an algebraic
Hecke character of `QuadField d` (a member of `algHeckeChars`), and its base change to `E` is
unramified at every place `w` with `IsSafe 𝔑 w`. -/
lemma New.GaloisRep.centralChar_mem_algHeckeChars_and_charUnramifiedAt {E : Type} [Field E]
    [CMBase E]
    [EmbeddedNumberField E] {d : ℕ} [HasQuadSubfield d E] {n W : Type} [Fintype n] [DecidableEq n]
    [Nonempty n] [AddCommGroup W] [Module ℂ W] {ξ : Representation ℂ (GL n E) W} {𝔑 : 𝓞 E}
    (h𝔑 : 𝔑 ≠ 0) {ψ : GL n (𝔸f E) → W} (hψ_mem : ψ ∈ Variety.definiteForms 𝔑 ξ) (hψ_ne : ψ ≠ 0)
    {ω : (𝔸f (QuadField d))ˣ →* ℂ}
    (hψ_cen : ∀ x : (𝔸f (QuadField d))ˣ,
      rightRegular ℂ (GL n (𝔸f E)) W (centralScalar x) ψ = ω x • ψ)
    {A : (QuadField d →+* ℂ) → ℤ}
    (hξ_centre : ∀ x : (QuadField d)ˣ,
      ξ (GeneralLinearGroup.scalar n (star (x.map (algebraMap (QuadField d) E)))) =
        (∏ s : QuadField d →+* ℂ, s x ^ (-A s)) • 1) :
    ∃ hω : (ω.toHomUnits, Multiplicative.ofAdd A) ∈ algHeckeChars (QuadField d), ∀ w : FinPlace E,
      IsSafe 𝔑 w →
      New.CharUnramifiedAt (AlgHeckeChar.baseChange (E := E)
        ⟨(ω.toHomUnits, Multiplicative.ofAdd A), hω⟩).val.1 w := by
  have hω_eq {x : (𝔸f (QuadField d))ˣ} {c : ℂ}
      (h : rightRegular ℂ (GL n (𝔸f E)) W (centralScalar x) ψ = c • ψ) : ω x = c :=
    smul_left_injective ℂ hψ_ne ((hψ_cen x).symm.trans h)
  obtain ⟨⟨hψ_rat, -⟩, hψ_level⟩ := hψ_mem
  have hω_level (x : (𝔸f (QuadField d))ˣ) (hx : centralScalar x ∈ levelGU n 𝔑) :
      ω.toHomUnits x = 1 := Units.ext (hω_eq (hψ_level ⟨centralScalar x, hx⟩))
  refine ⟨⟨?_, fun x ↦ hω_eq (funext fun y ↦ ?_)⟩, fun w hw x hx ↦ hω_level _ ?_⟩
  · -- The kernel contains the ideles whose central scalar has level `𝔑`, an open subgroup.
    refine isOpen_mono (fun x hx ↦ hω_level x ⟨mem_GU_centralScalar x, mem_comap.mp hx⟩)
      ((Variety.isOpen_congruenceGL_span h𝔑).preimage (.of_coeHom_comp <| .matrix_diagonal ?_))
    simp only [Pi.constRingHom_eq_algebraMap, toMonoidHom_eq_coe, Units.coe_map,
      MonoidHom.coe_ofClass, coe_comp, Function.comp_apply, starRingEnd_apply,
      algebraMap_star_comm, continuous_fun_star_iff]
    fun_prop
  · -- On `(QuadField d)ˣ` the central scalar is rational, so it acts through `ξ`.
    let z : GL n E := .scalar n (star (x.map (algebraMap (QuadField d) E)))
    have hz : centralScalar (principalIdele x) = toFinGL z := by
      simp [z, Units.ext_iff, starRingEnd_apply]
    calc ψ (y * centralScalar (principalIdele x))
        = ψ (centralScalar (principalIdele x) * y) := congrArg ψ (commute_scalar_GL ..)
      _ = ξ z (ψ y) := by rw [hz, hψ_rat z y]
      _ = _ := by simp [z, hξ_centre]
  · -- The norm of a local unit at `w` gives an integral scalar, trivial at the places of `𝔑`.
    obtain ⟨-, -, hw_conj⟩ := hw
    refine mem_levelGU_of_map_evalAt_eq (mem_GU_centralScalar _) ?_ fun u hu ↦
      ⟨1, by simpa using evalAt_centralScalar_of_ne (hw_conj u · hu) x⟩
    have h_unit : locIdele w x ∈ (Ô E).units :=
      idelesUnitOff_empty.le (locIdele_mem_idelesUnitOff hx)
    simpa [mem_intGL, ← map_inv, ite_mem, diagonal, star_eq_adeleMap, starRingEnd_apply] using
      h_unit.imp adeleNorm_mem_Ô adeleNorm_mem_Ô

open Classical in
/-- The place `w₁` together with the places `u` of `S` or conjugate to a place of `S` such that
the conjugate of the place of `QuadField d` below `u` is neither the place below `w₀` nor the
place below `w'`. The seed construction takes a level that lies exactly in these places and in the
places that contain an integer `N`. -/
private noncomputable def New.GaloisRep.levelPlaces {E : Type} [Field E] [NumberField E]
    [IsCMField E] (d : ℕ) [HasQuadSubfield d E] (S : Finset (FinPlace E)) (w₀ w₁ w' : FinPlace E) :
    Finset (FinPlace E) :=
  insert w₁ {u ∈ S ∪ S.image star |
    star (u.below (QuadField d)) ∉ [w₀.below (QuadField d), w'.below (QuadField d)]}

open Classical in
/-- Each place in `insert w₁ S` or its conjugate lies in `levelPlaces d S w₀ w₁ w'`, written out:
`w₁` together with the places `u` of `S` or conjugate to a place of `S` such that the conjugate
of the place below `u` is neither the place below `w₀` nor the place below `w'`. The reason: the
places below `w₀` and `w'` are split and not conjugate to each other, since the place below `w₀`
contains `ℓ` (as `v`, the place of `ε`, does), hence so does its conjugate, and then `hw'`
applies. -/
private lemma New.GaloisRep.mem_or_star_mem_insert_filter_of_isSplitPrimeToDisc {ℓ : ℕ} {E : Type}
    {d : ℕ} [ThePrime ℓ] [Field E] [CMType E] [EmbeddedNumberField E]
    [HasQuadSubfield d E] {S : Finset (FinPlace E)} {w₀ w₁ v w' : FinPlace E}
    (hw₀_split : IsSplitPrimeToDisc (w₀.below (QuadField d)))
    (hw' : IsSplitPrimeToDisc (w'.below (QuadField d)) ∧
      (↑ℓ ∈ w'.asIdeal → w'.below (QuadField d) = w₀.below (QuadField d)))
    (hv : v ∉ S ∧ star v ∉ S ∧ v.below (QuadField d) = w₀.below (QuadField d))
    {ε : Ω →+* PadicAlgCl ℓ} (hε : placeOfEmb (ε.comp (algebraMap E Ω)) = v) :
    ∀ w ∈ insert w₁ S,
      w ∈ insert w₁ {u ∈ S ∪ S.image star |
          star (u.below (QuadField d)) ∉ [w₀.below (QuadField d), w'.below (QuadField d)]} ∨
        star w ∈ insert w₁ {u ∈ S ∪ S.image star |
          star (u.below (QuadField d)) ∉ [w₀.below (QuadField d), w'.below (QuadField d)]} := by
  have mem_below {n : ℕ} (w : FinPlace E) : ↑n ∈ w.1 ↔ ↑n ∈ (w.below (QuadField d)).1 := by simp
  grind [IsSplitPrimeToDisc.isSplit_and_prime_q, natCast_mem_placeOfEmb, below_star,
    mem_star_place, star_natCast]

/-- Rational unitary matrices act on a form through its coefficient system. Let `f` be a form of
weight `κ` on the unitary group, and let `ξ y` be the action of `ȳ` in weight `κ` for unitary `y`
(`hξ`). Then every rational unitary `y` acts on `f` by left translation by
`embFin (entryConj y)`, whose inverse transpose is `toFinGL y`. -/
private lemma New.GaloisRep.exists_apply_mul_eq_of_mem_unitary {E : Type} [Field E] [CMType E]
    {a : ℕ} {κ : Weight E} {f : Gf E (Fin a) → WeylIndex (Fin a) κ.1 → ℂ}
    (hf : f ∈ (stdSpace E (Fin a)).forms κ)
    {ξ : Representation ℂ (GL (Fin a) E) (WeylIndex (Fin a) κ.1 → ℂ)}
    (hξ : ∀ y : U (1 : Matrix (Fin a) (Fin a) E),
      (stdSpace E (Fin a)).weightRep κ.1 κ.2 (entryConj y) = ξ y.val)
    (y : GL (Fin a) E) (hy : y ∈ U (1 : Matrix (Fin a) (Fin a) E)) :
    ∃ c : Gf E (Fin a),
      (∀ u : Gf E (Fin a), f (c * u) = ξ y (f u)) ∧ invTransposeGL c.val = toFinGL y := by
  refine ⟨(stdSpace E (Fin a)).embFin (entryConj ⟨y, hy⟩), fun u ↦ ?_, ?_⟩
  · simpa [hξ] using hf.right (entryConj ⟨y, hy⟩) u
  · -- the form `(stdSpace E (Fin a)).J` of the standard space is `1` only by unfolding
    refine (congrArg invTransposeGL (stdSpace_embFin ..)).trans ?_
    rfl

/-- An embedding `s` of `E` that induces a safe place `w` (`IsSafe 𝔑 w`) restricts on `QuadField d`
to the embedding given by `ε`, if `𝔑 ∈ w₀` and `v`, the place of `ε`, lies over the same place of
`QuadField d` as `w₀`. Otherwise `s` restricts to its conjugate, and `w₀` would lie above the
conjugate of the place below `w`, which a safe place forbids. -/
private lemma New.GaloisRep.comp_algebraMap_eq_of_isSafe {ℓ : ℕ} {E : Type} {d : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    {𝔑 : 𝓞 E} {w w₀ v : FinPlace E} (hw : IsSafe 𝔑 w)
    (h𝔑_w₀ : 𝔑 ∈ w₀.asIdeal)
    (hv_below : v.below (QuadField d) = w₀.below (QuadField d)) {ε : Ω →+* PadicAlgCl ℓ}
    (hε : placeOfEmb (ε.comp (algebraMap E Ω)) = v) {s : E →+* ℂ} (hs : inducedPrime s = w) :
    s.comp (algebraMap (QuadField d) E) =
      (ιℓ.symm.toRingHom.comp (ε.comp (algebraMap E Ω))).comp (algebraMap (QuadField d) E) := by
  -- `QuadField d` has one infinite place, so `s` restricts to the embedding of `ε` or to its
  -- conjugate.
  obtain ⟨-, -, hw_conj⟩ := hw
  refine (InfinitePlace.mk_eq_iff.mp (by subsingleton)).resolve_right fun h ↦ hw_conj w₀ ?_ h𝔑_w₀
  ext x
  -- `x` lies in a place exactly when its image has norm below `1`; compare the two embeddings.
  simpa [← hv_below, ← hs, ← hε, map_star_CM] using
    congrArg (fun z : ℂ ↦ ‖ιℓ z‖ < 1) (RingHom.congr_fun h x).symm

open Classical in
/-- Galois representations from the cohomology of a PEL model: for PEL data `D` with neat level,
`D.β = betaK d`, good at the safe places, a safe place `v`, and a multiset `J` of nonnegative
integers each occurring in weight `ν + 1` for `θ`, some continuous representation satisfies
`IsSphericalAbove` at every safe place `w`: the members of `J` occur among its jumps at the
embedding `algebraMap E ℂ`, with no condition at the other embeddings, and the Hecke polynomial of
`ιℓ ∘ θ w` kills its geometric Frobenius elements. The model lives over the localisation at the
integers that lie in no safe place. -/
private lemma New.GaloisRep.exists_padicRep_of_pel {ℓ : ℕ} {E : Type} {d : ℕ}
    [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMBase E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    {D : PEL E} [NeZero D.rank] (h_neat : IsNeat (Fin D.rank) D.level)
    (hD_β : D.β = algebraMap (𝓞 (QuadField d)) (𝓞 E) (QuadField.betaK d))
    (hD_good : ∀ w : FinPlace E, IsSafe D.level w → D.IsGoodAt w.asIdeal) {v : FinPlace E}
    (hv_safe : IsSafe D.level v) (ν : ℕ) (θ : SafePlace D.level → ℕ → ℂ) (J : Multiset ℤ)
    (hJ_nonneg : ∀ u ∈ J, 0 ≤ u)
    (hJ_occurs : ∀ h : ℕ, (h : ℤ) ∈ J → OccursInWeight D.rank ν.succ θ h) :
    ∃ ρ : PadicRep Gal(Ω/E) ℓ,
      Continuous ρ.rep ∧
      ∀ w : SafePlace D.level,
        IsSphericalAbove ρ.rep OccursIn
          (fun τ : E →+* ℂ ↦ if algebraMap E ℂ = τ then J else 0) w.val.val
          (heckePoly w.val.val.q D.rank fun j : ℕ ↦ ιℓ (θ w j)) := by
  -- The base ring `R` of the model: the safe places are exactly the places that survive in `R`.
  let M : Submonoid (𝓞 E) := ⨅ (w : FinPlace E) (_ : IsSafe D.level w), w.asIdeal.primeCompl
  have hM (w : FinPlace E) : Disjoint M.carrier w.asIdeal ↔ IsSafe D.level w :=
    disjoint_iInf_primeCompl_iff (IsSafe D.level) w
  have hM_le : M ≤ nonZeroDivisors (𝓞 E) :=
    iInf₂_le_of_le v hv_safe v.asIdeal.primeCompl_le_nonZeroDivisors
  let R := Localization.subalgebra E M hM_le
  -- `R` is not a field, as `v` extends to a nonzero proper ideal; so maximal ideals are nonzero
  -- and lie over safe places.
  have hR_field : ¬IsField R := Ring.not_isField_of_ne_of_ne (Ideal.map_ne_bot_of_ne_bot v.ne_bot)
    ((map_algebraMap_ne_top_iff_disjoint ..).mpr ((hM v).mpr hv_safe))
  have hR (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) : D.IsGoodAt (𝔪.comap (algebraMap _ R)) :=
    hD_good _ ((hM ⟨_, .comap _, (bot_lt_under_prime M R hM_le 𝔪
      (𝔪.bot_lt_of_maximal hR_field).ne').ne'⟩).mp ((disjoint_under_iff ..).mpr h𝔪.ne_top))
  obtain ⟨X⟩ :=
    exists_model (ThetaNull.nonempty_universalFamily hM_le hR).some h_neat hD_β hD_good ν.succ
  exact X.exists_galois_rep h_neat M iInf₂_le θ J hJ_nonneg hJ_occurs

open Classical in
/-- The level `𝔑` is prime to the places the local conditions ask for: if `𝔑` lies exactly in the
places containing `N` and those of `levelPlaces d S w₀ w₁ w'`, `N` is prime to `w₀` and `w'`, and
`w₁` is split and far from `w'`, `S` and `N`, `w₀ ∈ S`, `w₀` and `w'` lie over places with
`IsSplitPrimeToDisc`, `v` and `star v` lie outside `S` with `v` over the place below `w₀`, and `w'`
lies over that place too if `ℓ ∈ w'`, then `v`, and `w'` if `w'` and `star w'` lie outside `S`, are
safe, `𝔑 ∉ star w₀`, and `𝔑` lies in `w₁` but not in `star w₁`. -/
private lemma New.GaloisRep.isSafe_and_mem_of_mem_iff {ℓ : ℕ} {E : Type} {d : ℕ}
    [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    {S : Finset (FinPlace E)} {w₀ w₁ v w' : FinPlace E} {N : ℕ+} {𝔑 : 𝓞 E}
    (h𝔑_mem : ∀ w : FinPlace E,
      𝔑 ∈ w.asIdeal ↔ ((N : ℕ) : 𝓞 E) ∈ w.asIdeal ∨ w ∈ levelPlaces d S w₀ w₁ w')
    (hN : ∀ w ∈ ({w₀, w'} : Finset (FinPlace E)), ((N : ℕ) : 𝓞 E) ∉ w.asIdeal) (hS : w₀ ∈ S)
    (hw₀_split : IsSplitPrimeToDisc (w₀.below (QuadField d)))
    (hv : v ∉ S ∧ star v ∉ S ∧ v.below (QuadField d) = w₀.below (QuadField d))
    (hw' : IsSplitPrimeToDisc (w'.below (QuadField d)) ∧
      (↑ℓ ∈ w'.asIdeal → w'.below (QuadField d) = w₀.below (QuadField d)))
    (hw₁ : w₁.IsSplit)
    (hw₁_far : w₁.below (QuadField d) ∉ (insert w' S).image (FinPlace.below (QuadField d)) ∧
      star (w₁.below (QuadField d)) ∉ (insert w' S).image (FinPlace.below (QuadField d)) ∧
      ((N : ℕ) : 𝓞 (QuadField d)) ∉ (w₁.below (QuadField d)).asIdeal) :
    (∀ᶠ w : FinPlace E in
      pure v ⊔ Filter.principal {w : FinPlace E | w' = w ∧ w' ∉ S ∧ star w' ∉ S}, IsSafe 𝔑 w) ∧
    𝔑 ∉ (star w₀).asIdeal ∧ 𝔑 ∈ w₁.asIdeal ∧ 𝔑 ∉ (star w₁).asIdeal := by
  have mem_below {n : ℕ} (w : FinPlace E) : ↑n ∈ w.1 ↔ ↑n ∈ (w.below (QuadField d)).1 := by simp
  simp [IsSafe, h𝔑_mem, levelPlaces]
  grind -ring -linarith [star_star, below_star, mem_star_place, star_natCast]

open Classical in
/-- A place `u` of `E` is safe for `𝔑` (`IsSafe`) if the place below it satisfies
`IsSplitPrimeToDisc`, neither that place nor its conjugate lies below `w₁` or below a place of `S`,
and it is prime to `N`; here `𝔑` lies exactly in the places that contain `N` and in those of
`levelPlaces d S w₀ w₁ w'`. -/
private lemma New.GaloisRep.isSafe_of_notMem_image_below {E : Type} {d : ℕ}
    [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    {S : Finset (FinPlace E)} {w₀ w₁ w' u : FinPlace E} {N : ℕ+} {𝔑 : 𝓞 E}
    (h𝔑_mem : ∀ w : FinPlace E,
      𝔑 ∈ w.asIdeal ↔ ((N : ℕ) : 𝓞 E) ∈ w.asIdeal ∨ w ∈ levelPlaces d S w₀ w₁ w')
    (hu_split : IsSplitPrimeToDisc (u.below (QuadField d)))
    (hu_far : u.below (QuadField d) ∉ (insert w₁ S).image (FinPlace.below (QuadField d)) ∧
      star (u.below (QuadField d)) ∉ (insert w₁ S).image (FinPlace.below (QuadField d)) ∧
      ((N : ℕ) : 𝓞 (QuadField d)) ∉ (u.below (QuadField d)).asIdeal) :
    IsSafe 𝔑 u := by
  have mem_below {n : ℕ} (w : FinPlace E) : ↑n ∈ w.1 ↔ ↑n ∈ (w.below (QuadField d)).1 := by simp
  simp [IsSafe, h𝔑_mem, levelPlaces]
  grind -ring -linarith [star_star, below_star, mem_star_place, star_natCast]

open Classical in
/-- A place `w` that is safe for `𝔑` (`IsSafe`) lies outside `S`, and so does its conjugate, and
`𝔑` lies in `w₀`. Here `𝔑` lies exactly in the places that contain `N` and in those of
`levelPlaces d S w₀ w₁ w'`, each place of `insert w₁ S` or its conjugate lies in that set
(`h_cover`), `w₀ ∈ S`, and `𝔑` is prime to the conjugate of `w₀`. -/
private lemma New.GaloisRep.mem_and_notMem_of_isSafe {E : Type} {d : ℕ}
    [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    {S : Finset (FinPlace E)} {w₀ w₁ w' : FinPlace E} {N : ℕ+} {𝔑 : 𝓞 E}
    (h𝔑_mem : ∀ w : FinPlace E,
      𝔑 ∈ w.asIdeal ↔ ((N : ℕ) : 𝓞 E) ∈ w.asIdeal ∨ w ∈ levelPlaces d S w₀ w₁ w')
    (h_cover : ∀ w ∈ insert w₁ S, w ∈ levelPlaces d S w₀ w₁ w' ∨ star w ∈ levelPlaces d S w₀ w₁ w')
    (hS : w₀ ∈ S) (h𝔑 : 𝔑 ∉ (star w₀).asIdeal ∧ 𝔑 ∈ w₁.asIdeal ∧ 𝔑 ∉ (star w₁).asIdeal)
    (w : FinPlace E) : IsSafe 𝔑 w → 𝔑 ∈ w₀.asIdeal ∧ w ∉ S ∧ star w ∉ S := by
  grind [levelPlaces, IsSafe, star_star, below_star]

open Classical in
/-- A principal level inside the stabiliser of `f`: if `f` has an open stabiliser and is fixed by
the integral points trivial at `S ∋ w₀`, and each place of `insert w₁ S` or its conjugate lies in
`levelPlaces d S w₀ w₁ w'`, then some multiple `𝔑` of `N` lies exactly in the places containing `N`
and those of that set, and each `u` whose inverse transpose lies in `levelGU (Fin a) 𝔑` fixes `f`,
is `≡ 1` modulo `w₀` and lies in `proIwahori` at `w₁`. -/
private lemma New.GaloisRep.exists_levelGU_le_rightStabilizer {E : Type} {d : ℕ}
    [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    {a : ℕ} {W : Type} {f : Gf E (Fin a) → W → ℂ}
    (hf_open : IsOpen ((rightStabilizer f : Subgroup (Gf E (Fin a))) : Set (Gf E (Fin a))))
    {S : Finset (FinPlace E)} (hf_off : ∀ k ∈ stdLevel E (Fin a) ⊓ Gf.trivialOn (Fin a) S,
      rightRegular ℂ (Gf E (Fin a)) (W → ℂ) k f = f)
    {w₀ w₁ w' : FinPlace E} (hS : w₀ ∈ S)
    (h_cover : ∀ w ∈ insert w₁ S, w ∈ levelPlaces d S w₀ w₁ w' ∨ star w ∈ levelPlaces d S w₀ w₁ w')
    (N : ℕ+) :
    ∃ 𝔑 : 𝓞 E, ((N : ℕ) : 𝓞 E) ∣ 𝔑 ∧
      (∀ w : FinPlace E, 𝔑 ∈ w.asIdeal ↔ ((N : ℕ) : 𝓞 E) ∈ w.asIdeal ∨
        w ∈ levelPlaces d S w₀ w₁ w') ∧
      ∀ u : Gf E (Fin a), invTransposeGL u.val ∈ levelGU (Fin a) 𝔑 →
        u ∈ rightStabilizer f ∧ Gf.atPlace w₀ u ∈ localCongruence (Fin a) w₀ 0 ∧
          Gf.atPlace w₁ u ∈ proIwahori := by
  let H : OpenSubgroup (Gf E (Fin a)) := ⟨rightStabilizer f, hf_open⟩ ⊓
    (.comap _ (continuous_atPlace w₀) ⟨localCongruence _ _ 0, isOpen_localCongruence⟩ ⊓
      .comap _ (continuous_atPlace w₁) ⟨proIwahori, isOpen_proIwahori⟩)
  have hH : stdLevel E _ ⊓ Gf.trivialOn _ ↑(insert w₁ S) ≤ H.toSubgroup := fun k hk ↦
    ⟨congrFun (hf_off k (hk.imp_right (by simp))), by simp [mem_trivialOn.mp hk.2, hS]⟩
  exact exists_levelGU_invTransposeGL_le H.isOpen' hH h_cover N

/-- At a safe place `w`, the Hecke element `heckeSum` of index `j` acts on `ψ` by the eigenvalue
`t w j` of `f` (`ht_eig`) times `ω` of the inverse of `uniformizerNorm w ^ j`: the linear maps `L`,
with `L w hw f = ψ`, carry the local Hecke operator over from `f` (`hL`), and the central scalar
acts through `ω` (`hψ_cen`). -/
private lemma New.GaloisRep.asAlgebraHom_heckeSum_eq_smul {E : Type} {d : ℕ} [Field E] [CMBase E]
    [EmbeddedNumberField E] [HasQuadSubfield d E] {n W : Type} [Fintype n] [DecidableEq n]
    [AddCommGroup W] [Module ℂ W] {𝔑 : 𝓞 E} {f : Gf E n → W}
    {ξ : Representation ℂ (GL n E) W} {ψ : GL n (𝔸f E) → W}
    (hψ_mem : ψ ∈ Variety.definiteForms 𝔑 ξ) {ω : (𝔸f (QuadField d))ˣ →* ℂ}
    (hψ_cen : ∀ x : (𝔸f (QuadField d))ˣ,
      rightRegular ℂ (GL n (𝔸f E)) W (centralScalar x) ψ = ω x • ψ)
    (L : (w : SplitFinPlace E) → 𝔑 ∉ (star w.val).asIdeal → (Gf E n → W) →ₗ[ℂ] GL n (𝔸f E) → W)
    (hL : ∀ (w : SplitFinPlace E) (hw : 𝔑 ∉ (star w.val).asIdeal)
      (g : GL n (LocField (w : FinPlace E))),
      rightRegular ℂ (GL n (𝔸f E)) W (conjAtSplit w g) ψ =
        L w hw (rightRegular ℂ (Gf E n) W (ofSplitPlace w.prop g) f))
    {t : SafePlace 𝔑 → ℕ → ℂ}
    (ht_eig : ∀ (w : SafePlace 𝔑) (j : ℕ),
      heckeSplit (rightRegular ℂ (Gf E n) W) w.val.prop j f = t w j • f)
    (w : SafePlace 𝔑) (j : ℕ) :
    (rightRegular ℂ (GL n (𝔸f E)) W).asAlgebraHom (heckeSum n ℂ w.val j) ψ =
      (t w j * (ω (uniformizerNorm w.val))⁻¹ ^ j) • ψ := by
  obtain ⟨-, -, hw_conj⟩ := w.prop
  have hw : 𝔑 ∉ (star w.val.val).asIdeal := hw_conj _ (below_star ..)
  have hL_f : L _ hw f = ψ := by simpa using (hL _ hw 1).symm
  let π := (rightRegular ℂ (GL n (𝔸f E)) W).comp (conjAtSplit w.val)
  have h_equiv (g : GL n (LocField (w.val : FinPlace E))) :
      L _ hw (((rightRegular ℂ (Gf E n) W).comp (ofSplitPlace w.val.prop)) g f) =
        π g (L _ hw f) := by
    simpa [hL_f, π] using (hL _ hw g).symm
  -- `L` intertwines the local actions on `f` and `ψ`, hence the Hecke operators.
  have h_eig : heckeGL π j ψ = t w j • ψ :=
    calc heckeGL π j ψ = heckeGL π j (L _ hw f) := by rw [hL_f]
      _ = L _ hw (heckeSplit (rightRegular ℂ (Gf E n) W) w.val.prop j f) :=
        (map_heckeFun _ (isHeckeFunction_basicDoubleCoset j).1 h_equiv).symm
      _ = t w j • ψ := by rw [ht_eig, map_smul, hL_f]
  -- `heckeSum` at `(w, j)` is the `j`-th Hecke operator at `w`, then a central scalar.
  rw [asAlgebraHom_heckeSum (w, j) hψ_mem.right, h_eig, map_smul, hψ_cen]
  simp [smul_smul]

/-- The representation for one embedding. Under the hypotheses of
`New.GaloisRep.exists_rep_of_cuspidal_type` other than the free jumps, for each complex embedding
`τ₀` of `E` some continuous representation satisfies `IsSphericalAbove` at the places of the
Frobenius data along `mostFrobenii E`, at `v`, and at `w'` if `w'` and its conjugate are outside
`S`: the jumps of `κ` at `τ₀` occur among its jumps, with no condition at the other embeddings, and
`ιℓ (P w)` kills its Frobenius elements. -/
private lemma New.GaloisRep.exists_padicRep_of_cuspidal_type_at_embedding {ℓ : ℕ} {E : Type}
    {a d : ℕ} [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E]
    [HasQuadSubfield d E] [HasPrimitiveRoot5040 E]
    (ha : Odd a) {κ : Weight E} {f : Gf E (Fin a) → WeylIndex (Fin a) κ.1 → ℂ}
    (hf : f ∈ (stdSpace E (Fin a)).forms κ) {S : Finset (FinPlace E)}
    {P : FinPlace E → Polynomial ℂ} (hP : IsSphericalOff S f P) {w₀ v : FinPlace E} (hS : w₀ ∈ S)
    (hw₀_split : IsSplitPrimeToDisc (w₀.below (QuadField d)))
    {χ : localCongruence (Fin a) w₀ 0 →* ℂ}
    (hχ_type : IsCuspidalType (localCongruence (Fin a) w₀ 0) χ)
    (hχ : ∀ j : localCongruence (Fin a) w₀ 0,
      rightRegular ℂ (Gf E (Fin a)) (WeylIndex (Fin a) κ.1 → ℂ)
        (ofSplitPlace hw₀_split.isSplit_of_below j.val) f = χ j • f)
    (hv : v ∉ S ∧ star v ∉ S ∧ v.below (QuadField d) = w₀.below (QuadField d))
    {ε : Ω →+* PadicAlgCl ℓ} (hε : placeOfEmb (ε.comp (algebraMap E Ω)) = v) (w' : FinPlace E)
    (hw' : IsSplitPrimeToDisc (w'.below (QuadField d)) ∧
      (↑ℓ ∈ w'.asIdeal → w'.below (QuadField d) = w₀.below (QuadField d))) (τ₀ : E →+* ℂ) :
    ∃ ρ : PadicRep Gal(Ω/E) ℓ,
      Continuous ρ.rep ∧
      ∀ᶠ w : FinPlace E in (mostFrobenii E).map (fun y : FrobeniusDatum E ↦ y.place) ⊔
          (pure v ⊔ Filter.principal {w : FinPlace E | w' = w ∧ w' ∉ S ∧ star w' ∉ S}),
        IsSphericalAbove ρ.rep OccursIn (Set.indicator {τ₀} (jumps κ a)) w ((P w).map ιℓ) := by
  classical
  have : NeZero a := .of_pos ha.pos
  obtain ⟨hf_ne, hf_off, h_eig⟩ := hP
  let s₀ : QuadField d →+* ℂ :=
    (ιℓ.symm.toRingHom.comp (ε.comp (algebraMap E Ω))).comp (algebraMap (QuadField d) E)
  -- `ξ` extends the weight `κ` to `GL (Fin a) E`, with central exponents `A₀` and `A₀ s₀ = μ`; by
  -- `h_occurs`, the eigenvalues of a test eigenform occur in weight `z + μ` for each jump `z` at
  -- an embedding over `s₀`.
  obtain ⟨ξ, μ, m, A₀, hμ, hξ, hξ_centre, h_nonneg, h_occurs⟩ :=
    exists_isCoefficientSystem ha (algebraMap (QuadField d) E) s₀ κ
  -- A second CM type `Ψ`, whose embedding `Ψ.Φ Ψ.v₀` at its distinguished place is `τ₀` (`hv₀`) and
  -- whose other embeddings differ from `τ₀` on `QuadField d` (`hΨ`), and PEL data at every nonzero
  -- level divisible by `N`, which lies in neither `w₀` nor `w'`.
  obtain ⟨Ψ, ⟨hv₀, hΨ⟩, N, hN, h_model⟩ := exists_pel a τ₀ {w₀, w'}
  -- An auxiliary split place `w₁`, away from `S`, `w'` and `N`, makes the level neat.
  have h_far (w : FinPlace E) : ∀ᶠ x : FinPlace E in .cofinite, (x ∉ S ∧ star x ∉ S ∧ ↑d ∉ x.1) ∧
      x.below (QuadField d) ∉ (insert w S).image (.below _) ∧
      star (x.below (QuadField d)) ∉ (insert w S).image (.below _) ∧ ↑(N : ℕ) ∉ (x.below _).1 :=
    (eventually_notMem_star_notMem d S).and
      ((tendsto_place_comap_cofinite (algebraMap ..)).eventually (eventually_notMem_star_notMem ..))
  obtain ⟨w₁, hw₁, ⟨⟨hw₁S, hw₁S', -⟩, hw₁_far⟩, h_neat⟩ :=
    ((frequently_prime_q.mono fun _ ↦ isSplit_of_q_prime).and_eventually
      ((h_far w').and (eventually_isNeat (n := Fin a)))).exists
  -- A level `𝔑` that lies exactly in the places of `levelPlaces d S w₀ w₁ w'` and those containing
  -- `N`, whose elements fix `f`, are `≡ 1` modulo `w₀` and lie in `proIwahori` at `w₁`.
  have h_cover :
      ∀ w ∈ insert w₁ S, w ∈ levelPlaces d S w₀ w₁ w' ∨ star w ∈ levelPlaces d S w₀ w₁ w' :=
    mem_or_star_mem_insert_filter_of_isSplitPrimeToDisc hw₀_split hw' hv hε
  obtain ⟨𝔑, hN𝔑, h𝔑_mem, h_level⟩ := exists_levelGU_le_rightStabilizer hf.1 hf_off hS h_cover N
  -- Call `w` safe if `IsSafe 𝔑 w` holds. By `hF_good`, `v` is safe, and so is `w'` if `w'` and
  -- `star w'` lie outside `S`.
  obtain ⟨hF_good, h𝔑_star_w₀, h𝔑_w₁, h𝔑_star_w₁⟩ :=
    isSafe_and_mem_of_mem_iff h𝔑_mem hN hS hw₀_split hv hw' hw₁ hw₁_far
  have h_good (w : FinPlace E) : IsSafe 𝔑 w → 𝔑 ∈ w₀.asIdeal ∧ w ∉ S ∧ star w ∉ S :=
    mem_and_notMem_of_isSafe h𝔑_mem h_cover hS ⟨h𝔑_star_w₀, h𝔑_w₁, h𝔑_star_w₁⟩ w
  -- `t w j` is the eigenvalue of the `j`-th Hecke operator at `w` on `f`.
  have h_eig_safe (w : SafePlace 𝔑) : HasHeckePolyAt f w.val.val w.val.prop (P w.val.val) := by
    obtain ⟨-, hw_S, hw_S'⟩ := h_good w.val.val w.prop
    exact h_eig w.val.val w.val.prop hw_S hw_S'
  choose t ht_poly ht_eig using fun w : SafePlace 𝔑 ↦ (h_eig_safe w).right
  specialize h_neat 𝔑 (fun h ↦ by simp [h] at h𝔑_star_w₀) h𝔑_w₁
  choose h_level_fix h_level_w₀ h_level_w₁ using h_level
  obtain ⟨D, rfl, rfl, hD_β, hD_good⟩ := h_model 𝔑 h_neat.1 hN𝔑
  -- The form `ψ` attached to `f`; rational unitary matrices act on `f` through `ξ`
  -- (`exists_apply_mul_eq_of_mem_unitary`).
  obtain ⟨ψ, hψ_mem, hψ_ne, ⟨ω, hψ_cen⟩, hψ_loc⟩ := exists_central_eigenform ξ hf_ne h_neat
    ⟨w₀, hw₀_split.isSplit_of_below⟩ h𝔑_star_w₀ (exists_apply_mul_eq_of_mem_unitary hf hξ)
      h_level_fix
  choose L hL using hψ_loc
  have hL_f (w : SplitFinPlace E) (hw : D.level ∉ (star w.val).asIdeal) : L w hw f = ψ := by
    simpa using (hL w hw 1).symm
  have h_test : IsTestVector D.level (rightRegular ..) ψ ⟨_, hw₀_split.isSplit_of_below⟩ ⟨_, hw₁⟩
    χ := by
    refine
      { place_ne := hS.ne_of_notMem hw₁S
        notMem_star_fst := h𝔑_star_w₀
        mem_snd := h𝔑_w₁
        notMem_star_snd := h𝔑_star_w₁
        level_le := fun g hg ↦ by simpa using h_level_w₀ _ hg
        le_localIntGL := fun _ hg ↦ hg.1
        isCuspidalType := hχ_type
        level_le_proIwahori := fun g hg ↦ by simpa using h_level_w₁ _ hg
        ne_zero := hψ_ne
        isEigenvector := fun j ↦ (hL _ h𝔑_star_w₀ _).trans (by rw [hχ, map_smul, hL_f])
        fixed := fun g ↦ ?_ }
    have h_fix : rightRegular ℂ _ _ (ofSplitPlace hw₁ g.val) f = f := by
      simpa using (mem_sphericalAt_iff hw₁).mp (h_eig _ hw₁ hw₁S hw₁S').left g
    exact (hL _ h𝔑_star_w₁ _).trans (by simp only [h_fix, hL_f, MonoidHom.one_apply, one_smul])
  -- `ω` is an algebraic Hecke character, and its base change is unramified at the safe places.
  obtain ⟨hω, h_unr⟩ := centralChar_mem_algHeckeChars_and_charUnramifiedAt h_neat.1 hψ_mem hψ_ne
    hψ_cen hξ_centre
  -- The eigenvalues `θ` of `ψ` are those of `f` twisted by `ω`.
  let θ (w : SafePlace D.level) (j : ℕ) : ℂ := t w j * (ω (uniformizerNorm w.val))⁻¹ ^ j
  have hθ (w : SafePlace D.level) (j : ℕ) :
      (rightRegular ..).asAlgebraHom (heckeSum _ ℂ w.val j) ψ = θ w j • ψ :=
    asAlgebraHom_heckeSum_eq_smul hψ_mem hψ_cen L hL ht_eig w j
  -- `J`: the jumps at `τ₀` shifted by `μ` if `τ₀` lies over `s₀`, and no condition otherwise.
  let J : Multiset ℤ :=
    ((jumps κ D.rank τ₀).map (· + (μ : ℤ))).filter fun _ ↦ τ₀.comp (algebraMap ..) = s₀
  have hJ (u : ℤ) (hu : u ∈ J) : 0 ≤ u ∧ OccursInWeight D.rank m.succ θ u.toNat := by
    obtain ⟨⟨z, hz, rfl⟩, hs₀⟩ : (∃ z ∈ jumps κ D.rank τ₀, z + (μ : ℤ) = u) ∧
        τ₀.comp (algebraMap (QuadField d) E) = s₀ := by simpa [J] using hu
    exact ⟨h_nonneg hs₀ hz, h_occurs hs₀ hz hv₀ (fun u hu h ↦ hΨ u hu (by rw [h, hv₀, hs₀])) h_neat
      ⟨hψ_mem, ⟨_, _, _, _, h_test⟩, hθ⟩⟩
  -- The cohomology of a PEL model for `D` gives a representation with the eigenvalues `θ`.
  have hv_safe : IsSafe D.level v := hF_good.left
  obtain ⟨ρ, hρ, hρ_sph⟩ := exists_padicRep_of_pel h_neat hD_β hD_good hv_safe m θ J
    (fun u hu ↦ (hJ u hu).1) fun h hh ↦ (hJ h hh).2
  -- Twisting by the base change of `ω` removes the shift `μ` and the factor `ω`.
  obtain ⟨ρ', hρ', h_twist⟩ := exists_twist_algHeckeChar (.baseChange ⟨_, hω⟩) μ hρ
  -- Almost all places of prime norm are safe; `hF_good` covers `v` and `w'`.
  have h_ev : ∀ᶠ w in (mostFrobenii E).map (·.place), IsSafe D.level w :=
    eventually_mostFrobenii (h_far w₁) fun y ⟨⟨_, _, hyd⟩, h_off⟩ ↦
      isSafe_of_notMem_image_below h𝔑_mem (isSplitPrimeToDisc_below_of_prime_norm y.prime_q hyd)
        h_off
  refine ⟨ρ', hρ', (Filter.eventually_sup.mpr ⟨h_ev, hF_good⟩).mono fun w hw A hA ↦ ?_⟩
  obtain ⟨-, -, hv_below⟩ := hv
  -- An embedding that induces the safe place `w` restricts to `s₀`.
  have h_s₀ (s : E →+* ℂ) (hs : inducedPrime s = w) : s.comp (algebraMap (QuadField d) E) = s₀ :=
    comp_algebraMap_eq_of_isSafe hw (h_good w hw).left hv_below hε hs
  obtain ⟨h_unr', h_jump, h_poly⟩ :=
    h_twist w (by simp +contextual [h_s₀, hμ, AlgHeckeChar.baseChange]) (h_unr w hw)
      (hρ_sph ⟨⟨w, hw.1.isSplit_of_below⟩, hw⟩) hA
  rw [ht_poly ⟨⟨w, hw.1.isSplit_of_below⟩, hw⟩, Fintype.card_fin, map_heckePoly]
  refine ⟨h_unr', h_jump.congr hA ?_, h_poly⟩
  -- At an embedding inducing `w` the type of the twist is `μ`, which cancels the shift in `J`.
  simp +contextual [J, h_s₀, hμ, hv₀, AlgHeckeChar.baseChange, apply_ite, algebraMap_toAlgebra,
    Pi.single_apply]
  lia

/-- A weak form of a case of the theorem on Galois representations attached to cohomological
cuspidal forms, in odd rank `a`. Let `f` be a form of weight `κ` on the definite unitary group,
spherical off `S` with Hecke polynomials `P` (`hP`), that transforms at a split place `w₀ ∈ S` by a
cuspidal type `χ` of the matrices `≡ 1` modulo `w₀` (`localCongruence (Fin a) w₀ 0`). Let `v`, the
place of `ε`, lie with its conjugate outside `S` and over the place of `QuadField d` below `w₀`, and
let `κ` have `a` free jumps `e i` at `ε` (`HasNoSmallRelations`). Then some continuous `r` of rank
`a` has characteristic polynomials `ιℓ (P w)` along the filter `mostFrobenii E` and satisfies
`IsSphericalAbove` with exactly the jumps of `κ` at a given place `w'` as in `hw'`, if `w'` and its
conjugate lie outside `S`. -/
lemma New.GaloisRep.exists_rep_of_cuspidal_type {ℓ : ℕ} {E : Type} {a d : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    [HasPrimitiveRoot5040 E]
    (ha : Odd a) {κ : Weight E} {f : Gf E (Fin a) → WeylIndex (Fin a) κ.1 → ℂ}
    (hf : f ∈ (stdSpace E (Fin a)).forms κ) {S : Finset (FinPlace E)}
    {P : FinPlace E → Polynomial ℂ} (hP : IsSphericalOff S f P) {w₀ v : FinPlace E} (hS : w₀ ∈ S)
    (hw₀_split : IsSplitPrimeToDisc (w₀.below (QuadField d)))
    {χ : localCongruence (Fin a) w₀ 0 →* ℂ}
    (hχ_type : IsCuspidalType (localCongruence (Fin a) w₀ 0) χ)
    (hχ : ∀ j : localCongruence (Fin a) w₀ 0,
      rightRegular ℂ (Gf E (Fin a)) (WeylIndex (Fin a) κ.1 → ℂ)
        (ofSplitPlace hw₀_split.isSplit_of_below j.val) f = χ j • f)
    (hv : v ∉ S ∧ star v ∉ S ∧ v.below (QuadField d) = w₀.below (QuadField d))
    {ε : Ω →+* PadicAlgCl ℓ} (hε : placeOfEmb (ε.comp (algebraMap E Ω)) = v) {e : Fin a → ℤ}
    (he_free : HasNoSmallRelations e)
    (he_jumps : ∀ i : Fin a, e i ∈ jumps κ a (RingHom.comp ιℓ.symm (ε.comp (algebraMap E Ω))))
    (w' : FinPlace E) (hw' : IsSplitPrimeToDisc (w'.below (QuadField d)) ∧
      (↑ℓ ∈ w'.asIdeal → w'.below (QuadField d) = w₀.below (QuadField d))) :
    ∃ r : GalRep ℓ E (Fin a),
      Continuous r ∧
      -- (a) characteristic polynomials along the filter `mostFrobenii E`
      (∀ᶠ y : FrobeniusDatum E in mostFrobenii E, (r y.frob).val.charpoly = (P y.place).map ιℓ) ∧
      -- (b) local behaviour at `w'`
      (w' ∉ S ∧ star w' ∉ S → IsSphericalAbove r Eq (jumps κ a) w' ((P w').map ιℓ)) := by
  -- For each embedding `τ₀`, transfer `f` to a form `ψ` on the definite frames, realize its
  -- eigenvalues in the cohomology of a PEL model and twist: this gives a representation with the
  -- jumps at `τ₀` (`exists_padicRep_of_cuspidal_type_at_embedding`).
  -- `exists_galRep_charpoly_eq_of_forall_embedding` joins these, using the free jumps at `v`.
  have : NeZero a := .of_pos ha.pos
  have h_one :=
    exists_padicRep_of_cuspidal_type_at_embedding ha hf hP hS hw₀_split hχ_type hχ hv hε w' hw'
  obtain ⟨hf_ne, -, h_eig⟩ := hP
  have h_monic : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      ↑ℓ ∉ y.place.asIdeal ∧ ((P y.place).map (ιℓ : ℂ →+* PadicAlgCl ℓ)).IsMonicOfDegree a := by
    refine eventually_mostFrobenii (eventually_notMem_star_notMem ℓ S) fun y ⟨hyS, hyS', hyℓ⟩ ↦ ?_
    obtain ⟨h_deg, h_lead⟩ :=
      (h_eig _ (isSplit_of_q_prime y.prime_q) hyS hyS').isMonicOfDegree hf_ne
    exact ⟨hyℓ, by simp [h_deg], h_lead.map _⟩
  obtain ⟨r, hr, h_frob, -, h_w'⟩ :=
    exists_galRep_charpoly_eq_of_forall_embedding κ h_monic he_free he_jumps (by simp [hε]) h_one
  exact ⟨r, hr, h_frob, fun hS' ↦ h_w' ⟨rfl, hS'⟩⟩
