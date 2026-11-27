module

import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.RingTheory.Etale.Weakly
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.DiscreteSeries.Holomorphic.PeaksAwayFromCusp
public import New.OneLift.ComparisonOperator.ExchangeData
public import Lib.DiscreteSeries.Holomorphic.HighestVectorExtension
import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
import Lib.DiscreteSeries.Haar.TotalMass
import Lib.DiscreteSeries.Holomorphic.MaximalCompactMinors
import Lib.DiscreteSeries.Holomorphic.ModelFunction
import Lib.General.Analysis.PackingAndSobolev
import Lib.PadicComparison.Descent.TestCategory
import Lib.DiscreteSeries.Bruhat.ComplexPlace
import Lib.DiscreteSeries.Rigidity.HighestVectorsAndFiltration
import Lib.SiegelWeil.Reproduction
import New.Determinant.Norms.AdjointThetaLift
import New.OneLift.ComparisonOperator.ThreeExchanges

section
/-!
# Decay of Fock matrix coefficients, sparse theta sums and the isolation estimate

This file holds the estimates behind the theorem that products span. The Heisenberg matrix
coefficients of a homogeneous Fock vector decay faster than any power. So in a theta sum over a
sparse lattice the term of `0` dominates, and a mean over additive characters produces such a sum.
Bounds for integrals of matrix coefficients of holomorphic discrete series then give the isolation
estimate `New.Data.norm_apply_one_le_of_forall_isPeak`, the last step of the proof: the mean over a
circle of peaks.

## Main definitions and results

* `New.Fock.norm_fockInner_realHeisenbergOp_le`: the decay of the coefficient `⟨v, ϱ(y) ω(σ) v⟩` in
  `y`.
* `New.Rows.firstMinimum_mul_le_hom`: the first minimum of `Hom (S, T)` is bounded below by the
  product of the first minima of `S` and `T`, up to an explicit constant.
* `New.Rows.exists_norm_modKernel_sub_fockInner_le`: for a suitable finite datum `Ψ` modulo `𝔪`, the
  theta kernel at real translates of `(g, h)` differs from a Fock matrix coefficient by a small
  error if the lattice of `Hom (S, T)` has no short vectors.
* `New.Data.integral_norm_holMinorsPi_mul_pow_le`: the integral of the basic function of a weight
  with a large gap against a power of the norm, compared with a squared `L²` norm.
* `New.Data.norm_apply_one_le_of_forall_isPeak`: let a bounded function `K₀` be close, for every
  peak of a holomorphic `F`, to a holomorphic `K` whose weighted integral against the translate of
  `F` vanishes. Then `K₀ 1` is small.

Notions from other files:
* `New.Fock.fockSpace`: The Fock space: integrable functions c on ℂ^ι with c(x) = ∫ c(y)β(y,x)e(x−y)
  dy, β the Heisenberg bicharacter, e the Gaussian exp(−|x|²/2), under the L¹ norm.
* `New.Fock.fockInner`: The bounded sesquilinear form on the Fock space, conjugate-linear in the
  first variable, (c, c′) ↦ ∫ c̄ c′.
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.GInf`: The archimedean unitary group G_∞ for signs s: one copy of the complex unitary group
  U(diag s) for each infinite place of E.
* `New.IsPosFirstOrder`: The order o has distinct values and puts every index of sign +1 before
  every index of sign −1.
* `New.Space.vecAtPoint`: the adelic vector x⁻¹y of a rational vector y at the point x of a space;
  the lattice `New.Space.baseLattice` consists of the y for which it has integral finite part.
* `New.realCoord`: the Fock coordinates of an adelic vector: its components at the infinite places
  τ, times √(2π Im τ(j)), with j the element fixed by the Weil data.

## Relation to the literature

See `New.OneLift.ComparisonOperator.ProductsSpan` for related work. See
`Lib.Weil.DualPair.ThetaLiftConvergence` and `Lib.Adelic.Reduction.FiniteVolume` for sources.
-/

@[expose] public section

/-!
## Decay of Heisenberg matrix coefficients of homogeneous Fock vectors

One estimate, `New.Fock.norm_fockInner_realHeisenbergOp_le`: for a homogeneous polynomial P and v =
v_P in the Fock space, the coefficient ⟨v, ϱ(y)ω(σ)v⟩ decays faster than any power of |y|, with
explicit constants and polynomial growth in ‖σ‖. Here ϱ = `New.Fock.realHeisenbergOp` is the
Heisenberg action, ω = `New.Fock.realWeil` the Weil representation of U(ε), and v_P =
`New.Fock.polyVector` ε P.
-/

section FockCoeffDecay

open MeasureTheory Real Fintype MvPolynomial Matrix.Norms.L2Operator New.Heisenberg IsVacuum Rep
  WithLp

/-- For `σ` in `U(ε)` and vectors `x`, `y`, the points `x` and `σ x + y` cannot both be
small: `|y|² ≤ 2 ‖σ‖² (|x|² + |σ x + y|²)`, with Euclidean norms and the ℓ² operator norm. -/
lemma New.Fock.norm_sq_le_norm_sq_add_norm_mulVec_add_sq {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {ε : ι → ℤˣ} (σ : USign (n := ι) ε) (x y : ι → ℂ) :
    ‖toLp 2 y‖ ^ 2 ≤ 2 * ‖(σ : Matrix ι ι ℂ)‖ ^ 2 *
      (‖toLp 2 x‖ ^ 2 + ‖toLp 2 ((σ : Matrix ι ι ℂ).mulVec x) + toLp 2 y‖ ^ 2) := by
  set M : Matrix ι ι ℂ := ↑σ
  have Mx_le : ‖toLp 2 (M.mulVec x)‖ ≤ ‖M‖ * ‖toLp 2 x‖ := M.l2_opNorm_mulVec (toLp 2 x)
  calc ‖toLp 2 y‖ ^ 2 ≤ (‖M‖ * ‖toLp 2 (M.mulVec x) + toLp 2 y‖ + ‖M‖ * ‖toLp 2 x‖) ^ 2 := by
        grw [norm_le_add_norm_add' (toLp 2 (M.mulVec x)), ← Mx_le, ← U.one_le_norm σ, one_mul]
    _ ≤ 2 * ((‖M‖ * ‖toLp 2 (M.mulVec x) + toLp 2 y‖) ^ 2 + (‖M‖ * ‖toLp 2 x‖) ^ 2) := add_sq_le
    _ = _ := by ring

/-- Let ι be nonempty, P a complex polynomial with P(cx) = c^d P(x) for real c, v = v_P its Fock
vector (`polyVector`), σ in U(ε), and y ≠ 0 in ℂ^ι. For natural numbers A ≥ d + |ι| and n,
|⟨v, ϱ(y)ω(σ)v⟩| ≤ (4(A + n))^n |y|^{−2n} ‖σ‖^{|ι| + 2n} ⟨v, v⟩.
Here ϱ = `realHeisenbergOp` is the Heisenberg action on the Fock space and ω = `realWeil` the Weil
representation of U(ε), |y| = `‖toLp 2 y‖` is the Euclidean norm, ‖σ‖ the ℓ² operator norm of the
matrix of σ, and ⟨v, v⟩ is real. -/
theorem New.Fock.norm_fockInner_realHeisenbergOp_le {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    {ε : ι → ℤˣ} {P : MvPolynomial ι ℂ} {v : fockSpace ε} {y : ι → ℂ} (σ : USign (n := ι) ε)
    (hv : v = polyVector ε P) {d A n : ℕ}
    (hP : ∀ (c : ℝ) (x : ι → ℂ), eval (c • x) P = c ^ d * eval x P) (hA : d + card ι ≤ A)
    (hy : 0 < ‖toLp 2 y‖) :
    ‖fockInner v (realHeisenbergOp y (realWeil σ v))‖ ≤
      ‖(σ : Matrix ι ι ℂ)‖ ^ (card ι + 2 * n) * (fockInner v v).re * (4 * (A + n)) ^ n *
        ‖toLp 2 y‖⁻¹ ^ (2 * n) := by
  -- The coefficient is at most `‖σ‖^|ι| ∫ ‖v x‖ ‖v (σ x + y)‖ dx`. Dilating by `c = √(n/A + 1)`
  -- takes a Gaussian factor out of `v`, which is small at `x` or at `σ x + y`; the rest is bounded
  -- by `2ab ≤ a² + b²`, which does the work of the Cauchy–Schwarz inequality as `a²` and `b²` have
  -- the same integral. The dilation costs the factor `c^(2(d + |ι|)) ≤ eⁿ`.
  have A_ne : A ≠ 0 :=
    (card_pos.trans_le ((Nat.le_add_left (card ι) d).trans hA)).ne'
  let c : ℝ := √(n / A + 1)
  let v_scaled : fockSpace ε := (c : ℂ) ^ d • v
  let G (x : ι → ℂ) : ℝ := ‖v_scaled (c⁻¹ • x)‖ ^ 2
  let K : ℝ := (4 * (A + n) * ((‖(σ : Matrix ι ι ℂ)‖ / ‖toLp 2 y‖) ^ 2 / exp 1)) ^ n
  -- Homogeneity of `P`, and `1 - c⁻² = n / (n + A)`.
  have norm_v (x : ι → ℂ) :
      ‖v x‖ = ‖v_scaled (c⁻¹ • x)‖ / exp (‖toLp 2 x‖ ^ 2 / (n + A) / 2) ^ n := by
    simp (disch := positivity) [v_scaled, *, realVac, star_dotProduct_self_eq_norm_sq, sq, c,
      ← exp_natCast_mul, mul_assoc, ← exp_add, field, star_trivial, Complex.norm_exp]
  have G_int : Integrable G (normalizedVolume ι) :=
    (integrable_norm_sq v_scaled).comp_smul (by positivity)
  have preserving : MeasurePreserving (σ • · + y) (normalizedVolume ι) (normalizedVolume ι) :=
    ((realAction ε).measurePreserving σ).add_right _ y
  -- Undoing the dilation gives `c^(2d)` from `v_scaled` and the Jacobian `c^(2|ι|)`.
  have G_le : ∫ x, G x ∂normalizedVolume ι ≤ exp n * ∫ x, ‖v x‖ ^ 2 ∂normalizedVolume ι := by
    have exponent_le : ((card ι + d : ℕ) : ℝ) * (n / A) ≤ n := by
      grw [add_comm, hA]
      simp [field]
    have c_pow : (c ^ 2) ^ (card ι + d) ≤ exp n := by
      grw [sq_sqrt (by positivity), add_one_le_exp, ← exp_natCast_mul, exponent_le]
    calc _ = (c ^ 2) ^ card ι * ((c ^ 2) ^ d * ∫ x, ‖v x‖ ^ 2 ∂normalizedVolume ι) := by
          -- ↓ changes variables before simp rewrites inside the integral.
          simp [G, ↓(normalizedVolume ι).integral_comp_inv_smul (‖v_scaled ·‖ ^ 2), v_scaled,
            mul_pow, integral_const_mul, pow_mul, finrank_real_of_complex, pow_right_comm _ d]
      _ ≤ _ := by grw [← mul_assoc, ← pow_add, c_pow]
  -- As `x` and `σ x + y` are not both small, the two denominators multiply to at least `K⁻¹`.
  have pointwise (x : ι → ℂ) :
      ‖v x‖ * ‖v ((σ : Matrix ι ι ℂ).mulVec x + y)‖ ≤ K / 2 * (G x + G (σ • x + y)) := by
    let e : ℝ := ‖toLp 2 x‖ ^ 2 / (n + A) / 2 +
      ‖toLp 2 ((σ : Matrix ι ι ℂ).mulVec x) + toLp 2 y‖ ^ 2 / (n + A) / 2
    have one_le :
        1 ≤ exp e * (4 * (A + n) * ((‖(σ : Matrix ι ι ℂ)‖ / ‖toLp 2 y‖) ^ 2 / exp 1)) := by
      grw [← exp_one_mul_le_exp]
      simp only [e]
      field_simp
      linear_combination 2 * (n + A) * norm_sq_le_norm_sq_add_norm_mulVec_add_sq σ x y
    calc _ = ‖v_scaled (c⁻¹ • x)‖ * ‖v_scaled (c⁻¹ • (σ • x + y))‖ / exp e ^ n := by
          simp [norm_v, unitary_smul_eq_mulVec, e, exp_add, mul_pow, div_mul_div_comm]
      _ ≤ (G x + G (σ • x + y)) / 2 / exp e ^ n := by
          gcongr
          linarith [two_mul_le_add_sq ‖v_scaled (c⁻¹ • x)‖ ‖v_scaled (c⁻¹ • (σ • x + y))‖]
      _ ≤ (G x + G (σ • x + y)) / 2 / exp e ^ n * (exp e ^ n * K) := by
          grw [← mul_pow, ← one_le_pow₀ one_le, mul_one]
      _ = _ := by field_simp
  -- By the reproducing property of the vacuum, the integrand below has the norm just bounded.
  have integrand_le (x : ι → ℂ) :
      ‖v x * fockInner (realHeisenbergOp (-y) v)
        (realHeisenbergOp ((σ : Matrix ι ι ℂ).mulVec x) vacElem)‖ ≤
        K / 2 * (G x + G (σ • x + y)) := by
    rw [← conj_modelInner, modelInner_heisenbergOp_vacElem]
    simpa [norm_eq_one] using pointwise x
  -- Move `realHeisenbergOp y` to the left and write `realWeil σ v` as an integral of translated
  -- vacua.
  have coeff_eq : ‖fockInner v (realHeisenbergOp y (realWeil σ v))‖ = ‖realMultiplier σ‖ *
      ‖∫ x, v x * fockInner (realHeisenbergOp (-y) v)
        (realHeisenbergOp ((σ : Matrix ι ι ℂ).mulVec x) vacElem)
        ∂normalizedVolume ι‖ := by
    rw [← modelInner_heisenbergOp (-y), mul, neg_add_cancel, Rep.rho_zero_apply]
    simp [weilRep, map_integrated_eq_integral, realAction, self_eq_one]
  -- The multiplier has norm at most `‖σ‖^|ι|`, and both terms of the bound have integral `∫ G`,
  -- since `x ↦ σ x + y` preserves the measure.
  rw [coeff_eq]
  calc _ ≤ ‖(σ : Matrix ι ι ℂ)‖ ^ card ι * (K / 2 *
        (exp n * ∫ x, ‖v x‖ ^ 2 ∂normalizedVolume ι + exp n * ∫ x,
          ‖v x‖ ^ 2 ∂normalizedVolume ι)) := by
        have G_int' : Integrable (G ∘ (σ • · + y)) _ :=
          preserving.integrable_comp_of_integrable G_int
        grw [norm_integral_le_of_norm_le ((G_int.add G_int').const_mul (K / 2))
          (.of_forall integrand_le), integral_const_mul, integral_add' G_int G_int',
          preserving.hasLaw.integral_comp G_int.aestronglyMeasurable, norm_realMultiplier_le, G_le]
    _ = _ := by
      simp [modelInner_self, K, mul_pow, pow_mul, div_pow, pow_add, field, one_add_one_eq_two]

end FockCoeffDecay

/-!
## First minimum of Hom(S, T) and sparse theta sums

`New.Space.firstMinimum V` is the length of a shortest nonzero vector of the lattice of `V`, cut off
at `1`. A point `g` enters by moving the space, as in `V.move g`. `New.modKernel S T a b 𝔪 Ψ Q` is
the theta kernel of `(S, T)` for the characters `a`, `b`, the function `Ψ` on matrices modulo `𝔪`
and the polynomial `Q`.
-/

namespace New.Rows

open NumberField Matrix ComplexConjugate Fock WeilData Norms.L2Operator Fintype Space G
  EuclideanSpace Complex BigOperators Modulus Finset Prod Set AddChar Circle

variable {E n n' : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  [Fintype n'] [DecidableEq n'] {s' : n' → ℤˣ}
  {S : Space E n s} (T : Space E n' s')

/-- For a space `V` let `λ(V) = V.firstMinimum` be the minimum of `1` and the length of a shortest
nonzero vector of the lattice of `V`. If the natural number `N ≠ 0` lies in the different of `E`,
then `λ(S) λ(T) / (C |n'| |n|) ≤ λ(Hom (S, T))`, where `C = shortBasisConst E n N = 6 N (f |n|)²`
and `f` is the number of infinite places of `E`. -/
theorem firstMinimum_mul_le_hom [Nonempty n] [Nonempty n']
    {S : Space E n s} (T : Space E n' s') {N : ℕ} [NeZero N]
    (hN_mem : ↑N ∈ differentIdeal ℤ (𝓞 E)) :
    S.firstMinimum * T.firstMinimum / (shortBasisConst E n N * Fintype.card n' * Fintype.card n) ≤
      (S.hom T).firstMinimum := by
  -- Read a nonzero lattice vector `z` of `Hom (S, T)` as a matrix and apply it to a short basis `Y`
  -- of the lattice of `S`. Some image is a nonzero lattice vector of `T`, so it has length at least
  -- `T.firstMinimum`; and its length is at most `card n' * card n * ‖z‖` times that of the basis
  -- vector.
  refine le_firstMinimum_iff.2 ⟨?_, fun z hz z_ne ↦ ?_⟩
  · -- both minima are at most `1` and the denominator is a natural number
    grw [firstMinimum_le_one, firstMinimum_le_one]
    · simp [Nat.cast_inv_le_one, ← Nat.cast_mul]
    simp [firstMinimum_pos, le_of_lt]
  choose Y Y_mem Y_short using S.exists_short_basis hN_mem
  -- `k`, the matrix of `z` in adelic coordinates, takes the coordinates of `y` to those of `z y`
  let k : Matrix n' n (𝔸 E) := vecToMatrix ((S.hom T).vecAtPoint z)
  have vec_eq (y : n → E) : T.vecAtPoint (vecToMatrix z *ᵥ y) = k *ᵥ S.vecAtPoint y := by
    -- `z` is `matrixToVec (vecToMatrix z)` by definition.
    simp [k, show (S.hom T).vecAtPoint z = matrixToVec (T.ratMap S (vecToMatrix z)) from
      vecAtPoint_hom _ _ (vecToMatrix z), ratMap_mulVec_vecAtPoint]
  have norm_k (w : InfinitePlace E) :
      ‖k.map (·.1 w)‖ ≤ card n' * card n * ‖(S.hom T).archCoords z‖ :=
    l2_opNorm_le_of_apply fun i j ↦ ((S.hom T).archCoords z).norm_apply_le (w, i, j)
  have k_int (i : n') (j : n) : (k i j).2 ∈ Ô E := hz (i, j)
  -- As `Y` is invertible and `z ≠ 0`, some basis vector has a nonzero image.
  obtain ⟨j, hj⟩ : ∃ j : n, vecToMatrix z *ᵥ Y.val.col j ≠ 0 := by
    by_contra! h_all
    have hzY : vecToMatrix z * Y.val = 0 := Matrix.ext fun i j ↦ congrFun (h_all j) i
    exact z_ne (by simpa [Matrix.mul_assoc] using congrArg (fun M ↦ matrixToVec (M * Y⁻¹.1)) hzY :)
  -- That image lies in the lattice of `T`, and its length is bounded by means of `norm_k`.
  obtain ⟨image_mem, norm_image⟩ :=
    T.mem_and_norm_le_of_vecAtPoint _ S (Y.val.col j) k 1 norm_k (by rw [one_smul, vec_eq])
  grw [firstMinimum_le (image_mem (by simpa using k_int) (Y_mem j)) hj, norm_image, Y_short]
  · have h_pos : 0 < S.firstMinimum := S.firstMinimum_pos
    simp [field]
  all_goals simp [firstMinimum_pos, le_of_lt]

variable [WeilData E]

/-- Let `S`, `T` be hermitian spaces over `E` with signs `s`, `s'` at the infinite places, and
`S.hom T = Hom (S, T)`. Let `t` be a matrix modulo the ideal `𝔪` and `Ψ_t(y) = ψ(tr(y t))` its
additive character (`traceChar t`), with `ψ` the chosen primitive character of the residue ring. Let
`v`, `w` be vectors of the Fock space in the variables `(τ, (i, k))`, `τ` an infinite place, with
signs `s' i * s k`, and `z` an adelic vector of `Hom (S, T)`. The datum `v ⊗ Ψ_t ⊗ vac` (`modDatum`)
is the function on adelic vectors made of `v` at the infinite places, `Ψ_t` at the places dividing
`𝔪` and the vacuum elsewhere; `dataInner` is the pairing `∫ c̄ c'` of such functions and `ϱ` the
Heisenberg action on them.

Then `⟨v ⊗ Ψ_t ⊗ vac, ϱ(z)(w ⊗ Ψ_t ⊗ vac)⟩` is a product of three factors. Write `z_f` for the
finite part of `z`, and `α`, `j` for the finite idele and the imaginary element of `E` fixed by
`WeilData E`. The first factor is `Ψ_t` read (by `liftFn`) at `finCoord z = α⁻¹ z_f`. The second is
the Fock coefficient `⟨v, ϱ(x) w⟩` at `x = realCoord z`, the components of `z` at the places `τ`
times `√(2π Im τ(j))`. The third is `vacuumFn` at `finVec (finCoord z) = (0, z_f)`: a complex number
of modulus `1` if `α⁻¹ z_f` is integral, and `0` otherwise. -/
lemma dataInner_traceChar {𝔪 : Modulus E} (t : Matrix n n' 𝔪.ResidueRing)
    (v w : fockSpace (realSigns E (homSigns s s'))) (z : n' × n → 𝔸 E) :
    (S.hom T).dataInner (modDatum S T 𝔪 (traceChar t) v)
        ((S.hom T).ϱ z (modDatum S T 𝔪 (traceChar t) w)) =
      𝔪.liftFn (traceChar t ∘ vecToMatrix) (finCoord z) *
        (fockInner v (realHeisenbergOp (realCoord z) w) * vacuumFn (finVec (finCoord z))) := by
  -- The finite part of the datum of `traceChar t` is the vacuum translated by a finite vector `y`.
  -- Moving `ϱ z_f` past `ϱ y` costs the phase `β(z_f, y) ^ 2`; if `α⁻¹ z_f` is integral, this is
  -- the lift of `traceChar t` at it.
  choose lift hlift using fun i j ↦ 𝔪.reduction_surjective (t i j)
  -- `tLift` is an integral lift of the transpose of `t`, so the trace of `x * t` is a dot product
  let tLift (p : n' × n) : Ô E := lift p.2 p.1
  have h_char :
      traceChar t ∘ vecToMatrix = fun x ↦ 𝔪.primAddChar (x ⬝ᵥ 𝔪.reduction ∘ tLift) := by
    simp [funext_iff, tLift, hlift, trace, Matrix.mul_apply, dotProduct, sum_prod_type, traceChar,
      vecToMatrix]
  let y : n' × n → 𝔸 E := finVec (star (idem 𝔪.places • 𝔪.generator⁻¹.val • Subtype.val ∘ tLift))
  let zf : n' × n → 𝔸 E := fun i ↦ (0, (z i).2)
  have h_zf : finVec (finCoord z) = zf := funext fun i ↦ by simp [finVec, finCoord, zf]
  rw [h_zf]
  -- the pairing splits into a real and a finite part; `ϱ y` is unitary and cancels after `rho_swap`
  trans fockInner v (realHeisenbergOp (realCoord z) w) *
    ((adelicHeisenberg E (homSigns s s')).β zf y ^ 2 * vacuumFn zf)
  · rw [modDatum, modDatum, rho_integrated_realCoord, dataInner_integrated, h_char,
      𝔪.schrodingerOp_char_eq_translate_projOn, rho_swap, map_smul]
    -- ↓ rewrites operators on integrated vectors before their arguments are simplified.
    simp [y, zf, finVec, ↓← rho_integrated]
  by_cases hz : ∀ i, finCoord z i ∈ Ô E
  · -- The phase of `ϱ zf` past `ϱ y` is the lift of `traceChar t` at `α⁻¹ z_f`.
    have h_beta : ((adelicHeisenberg E (homSigns s s')).β zf y : ℂ) ^ 2 =
      (ψf E (algebraMap E (𝔸f E) j * ∑ x, star α.val *
        (idem 𝔪.places * (𝔪.generator⁻¹.val * (tLift x).val)) * (z x).2) : Circle) := by
      simp [y, zf, finVec, adelicHeisenberg, stdForm, stdAddChar, dotProduct, fst_sum, snd_sum,
        mulVec_diagonal, ← Circle.coe_pow, ← map_nsmul_eq_pow, two_mul, ← map_add, ← add_mul]
    rw [h_char, 𝔪.liftFn_apply, dite_eq_left fun i ↦ mul_mem (idem_mem_Ô _) (hz i), h_beta,
      mul_left_comm]
    simp [zf, finCoord, stdLattice.selfDualAddChar_apply, dotProduct, ← map_mul, ← map_sum, mul_sum,
      mul_assoc,
      mul_left_comm, mul_comm (tLift _).val]
  · -- Otherwise `z_f` lies outside the support of the vacuum.
    have h_vac : vacuumFn zf = 0 := by simpa [zf, vacuumFn, finCoord] using hz
    simp [h_vac]

omit [WeilData E] in
/-- Let `u` and `u'` be families of matrices `u τ` in `U(diag s)` and `u' τ` in `U(diag s')`, one
for each infinite place `τ` of `E` (`GInf`). The block diagonal matrix `pairHomInf (u, u')`, which
acts on `n' × n` matrices by `x ↦ (u' τ) x (u τ)⁻¹` at `τ`, has ℓ² operator norm at most
`maxOpNorm u * maxOpNorm u'`, where `maxOpNorm u` is the largest of the norms `‖u τ‖`. -/
lemma norm_pairHomInf_le_mul (u : GInf E s) (u' : GInf E s') :
    ‖(pairHomInf (u, u') :
        Matrix (InfinitePlace E × n' × n) (InfinitePlace E × n' × n) ℂ)‖ ≤
      maxOpNorm u * maxOpNorm u' := by
  -- The block diagonal map is a star homomorphism, so it does not increase norms, and each block
  -- is a Kronecker product.
  let B : (InfinitePlace E → Matrix (n' × n) (n' × n) ℂ) →⋆ₙₐ[ℂ]
      Matrix (InfinitePlace E × n' × n) (InfinitePlace E × n' × n) ℂ :=
    { blockMatrix with map_smul' := by simp [submatrix_smul], map_star' := by simp [star] }
  refine (NonUnitalStarAlgHom.norm_apply_le B _).trans ((pi_norm_le_iff_of_nonempty _).2 fun τ ↦ ?_)
  refine (norm_pairHom_le ..).trans ?_
  change ‖(u τ : Matrix n n ℂ)‖ * ‖(u' τ : Matrix n' n' ℂ)‖ ≤ maxOpNorm u * maxOpNorm u'
  gcongr
  exacts [norm_le_pi_norm (fun w ↦ (u w : Matrix n n ℂ)) τ,
    norm_le_pi_norm (fun w ↦ (u' w : Matrix n' n' ℂ)) τ]

/-- Let `V` be a hermitian space over `E` with adelic point `x` (`Space`). Its lattice
`V.baseLattice` consists of the rational vectors `y` whose adelic vector `V.vecAtPoint y = x⁻¹ y`
has integral finite part, and `λ = V.firstMinimum` is the minimum of `1` and the length of a
shortest nonzero lattice vector. Let `Φ w` be the chosen complex embedding at the infinite place `w`
and `j` the element of `E` with `Im (Φ w j) > 0` fixed by `WeilData E`. Let `c ≠ 0` and `m > 0`
satisfy `m |Φ w c| ≤ √(2π Im (Φ w j)) λ` for all `w`. If `y ≠ 0` and `c y` lies in the lattice, then
the Fock coordinates of `x⁻¹ y` have Euclidean norm at least `m`. -/
lemma le_norm_realCoord {ι : Type} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ} (V : Space E ι ε)
    {c : E} (hc_ne : c ≠ 0) {m : ℝ} (hm_pos : 0 < m)
    (hm : ∀ w : InfinitePlace E, m * ‖Φ w c‖ ≤ √(2 * Real.pi * (Φ w j).im) * V.firstMinimum)
    {y : ι → E} (hy_mem : c • y ∈ V.baseLattice) (hy_ne : y ≠ 0) :
    m ≤ ‖WithLp.toLp 2 (realCoord (V.vecAtPoint y))‖ := by
  -- The vector `c • y` is a nonzero lattice vector, so its length is at least the first minimum.
  refine le_of_mul_le_mul_right ?_ V.firstMinimum_pos
  calc m * V.firstMinimum ≤ ‖m • V.archCoords (c • y)‖ := by
        grw [norm_smul_of_nonneg hm_pos.le, firstMinimum_le hy_mem (smul_ne_zero hc_ne hy_ne)]
    _ ≤ ‖V.firstMinimum • WithLp.toLp 2 (realCoord (V.vecAtPoint y))‖ := by
      -- Compare coordinate by coordinate, using `hm`.
      simp only [norm_eq]
      gcongr with ⟨w, i⟩
      calc _ = m * ‖Φ w c‖ * ‖(V.vecAtPoint y i).1 w‖ := by
            simp [abs_of_nonneg, hm_pos.le, archCoords, mul_assoc]
        _ ≤ √(2 * Real.pi * (Φ w j).im) * V.firstMinimum * ‖(V.vecAtPoint y i).1 w‖ := by grw [hm]
        _ = _ := by simp [abs_of_nonneg, realCoord, V.firstMinimum_pos.le, val_scaleIdele_fst,
          field]
    _ = _ := by simp [norm_smul, V.firstMinimum_pos.le, mul_comm]

/-- Let `c ≠ 0` and `m > 0` satisfy `m ‖Φ w c‖ ≤ √(2π Im (Φ w j)) · V.firstMinimum` at every
infinite place `w`. If `y ≠ z` and both `c • y` and `c • z` lie in `V.baseLattice`, then the Fock
coordinates `realCoord (V.vecAtPoint y)` and `realCoord (V.vecAtPoint z)` are at distance at least
`m`. -/
lemma le_norm_realCoord_sub {ι : Type} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ} (V : Space E ι ε)
    {c : E} (hc_ne : c ≠ 0) {m : ℝ} (hm_pos : 0 < m)
    (hm : ∀ w : InfinitePlace E, m * ‖Φ w c‖ ≤ √(2 * Real.pi * (Φ w j).im) * V.firstMinimum)
    {y z : ι → E} (hy_mem : c • y ∈ V.baseLattice) (hz_mem : c • z ∈ V.baseLattice) (hyz : y ≠ z) :
    m ≤ ‖WithLp.toLp 2 (realCoord (V.vecAtPoint y)) -
      WithLp.toLp 2 (realCoord (V.vecAtPoint z))‖ := by
  have diff_far : m ≤ ‖WithLp.toLp 2 (realCoord (V.vecAtPoint (y - z)))‖ :=
    le_norm_realCoord V hc_ne hm_pos hm (by simpa [smul_sub] using sub_mem hy_mem hz_mem)
      (sub_ne_zero.2 hyz)
  -- The Fock coordinates of `y - z` are the differences of those of `y` and `z`.
  simpa [← sub_div, realCoord, norm_eq] using diff_far

/-- Let `V` be a hermitian space over `E` with adelic point `x` (`Space`). Its lattice
`V.baseLattice` consists of the rational vectors `y` whose adelic vector `V.vecAtPoint y = x⁻¹ y`
has integral finite part, and `λ = V.firstMinimum` is the minimum of `1` and the length of a
shortest nonzero lattice vector. Let `Φ w` be the chosen complex embedding at the infinite place `w`
and `j` the element of `E` with `Im (Φ w j) > 0` fixed by `WeilData E`. Let `c ≠ 0` and `m > 0`
satisfy `m |Φ w c| ≤ √(2π Im (Φ w j)) λ` for all `w`. Let `y` run over the nonzero vectors with
`c y` in the lattice, and let `|y|` be the Euclidean norm of the Fock coordinates of `x⁻¹ y`. If `q`
exceeds the number of these coordinates, then `m ≤ |y|` for all such `y`, and `∑ |y| ^ (-2q)`
converges and is at most `(5 / m) ^ (2q)`. -/
lemma tsum_inv_norm_realCoord_pow_le {ι : Type} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}
    (V : Space E ι ε) {c : E} (hc_ne : c ≠ 0) {m : ℝ} (hm_pos : 0 < m)
    (hm : ∀ w : InfinitePlace E, m * ‖Φ w c‖ ≤ √(2 * Real.pi * (Φ w j).im) * V.firstMinimum)
    {q : ℕ} (hq : Fintype.card (InfinitePlace E × ι) < q) :
    (∀ y : {y : ι → E | c • y ∈ V.baseLattice ∧ y ≠ 0},
      m ≤ ‖WithLp.toLp 2 (realCoord (V.vecAtPoint y))‖) ∧
    Summable (fun y : {y : ι → E | c • y ∈ V.baseLattice ∧ y ≠ 0} ↦
      ‖WithLp.toLp 2 (realCoord (V.vecAtPoint y))‖⁻¹ ^ (2 * q)) ∧
    ∑' y : {y : ι → E | c • y ∈ V.baseLattice ∧ y ≠ 0},
      ‖WithLp.toLp 2 (realCoord (V.vecAtPoint y))‖⁻¹ ^ (2 * q) ≤ (5 / m) ^ (2 * q) := by
  -- The points are `m`-separated and at distance at least `m` from `0`, so the packing bound
  -- applies; by `hq`, the exponent `2 * q` exceeds the real dimension by at least `2`.
  let L : Set (ι → E) := {y | c • y ∈ V.baseLattice ∧ y ≠ 0}
  let f (y : L) : EuclideanSpace ℂ (InfinitePlace E × ι) :=
    WithLp.toLp 2 (realCoord (V.vecAtPoint y))
  have h_far : ∀ y : L, m ≤ ‖f y‖ := fun ⟨_, hy, hy_ne⟩ ↦
    le_norm_realCoord V hc_ne hm_pos hm hy hy_ne
  have h_sep : Pairwise fun y z : L ↦ m ≤ ‖f y - f z‖ := fun ⟨_, hy, _⟩ ⟨_, hz, _⟩ hyz ↦
    le_norm_realCoord_sub V hc_ne hm_pos hm hy hz (Subtype.coe_ne_coe.2 hyz)
  have h_dim : Module.finrank ℝ (EuclideanSpace ℂ (InfinitePlace E × ι)) + 2 ≤ 2 * q := by
    simpa [finrank_real_of_complex, ← mul_add_one, le_of_lt] using hq
  exact ⟨h_far, tsum_inv_pow_le_of_separated hm_pos h_sep h_far h_dim⟩

open scoped Classical in
/-- Let `S`, `T` be hermitian spaces with signs `s`, `s'`, let `p` be an adelic point of the unitary
group of `S.hom T = Hom (S, T)`, whose signs are `homSigns s s' (i, k) = s' i * s k`, let `v`, `w`
be Fock vectors and let `y` be a rational vector. For a matrix `t` modulo the modulus `𝔪` with
additive character `Ψ_t = traceChar t`, the datum `v ⊗ Ψ_t ⊗ vac` (`modDatum`) is made of `v` at the
infinite places, `Ψ_t` at the places dividing `𝔪` and the vacuum vector elsewhere. Average over `t`
the pairing (`dataInner`) of `ω(p)(v ⊗ Ψ_t ⊗ vac)` with the Heisenberg translate `ϱ`, by the adelic
vector of `y` (`vecAtPoint`), of `ω(p)(w ⊗ Ψ_t ⊗ vac)`, where `ω` is the Weil action.

Let `x` be the adelic vector of `y` at the point of `Hom (S, T)` moved by `p`, with finite parts
`(x i).2`, and let `finCoord x` be these finite parts divided by the finite idele `α`. If
`finCoord x` is integral and vanishes modulo `𝔪`, the average is `fockInner v (realHeisenbergOp ξ
w) * ψf (traceOne * j / 2 * ∑ i, conj (x i).2 * (x i).2)`; otherwise it is `0`. Here
`realHeisenbergOp` is the Heisenberg action on the Fock space, `ξ = realCoord x` lists the
components of `x` at the infinite places `τ` times `√(2π Im τ(j))`, and `ψf` is the finite part of
the standard additive character. The idele `α` and the imaginary `j` in `E` are fixed by
`WeilData E`, and `traceOne = (1 - j⁻¹) / 2`. -/
lemma sum_dataInner_traceChar_div_card {𝔪 : Modulus E} (p : G E (homSigns s s'))
    (v w : fockSpace (realSigns E (homSigns s s'))) (y : n' × n → E) :
    let x : n' × n → 𝔸 E := ((S.hom T).move p).vecAtPoint y
    (∑ t : Matrix n n' 𝔪.ResidueRing,
        (S.hom T).dataInner ((S.hom T).ω p (modDatum S T 𝔪 (traceChar t) v))
          ((S.hom T).ϱ ((S.hom T).vecAtPoint y)
            ((S.hom T).ω p (modDatum S T 𝔪 (traceChar t) w)))) /
        Fintype.card (Matrix n n' 𝔪.ResidueRing) =
      if ∃ hx : ∀ i : n' × n, finCoord x i ∈ Ô E,
          ∀ i : n' × n, 𝔪.reduction ⟨finCoord x i, hx i⟩ = 0 then
        fockInner v (realHeisenbergOp (realCoord x) w) *
          ψf E ((traceOne * j / 2 : E) * ∑ i : n' × n, star (x i).2 * (x i).2)
      else 0 := by
  intro x
  -- Move `ω p` across the inner product, unfold the data and sum the characters over `t`. The
  -- idempotent of the places dividing `𝔪` does not change the class of an integral vector.
  have h_red (r : 𝔸f E) (hr : r ∈ Ô E) (hr' : idem 𝔪.places * r ∈ Ô E) :
      𝔪.reduction ⟨idem 𝔪.places * r, hr'⟩ = 𝔪.reduction ⟨r, hr⟩ := 𝔪.reduction_idem_mul ⟨r, hr⟩
  have h_term (t : Matrix n n' 𝔪.ResidueRing) :
      (S.hom T).dataInner ((S.hom T).ω p (modDatum S T 𝔪 (traceChar t) v))
          ((S.hom T).ϱ ((S.hom T).vecAtPoint y)
            ((S.hom T).ω p (modDatum S T 𝔪 (traceChar t) w))) =
        𝔪.liftFn (traceChar t ∘ vecToMatrix) (finCoord x) *
          (fockInner v (realHeisenbergOp (realCoord x) w) * vacuumFn (finVec (finCoord x))) := by
    simp [x, dataInner_omega_left, omega_rho, rep_apply_apply, dataInner_traceChar, vecAtPoint_move]
  simp only [h_term, ← sum_mul]
  by_cases hx : ∀ (i : n') (k : n), α⁻¹.val * (x (i, k)).2 ∈ Ô E
  · -- The sum of the characters `traceChar t` at a matrix vanishes unless the matrix is `0`.
    simp [finCoord, sum_addChar_trace_mul, isPrimitive_primAddChar, ← ext_iff, div_eq_inv_mul,
      liftFn_apply, traceChar, vecToMatrix, vacuumFn, finVec, hx, h_red, mul_mem, idem_mem_Ô]
  · -- Off the integral vectors the vacuum vanishes.
    simp [finCoord, vacuumFn, finVec, hx]

/-- Let the characters `a`, `b` of the unitary adeles of `E` (`AutChar`) have weights `γ`, `γ'` at
the infinite places and tame parts `ψ`, `ψ'` at the finite ones, and let `Ψ` be the average of the
characters `Ψ_t = traceChar t`, weighted by the conjugates of their theta kernels at `(g, h)`. Then
the kernel of `Ψ` at `(g u, h u')`, for real points `u`, `u'`, is the average over `t` of
`θ(ω(p)(w ⊗ Ψ_t ⊗ vac)) conj θ(ω(p)(v ⊗ Ψ_t ⊗ vac))`. Here `p = onHom (g, h)` is the point of
`Hom (S, T)` given by `(g, h)`, `ω` the untwisted adelic Weil action, `θ` the theta functional, `v`
the Fock vector of `Q` and `w = Ω(u, u') v`, with `Ω = realPairWeil γ γ'` the real Weil
representation of the pair twisted by powers of the determinants with exponents from `γ`, `γ'`. -/
lemma modKernel_expect_traceChar {a b : AutChar E} {γ γ' : InfinitePlace E → ℤ}
    {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ} {𝔪 : Modulus E}
    (ha : a.HasWeight γ ψ) (hb : b.HasWeight γ' ψ') (g : G E s) (h : G E s')
    (Q : MvPolynomial (InfinitePlace E × n' × n) ℂ) {v : fockSpace (realSigns E (homSigns s s'))}
    (hv : v = polyVector (realSigns E (homSigns s s')) Q) (u : GInf E s) (u' : GInf E s') :
    modKernel S T a b 𝔪 (𝔼 t : Matrix n n' 𝔪.ResidueRing,
        conj (modKernel S T a b 𝔪 (traceChar t) Q g h) • traceChar t) Q
        (g * (u, 1)) (h * (u', 1)) =
      (∑ t : Matrix n n' 𝔪.ResidueRing, (S.hom T).θ ((S.hom T).ω (G.onHom (g, h))
          (modDatum S T 𝔪 (traceChar t) (realPairWeil γ γ' (u, u') v))) *
        conj ((S.hom T).θ ((S.hom T).ω (G.onHom (g, h)) (modDatum S T 𝔪 (traceChar t) v)))) /
        Fintype.card (Matrix n n' 𝔪.ResidueRing) := by
  classical
  -- The unit scalar that `a`, `b` contribute at `(g, h)` cancels against its conjugate.
  have phase_cancel (f f' : 𝒮 (S.hom T)) :
      pairWeil S T a b (g, h) f 0 * conj (pairWeil S T a b (g, h) f' 0) =
        (S.hom T).ω (G.onHom (g, h)) f 0 * conj ((S.hom T).ω (G.onHom (g, h)) f' 0) := by
    calc _ = (pairChar a b (g, h) : ℂ) * conj (pairChar a b (g, h) : ℂ) *
          ((S.hom T).ω (G.onHom (g, h)) f 0 * conj ((S.hom T).ω (G.onHom (g, h)) f' 0)) := by
          simp [pairWeil]
          ring
      _ = _ := by rw [Complex.mul_conj', show ‖pairChar a b (g, h)‖ = 1 from norm_coe _, ofReal_one,
          one_pow, one_mul]
  -- By `pairWeil_integrated`, which uses the weights `ha` and `hb`, the real points act on `v` by
  -- `realPairWeil γ γ'`.
  have h_real (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) :
      pairWeil S T a b (g * (u, 1), h * (u', 1)) (modDatum S T 𝔪 Ψ v) =
        pairWeil S T a b (g, h) (modDatum S T 𝔪 Ψ (realPairWeil γ γ' (u, u') v)) := by
    simp [← Prod.mk_mul_mk, modDatum, pairWeil_integrated (γ := γ) (γ' := γ')]
  rw [← modKernelBilin_apply]
  -- By linearity the kernel of the average is the average of the kernels.
  simp [modKernel, pairTheta, mul_comm (conj _), h_real, expect, NNRat.smul_def, ← hv,
    div_eq_inv_mul, phase_cancel]

/-- Let `S`, `T` be hermitian spaces over `E` with signs `s`, `s'`, let `g`, `h` be points of their
adelic unitary groups, and let `a`, `b` be characters of the unitary adeles of `E` with weights `γ`,
`γ'` and tame parts `ψ`, `ψ'` (`HasWeight`). The class `WeilData E` fixes an imaginary element `j`
of `E` and a finite idele `α` that makes `Ô E` self-dual for the pairing `ψ_f(j α ᾱ z z')`. Let
`c ≠ 0` be such that `c α z` is integral for every `z` in `Ô E` that vanishes modulo `𝔪`. Let `λ` be
the first minimum of `Hom (S, T)` with the points moved by `g` and `h`, let `m > 0` satisfy
`m |Φ w c| ≤ √(2π Im (Φ w j)) λ` at all infinite places `w`, and let `q` exceed the number of
complex variables. Let `Q` be homogeneous of degree `d` under real scalings, with Fock vector `v`.

For a function `Ψ` on matrices modulo `𝔪`, the theta kernel `modKernel S T a b 𝔪 Ψ Q` sends a pair
of points `p` to `θ(ω_{a,b}(p)(v ⊗ Ψ ⊗ vac))`: the theta functional of the datum made of `v` at the
infinite places, `Ψ` at the places dividing `𝔪` and the vacuum elsewhere, moved by the Weil action
twisted by `a` and `b`. Then some `Ψ` has the property that, for all real points `u`, `u'`, this
kernel at `(g u, h u')` is within `(100 (d + 2q) / m²) ^ q (‖u‖ ‖u'‖) ^ (3q) |⟨v, v⟩|` of
`⟨v, Ω(u, u') v⟩`. Here `Ω` is the real Weil representation `realPairWeil γ γ'`, on the Fock space
for the signs `(τ, (i, k)) ↦ s' i * s k`, and `‖u‖ = maxOpNorm u` is the largest operator norm of
`u` at a place. -/
theorem exists_norm_modKernel_sub_fockInner_le [Nonempty n] [Nonempty n']
    {a b : AutChar E} {γ γ' : InfinitePlace E → ℤ}
    {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ} {𝔪 : Modulus E} {g : G E s}
    (ha : a.HasWeight γ ψ) (hb : b.HasWeight γ' ψ') {c : E} (hc_ne : c ≠ 0)
    (hc : ∀ z : Ô E, 𝔪.reduction z = 0 → (c : 𝔸f E) * (α.val * z.val) ∈ Ô E) (h : G E s') (m : ℝ)
    (q : ℕ) (hm_pos : 0 < m)
    (hm : ∀ w : InfinitePlace E, m * ‖Φ w c‖ ≤
      √(2 * Real.pi * (Φ w j).im) * ((S.move g).hom (T.move h)).firstMinimum)
    (hq : Fintype.card (InfinitePlace E × n' × n) < q)
    (Q : MvPolynomial (InfinitePlace E × n' × n) ℂ) {v : fockSpace (realSigns E (homSigns s s'))}
    (hv : v = polyVector (realSigns E (homSigns s s')) Q) (d : ℕ)
    (hQ : ∀ (r : ℝ) (x : InfinitePlace E × n' × n → ℂ), Q.eval (r • x) = r ^ d * Q.eval x) :
    ∃ Ψ : Matrix n' n 𝔪.ResidueRing → ℂ, ∀ (u : GInf E s) (u' : GInf E s'),
      ‖modKernel S T a b 𝔪 Ψ Q (g * (u, 1)) (h * (u', 1)) -
          fockInner v (realPairWeil γ γ' (u, u') v)‖ ≤
        maxOpNorm u' ^ (3 * q) * (100 * (d + 2 * q) / m ^ 2) ^ q * ‖fockInner v v‖ *
          maxOpNorm u ^ (3 * q) := by
  classical
  -- Take for `Ψ` the mean of the characters `traceChar t`, weighted by the conjugates of their
  -- kernels at `(g, h)`. Its kernel is a mean of products of thetas, hence a sum of terms `term y`
  -- over rational `y`. The term `y = 0` is the Fock coefficient; the others live on an
  -- `m`-separated set and decay fast.
  refine ⟨𝔼 t, conj (modKernel S T a b 𝔪 (traceChar t) Q g h) • traceChar t, fun u u' ↦ ?_⟩
  let p : G E (homSigns s s') := G.onHom (g, h)
  let V : Space E (n' × n) (homSigns s s') := (S.hom T).move p
  rw [show (S.move g).hom (T.move h) = V by
    simp [V, p, move, Space.hom, Units.ext_iff, mul_kronecker_mul, G.onHom]] at hm
  let L : Set (n' × n → E) := {y | c • y ∈ V.baseLattice ∧ y ≠ 0}
  let len (y : n' × n → E) : ℝ := ‖WithLp.toLp 2 (realCoord (V.vecAtPoint y))‖
  obtain ⟨h_far, h_summable, h_tsum⟩ : (∀ y : L, m ≤ len y) ∧
      Summable (fun y : L ↦ (len y)⁻¹ ^ (2 * q)) ∧
      ∑' y : L, (len y)⁻¹ ^ (2 * q) ≤ (5 / m) ^ (2 * q) :=
    tsum_inv_norm_realCoord_pow_le V hc_ne hm_pos hm hq
  -- The mean over `t` of the products of thetas is a sum over rational vectors.
  let w : fockSpace (realSigns E (homSigns s s')) := realPairWeil γ γ' (u, u') v
  let φ (t : Matrix n n' 𝔪.ResidueRing) (f : fockSpace (realSigns E (homSigns s s'))) :
    𝒮 (S.hom T) :=
    (S.hom T).ω p (modDatum S T 𝔪 (traceChar t) f)
  let mean : ℂ := (∑ t, (S.hom T).θ (φ t w) * conj ((S.hom T).θ (φ t v))) /
    card (Matrix n n' 𝔪.ResidueRing)
  let term (y : n' × n → E) : ℂ :=
    (∑ t, (S.hom T).dataInner (φ t v) ((S.hom T).ϱ ((S.hom T).vecAtPoint y) (φ t w))) /
      card (Matrix n n' 𝔪.ResidueRing)
  have h_sum : HasSum term mean :=
    (hasSum_sum fun t _ ↦ hasSum_dataInner _ (φ t w) (φ t v)).div_const _
  let x (y : n' × n → E) : n' × n → 𝔸 E := V.vecAtPoint y
  let χ (y : n' × n → E) : Circle :=
    ψf E ((traceOne * j / 2 : E) * ∑ i, star (x y i).2 * (x y i).2)
  have term_eq (y : n' × n → E) : term y =
      if ∃ hx : ∀ i, finCoord (x y) i ∈ Ô E, ∀ i, 𝔪.reduction ⟨finCoord (x y) i, hx i⟩ = 0 then
        fockInner v (realHeisenbergOp (realCoord (x y)) w) * χ y
      else 0 :=
    sum_dataInner_traceChar_div_card T p v w y
  -- By `hc`, the condition in `term_eq` puts `c • y` in the lattice.
  have h_supp : Function.support (fun y ↦ if y = 0 then 0 else term y) ⊆ L := by
    intro y hy
    obtain ⟨y_ne, term_ne⟩ := ite_ne_left_iff.1 hy
    obtain ⟨⟨hz, hz_zero⟩, -⟩ := ite_ne_right_iff.1 ((term_eq y).symm.trans_ne term_ne.symm)
    exact ⟨fun i ↦ by simpa [x, finCoord] using hc _ (hz_zero i), y_ne⟩
  -- Removing the term `y = 0` leaves the difference to be bounded, as a sum over `L`.
  have h_rest : HasSum (fun y : L ↦ if y.val = 0 then 0 else term y) (mean - term 0) :=
    (hasSum_subtype_iff_of_support_subset h_supp).2 (hasSum_ite_sub_hasSum h_sum 0)
  -- Each term decays like a Heisenberg matrix coefficient of the Fock vector `v`.
  set dim : ℕ := card (InfinitePlace E × n' × n)
  let σ : USign (realSigns E (homSigns s s')) := pairHomInf (u, u')
  let normσ : ℝ := ‖(σ : Matrix (InfinitePlace E × n' × n) (InfinitePlace E × n' × n) ℂ)‖
  have term_le (y : L) :
      ‖if y.val = 0 then 0 else term y‖ ≤
        normσ ^ (dim + 2 * q) * (fockInner v v).re * (4 * ((d + dim : ℕ) + q)) ^ q *
          (len y)⁻¹ ^ (2 * q) := by
    calc _ ≤ ‖fockInner v (realHeisenbergOp (realCoord (x y)) (realWeil σ v))‖ := by
          rw [term_eq]
          split_ifs <;> simp [w, σ, realPairWeil, prod_mul_distrib, norm_coe]
      _ ≤ _ := norm_fockInner_realHeisenbergOp_le σ hv hQ le_rfl (hm_pos.trans_le (h_far y))
  have h_zero : term 0 = fockInner v w := by
    simp [term_eq, x, χ, finCoord, ← ZeroMemClass.zero_def, realCoord.eq_unfold, ← Pi.zero_def]
  rw [modKernel_expect_traceChar T ha hb g h Q hv u u', ← h_zero]
  -- Sum the bounds of the terms, use `dim ≤ q`, and collect the constants: `100 = 4 * 5 ^ 2`.
  calc ‖mean - term 0‖
      ≤ normσ ^ (dim + 2 * q) * (fockInner v v).re * (4 * ((d + dim : ℕ) + q)) ^ q *
          ∑' y : L, (len y)⁻¹ ^ (2 * q) :=
        h_rest.norm_le_of_bounded (h_summable.hasSum.mul_left _) term_le
    _ ≤ (maxOpNorm u * maxOpNorm u') ^ (q + 2 * q) * ‖fockInner v v‖ * (4 * ((d + q : ℕ) + q)) ^ q *
        (5 / m) ^ (2 * q) := by
      have one_le : 1 ≤ normσ := U.one_le_norm σ
      have normσ_le : normσ ≤ maxOpNorm u * maxOpNorm u' := norm_pairHomInf_le_mul u u'
      grw [re_le_norm, h_tsum, hq, hq, normσ_le]
    _ = _ := by
      rw [mul_assoc _ _ ((5 / m) ^ _), pow_mul (5 / m), ← mul_pow]
      push_cast
      ring

end New.Rows

/-!
## Integrals of holomorphic discrete series coefficients and isolation

Archimedean estimates on `New.GInf E s`, the product of the groups `U(diag s)` over the `f`
infinite places. `New.holMinorsPi s k` is the basic function `Min^hol` of weight `k`, a product of
quotients of principal minors, written `m_k`. For dominant `k` (`New.IsKDominant`) with a large gap
between the two sign blocks (`New.HasHolGap`) it is a matrix coefficient of a holomorphic discrete
series. Below, `u`, `u'` are two such weights, the entries of `u` at most `5 b` in modulus, and
`b = D.b`, `n_* = New.Data.nStar D` for admissible data `D`.

* `New.Data.integral_norm_holMinorsPi_mul_pow_le`: `∫ |m_u|²` is positive, and
  `∫ |m_u'(h)| |h| ^ (6 n_*) dh ≤ b ^ n_* ∫ |m_u|²`.
* `New.Data.integrable_mul_holMinorsPi`: a continuous function of growth at most
  `C |h| ^ (6 n_*)` is integrable against `m_u'`, with integral at most `C b ^ n_* ∫ |m_u|²`.
* `New.Data.integrable_holMinorsPi`: `m_u` is integrable; the bound on its entries is not needed.
-/

section Isolation

open MeasureTheory Matrix Norms.L2Operator Finset Fintype AddCircle NumberField

namespace New.Rows

/-- A point of the archimedean unitary group has operator norm at least `1` at every place, so the
largest of these norms is at least `1`. -/
@[bound] theorem one_le_maxOpNorm {E n : Type} [Field E] [NumberField E] [Fintype n]
    [DecidableEq n] [Nonempty n] {s : n → ℤˣ} (h : GInf E s) : 1 ≤ maxOpNorm h := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  exact (U.one_le_norm (h w)).trans (norm_le_pi_norm (fun w ↦ (h w : Matrix n n ℂ)) w)

end New.Rows

namespace New.Data

open Rows DiscreteSeries

/-- Let `D` be admissible data, with weight `b = D.b` and rank step `t = D.t`; in such data `b` is
very large against `t`. For natural numbers `n ≤ t` and `L ≤ 10 b + t`, the constant
`8 (2000 (n + L + 1)⁶) ^ (2 n²) 2 ^ (10 n³)` of `New.integral_tail_le` is at most
`2 ^ (13 t³) b ^ (14 t²)`. -/
lemma eight_mul_pow_mul_two_pow_le {P : Parameters} (D : Data P) {n L : ℕ} (hn : n ≤ D.t)
    (hL : (L : ℝ) ≤ 2 * (5 * D.b) + D.t) :
    (8 * (2000 * (n + L + 1) ^ 6) ^ (2 * n ^ 2) * 2 ^ (10 * n ^ 3) : ℝ) ≤
      2 ^ (13 * D.t ^ 3) * D.b ^ (14 * D.t ^ 2) := by
  -- `le_of_hasLogBound` compares the logarithms of both sides: `b` is huge against `t`.
  have hbase : (2000 * (n + L + 1) ^ 6 : ℝ) ≤ D.b ^ 7 := by
    grw [hL, hn]
    exact D.le_of_hasLogBound
  have hb : 1 ≤ D.b ^ 7 := D.le_of_hasLogBound
  calc _ ≤ 2 ^ (3 * 1) * (D.b ^ 7) ^ (2 * n ^ 2) * 2 ^ (10 * n ^ 3) := by grw [hbase]; norm_num
    _ ≤ 2 ^ (3 * D.t ^ 3) * (D.b ^ 7) ^ (2 * D.t ^ 2) * 2 ^ (10 * D.t ^ 3) := by
        gcongr
        exacts [one_le_two, Nat.one_le_pow _ _ D.t_odd.pos, one_le_two]
    _ = _ := by ring

/-- Let `D` be admissible data, with weight `b = D.b`, rank step `t = D.t`, number `f = D.f` of
infinite places and `n_* = nStar D = 2 f t³`. Then the tail bound `B = 2 ^ (13 t³) b ^ (14 t²)` of
`integrable_tail_and_integral_le` satisfies `2 ^ (6 n_*) B ^ f ≤ b ^ n_*`. -/
lemma two_pow_mul_pow_f_le_b_pow_nStar {P : Parameters} (D : Data P) :
    2 ^ (6 * nStar D) * (2 ^ (13 * D.t ^ 3) * D.b ^ (14 * D.t ^ 2)) ^ D.f ≤ D.b ^ nStar D := by
  have hb : 1 ≤ D.b := D.le_of_hasLogBound
  have hb_large : 2 ^ 25 ≤ D.b := D.le_of_hasLogBound
  have ht : 14 ≤ D.t := D.nat_le_of_hasLogBound
  calc _ = (2 ^ 25) ^ (D.f * D.t ^ 3) * D.b ^ (D.f * (14 * D.t ^ 2)) := by
        rw [← pow_mul]
        ring
    _ ≤ D.b ^ (D.f * D.t ^ 3) * D.b ^ (D.f * (D.t * D.t ^ 2)) := by gcongr
    _ = _ := by ring

variable {P : Parameters} {D : Data P} {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
  {s : n → ℤˣ} {o : n → ℤ} {u u' : D.Φ → n → ℤ}

attribute [fun_prop] IsHolOfWeight IsHolOfWeight.continuous

omit [DecidableEq n] [Nonempty n] in
/-- For admissible data `D` and rank `n ≤ t = D.t` we have `2 n³ ≤ n_*`,
where `n_* = nStar D = 2 f t³`, since there are `f ≥ 1` infinite places. -/
lemma two_mul_card_pow_three_le_nStar (h_rank : card n ≤ D.t) : 2 * card n ^ 3 ≤ nStar D :=
  (by gcongr : 2 * card n ^ 3 ≤ 2 * D.t ^ 3).trans (Nat.le_mul_of_pos_left _ card_pos)

omit [DecidableEq n] in
/-- In rank `n ≥ 1` the order of decay `10 n³` exceeds `8 n²`, the threshold for integrability on
`U(diag s)`. -/
lemma eight_mul_card_sq_lt : 8 * card n ^ 2 < 10 * card n ^ 3 := by
  linarith [Nat.pow_le_pow_right (card_pos (α := n)) (Nat.le_succ 2),
    Nat.pow_pos (n := 2) (card_pos (α := n))]

/-- In rank `1 ≤ n ≤ t = D.t` let the order `o` put the signs `+1` first, and let the weight `v` be
dominant within each sign block, with gap `300 n_*` between the blocks, `n_* = nStar D`. Let
`2 ρ = twoRho (-o) ⊤`, with entries `#{j | o i < o j} - #{j | o j < o i}`. Then `l = 2 v + 2 ρ` is a
doubled Harish-Chandra parameter of gap `500 n³ + 8 n_*`, and its discrete series coefficient
`dsCoeff` is `holMinors s v`: the quotient `m_{v+c} / m_c` of products of principal minors, where
`c i = 2 ∑ |v j|` at a sign `+1` and `c i = 0` otherwise. -/
lemma hasLargeGap_and_dsCoeff_eq_holMinors (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    {v : n → ℤ} (hv_dom : IsKDominant s o v) (hv_gap : HasHolGap s v (300 * nStar D)) :
    let l : HCParam s := 2 * v + twoRho (-o) ⊤
    l.HasLargeGap (8 * nStar D) ∧ ∀ g : USign s, l.dsCoeff g = holMinors s v g := by
  have hgap : 500 * card n ^ 3 + 8 * nStar D + card n + 1 < 300 * nStar D := by
    linarith [two_mul_card_pow_three_le_nStar h_rank, Nat.le_self_pow three_ne_zero (card n),
      Fintype.card_pos (α := n)]
  exact dsCoeff_eq_holMinors ho (8 * nStar D) (300 * nStar D) v hv_dom hv_gap hgap

/-- Let `D` be admissible data, `b = D.b`, `t = D.t`, and let the rank satisfy `1 ≤ n ≤ t`. For an
integer function `o` on the indices let `2 ρ = twoRho (-o) ⊤`, with entries
`#{j | o i < o j} - #{j | o j < o i}`. Let `l = 2 v + 2 ρ` be a doubled Harish-Chandra parameter of
gap `500 n³ + gap`, with `|v i| ≤ 5 b` for all `i`. Then the tail `deg(l) (2 / ‖g‖) ^ (10 n³)`, with
`deg` the formal degree, is integrable on `U(diag s)`, with integral at most
`2 ^ (13 t³) b ^ (14 t²)`. -/
lemma integrable_tail_and_integral_le (h_rank : card n ≤ D.t) {v : n → ℤ} {l : HCParam s}
    {gap : ℕ} (hl : l = 2 * v + twoRho (-o) ⊤) (hl_gap : l.HasLargeGap gap)
    (hv_le : ∀ i : n, |(v i : ℝ)| ≤ 5 * D.b) :
    let tail (g : USign s) : ℝ := l.formalDegree * (2 / ‖(g : Matrix n n ℂ)‖) ^ (10 * card n ^ 3)
    Integrable tail ∧ ∫ g : USign s, tail g ≤ 2 ^ (13 * D.t ^ 3) * D.b ^ (14 * D.t ^ 2) := by
  intro tail
  let L : ℕ := 2 * ⌊5 * D.b⌋₊ + card n
  have hl_le (i : n) : |l i| ≤ L := by
    have hv_floor : (v i).natAbs ≤ ⌊5 * D.b⌋₊ := Nat.le_floor (by simpa using hv_le i)
    have hρ : |twoRho (-o) ⊤ i| ≤ card n := abs_twoRho_le ⊤ i (-o)
    calc |l i| = |2 * v i + twoRho (-o) ⊤ i| := by simp [hl]
      _ ≤ 2 * (v i).natAbs + |twoRho (-o) ⊤ i| := (abs_add_le _ _).trans_eq (by simp)
      _ ≤ L := by lia
  have hL : (L : ℝ) ≤ 2 * (5 * D.b) + D.t := by
    push_cast [L]
    grw [Nat.floor_le (by positivity), h_rank]
  obtain ⟨hint, hle⟩ : Integrable tail ∧ ∫ g : USign s, tail g ≤
      8 * (2000 * (card n + L + 1) ^ 6) ^ (2 * card n ^ 2) * 2 ^ (10 * card n ^ 3) :=
    integral_tail_le (hg := hl_gap) hl_le (10 * card n ^ 3) eight_mul_card_sq_lt
  exact ⟨hint, hle.trans (D.eight_mul_pow_mul_two_pow_le h_rank hL)⟩

/-- In rank `1 ≤ n ≤ t = D.t` let the order `o` put the signs `+1` first, and let the weights `u' τ`
be dominant within each sign block, with gap `300 n_*` between the blocks, `n_* = nStar D`. Then
`|m_u'(h)| |h| ^ (6 n_*) ≤ 2 ^ (6 n_*) ∏_τ (2 / ‖h τ‖) ^ (10 n³)` for `h` in the archimedean group
`GInf D.E s`. Here `τ` runs over the infinite places, `m_u' = holMinorsPi s u'` is the product
over `τ` of the quotients of minors `holMinors s (u' τ)`, and `|h| = maxOpNorm h` is the largest
of the operator norms `‖h τ‖`. -/
lemma norm_holMinorsPi_mul_pow_le (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu'_dom : ∀ τ : D.Φ, IsKDominant s o (u' τ))
    (hu'_gap : ∀ τ : D.Φ, HasHolGap s (u' τ) (300 * nStar D)) (h : GInf D.E s) :
    ‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D) ≤
      2 ^ (6 * nStar D) * ∏ τ : D.Φ, (2 / ‖(h τ : Matrix n n ℂ)‖) ^ (10 * card n ^ 3) := by
  -- Use `6 n_*` more powers of decay at a place `a` of largest norm.
  obtain ⟨a, ha⟩ : ∃ a : D.Φ, ‖(h a : Matrix n n ℂ)‖ = maxOpNorm h := (IsGreatest.pi_norm _).1
  have ha_ne : ‖(h a : Matrix n n ℂ)‖ ≠ 0 := (one_pos.trans_le (U.one_le_norm (h a))).ne'
  have hdecay (τ : D.Φ) : ‖holMinors s (u' τ) (h τ)‖ ≤
      (2 / ‖(h τ : Matrix n n ℂ)‖) ^ (10 * card n ^ 3 + if τ = a then 6 * nStar D else 0) := by
    let l : HCParam s := 2 * u' τ + twoRho (-o) ⊤
    obtain ⟨hgap, hcoeff⟩ : l.HasLargeGap (8 * nStar D) ∧
        ∀ g : USign s, l.dsCoeff g = holMinors s (u' τ) g :=
      hasLargeGap_and_dsCoeff_eq_holMinors h_rank ho (hu'_dom τ) (hu'_gap τ)
    rw [← hcoeff]
    exact norm_dsCoeff_le_pow hgap (by lia) (h τ)
  calc ‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D)
      ≤ (∏ τ, (2 / ‖(h τ : Matrix n n ℂ)‖) ^ (10 * card n ^ 3 + if τ = a then 6 * nStar D else 0)) *
          ‖(h a : Matrix n n ℂ)‖ ^ (6 * nStar D) := by
        grw [holMinorsPi, norm_prod, hdecay, ha]
    _ = (∏ τ, (2 / ‖(h τ : Matrix n n ℂ)‖) ^ (10 * card n ^ 3)) *
          (2 / ‖(h a : Matrix n n ℂ)‖ * ‖(h a : Matrix n n ℂ)‖) ^ (6 * nStar D) := by
        simp only [pow_add, prod_mul_distrib, pow_ite, pow_zero, Fintype.prod_ite_eq', mul_pow,
          mul_assoc]
    _ = _ := by rw [div_mul_cancel₀ _ ha_ne, mul_comm]

/-- In rank `1 ≤ n ≤ t = D.t` let the order `o` put the signs `+1` first, and let the weights `u τ`
be dominant within each sign block, with gap `300 n_*` between the blocks, `n_* = nStar D`. Then
`|m_u(h)| |h| ^ (6 n_*)` is integrable on `GInf D.E s`, the product of the groups `U(diag s)` over
the infinite places `τ` of `D.E`. Here `m_u = holMinorsPi s u` is the product over `τ` of the
quotients of minors `holMinors s (u τ)` of weight `u τ`, and `|h| = maxOpNorm h` is the largest of
the operator norms `‖h τ‖`. -/
lemma integrable_norm_holMinorsPi_mul_pow (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D)) :
    Integrable fun h : GInf D.E s ↦ ‖holMinorsPi s u h‖ * maxOpNorm h ^ (6 * nStar D) := by
  have hcont : Continuous (holMinorsPi s u) := (isHolOfWeight_holMinorsPi ho hu_dom).continuous
  have hdom_int : Integrable fun h : GInf D.E s ↦
      2 ^ (6 * nStar D) * ∏ τ : D.Φ, (2 / ‖(h τ : Matrix n n ℂ)‖) ^ (10 * card n ^ 3) :=
    (Integrable.fintype_prod fun _ ↦ integrable_two_div_norm_pow eight_mul_card_sq_lt).const_mul _
  exact hdom_int.mono' (by fun_prop) (.of_forall fun h ↦ by
    simpa [abs_of_nonneg] using norm_holMinorsPi_mul_pow_le h_rank ho hu_dom hu_gap h)

omit [Nonempty n] in
/-- If the factor `holMinors s (u τ)` of `m_u = holMinorsPi s u` is the discrete series coefficient
of parameter `l τ` at every infinite place `τ`, then `∫ |m_u|²` is the inverse of the product of
the formal degrees of the `l τ`. -/
lemma integral_norm_holMinorsPi_sq_eq_inv_prod {l : D.Φ → HCParam s}
    (hl_coeff : ∀ (τ : D.Φ) (g : USign s), (l τ).dsCoeff g = holMinors s (u τ) g) :
    ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 = (∏ τ : D.Φ, (l τ).formalDegree)⁻¹ := by
  simp [holMinorsPi, HCParam.formalDegree, prod_pow, ← integral_fintype_prod_volume_eq_prod,
    hl_coeff]

/-- In rank `1 ≤ n ≤ t = D.t` let the order `o` put the signs `+1` first, and let the weights `u τ`
be dominant within each sign block, with gap `300 n_*` between the blocks, `n_* = nStar D`. Then
`∫ |m_u|² > 0`, with the integral over `GInf D.E s`, the product of the groups `U(diag s)` over
the infinite places `τ` of `D.E`. Here `m_u = holMinorsPi s u` is the product over `τ` of the
quotients of minors `holMinors s (u τ)` of weight `u τ`. -/
lemma integral_norm_holMinorsPi_sq_pos (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D)) :
    0 < ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 := by
  let l (τ : D.Φ) : HCParam s := 2 * u τ + twoRho (-o) ⊤
  obtain ⟨hl_gap, hl_coeff⟩ : (∀ τ : D.Φ, (l τ).HasLargeGap (8 * nStar D)) ∧
      ∀ (τ : D.Φ) (g : USign s), (l τ).dsCoeff g = holMinors s (u τ) g :=
    forall_and.1 fun τ ↦ hasLargeGap_and_dsCoeff_eq_holMinors h_rank ho (hu_dom τ) (hu_gap τ)
  simpa only [integral_norm_holMinorsPi_sq_eq_inv_prod hl_coeff, inv_pos] using
    (prod_pos fun τ _ ↦ formalDegree_pos (hl_gap τ))

/-- Let `D` be admissible data, `b = D.b`, `t = D.t`, `n_* = nStar D`, and let the rank satisfy
`1 ≤ n ≤ t`. Let the order `o` put the signs `+1` first. Let the weights `u τ`, `u' τ` at the
infinite places `τ` be dominant within each sign block, with gap `300 n_*` between the blocks, and
let `u` have entries of modulus at most `5 b`. Write `m_u = holMinorsPi s u` for the product of
quotients of minors of weight `u`, and `|h| = maxOpNorm h` for the largest operator norm of `h` at
a place. Then `∫ |m_u|² > 0`, and `|m_u'(h)| |h| ^ (6 n_*)` is integrable with integral at most
`b ^ n_* ∫ |m_u|²`. -/
theorem integral_norm_holMinorsPi_mul_pow_le (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ)) (hu'_dom : ∀ τ : D.Φ, IsKDominant s o (u' τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D))
    (hu'_gap : ∀ τ : D.Φ, HasHolGap s (u' τ) (300 * nStar D))
    (hu_le : ∀ (τ : D.Φ) (i : n), |(u τ i : ℝ)| ≤ 5 * D.b) :
    0 < ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 ∧
    Integrable (fun h : GInf D.E s ↦ ‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D)) ∧
    ∫ h : GInf D.E s, ‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D) ≤
      D.b ^ nStar D * ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 := by
  refine ⟨integral_norm_holMinorsPi_sq_pos h_rank ho hu_dom hu_gap,
    integrable_norm_holMinorsPi_mul_pow h_rank ho hu'_dom hu'_gap, ?_⟩
  -- At each place the factors of `m_u` and `m_u'` are discrete series coefficients. So the
  -- integrand is at most `2 ^ (6 n_*) ∫ |m_u|²` times a product of tails
  -- `deg * (2 / ‖g‖) ^ (10 n³)`; the formal degrees are those of `u`, with product `(∫ |m_u|²)⁻¹`.
  let l (τ : D.Φ) : HCParam s := 2 * u τ + twoRho (-o) ⊤
  obtain ⟨hl_gap, hl_coeff⟩ : (∀ τ, (l τ).HasLargeGap (8 * nStar D)) ∧
      ∀ (τ : D.Φ) (g : USign s), (l τ).dsCoeff g = holMinors s (u τ) g :=
    forall_and.1 fun τ ↦ hasLargeGap_and_dsCoeff_eq_holMinors h_rank ho (hu_dom τ) (hu_gap τ)
  let tail (τ : D.Φ) (g : USign s) : ℝ :=
    (l τ).formalDegree * (2 / ‖(g : Matrix n n ℂ)‖) ^ (10 * card n ^ 3)
  obtain ⟨htail_int, htail_le⟩ : (∀ τ : D.Φ, Integrable (tail τ)) ∧
      ∀ τ : D.Φ, ∫ g, tail τ g ≤ 2 ^ (13 * D.t ^ 3) * D.b ^ (14 * D.t ^ 2) :=
    forall_and.1 fun τ ↦ integrable_tail_and_integral_le h_rank rfl (hl_gap τ) (hu_le τ)
  set I : ℝ := ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2
  have hI : I = (∏ τ, (l τ).formalDegree)⁻¹ := integral_norm_holMinorsPi_sq_eq_inv_prod hl_coeff
  have hdeg_pos (τ : D.Φ) : 0 < (l τ).formalDegree := formalDegree_pos (hl_gap τ)
  have hbound (h : GInf D.E s) : ‖‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D)‖ ≤
      2 ^ (6 * nStar D) * I * ∏ τ, tail τ (h τ) := by
    rw [Real.norm_of_nonneg (by positivity), hI, prod_mul_distrib, mul_assoc,
      inv_mul_cancel_left₀ (prod_pos fun τ _ ↦ hdeg_pos τ).ne']
    exact norm_holMinorsPi_mul_pow_le h_rank ho hu'_dom hu'_gap h
  have hI_pos : 0 < I := integral_norm_holMinorsPi_sq_pos h_rank ho hu_dom hu_gap
  calc _ ≤ ∫ h : GInf D.E s, 2 ^ (6 * nStar D) * I * ∏ τ, tail τ (h τ) :=
        (le_abs_self _).trans (norm_integral_le_of_norm_le
          ((Integrable.fintype_prod htail_int).const_mul _) (.of_forall hbound))
    _ = 2 ^ (6 * nStar D) * (∏ τ, ∫ g, tail τ g) * I := by
        rw [integral_const_mul, integral_fintype_prod_volume_eq_prod, mul_right_comm]
    _ ≤ 2 ^ (6 * nStar D) * (∏ _τ : D.Φ, 2 ^ (13 * D.t ^ 3) * D.b ^ (14 * D.t ^ 2)) * I := by
        gcongr with τ
        exacts [fun τ _ ↦ integral_nonneg fun g ↦ mul_nonneg (hdeg_pos τ).le (by positivity),
          htail_le τ]
    _ ≤ D.b ^ nStar D * I := by grw [prod_const, card_univ, D.two_pow_mul_pow_f_le_b_pow_nStar]

/-- Let `D` be admissible data (`Data P`), `b = D.b`, `t = D.t`, `n_* = nStar D`, and let the index
type `n` be nonempty with `card n ≤ t`. Let `s` be signs and let the order `o` put the indices of
sign `+1` first. Let the weights `u`, `u'` be K-dominant for `o` within each sign block, with gap
`300 n_*` between the blocks, and let the entries of `u` be at most `5 b` in modulus. Write
`m_u = holMinorsPi s u` and `|h| = maxOpNorm h` for `h` in `GInf D.E s`. If `A` is continuous on
`GInf D.E s` and `|A h| ≤ C |h| ^ (6 n_*)`, then `A m_u'` is integrable and
`|∫ A m_u'| ≤ C b ^ n_* ∫ |m_u|²`. -/
theorem integrable_mul_holMinorsPi (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ)) (hu'_dom : ∀ τ : D.Φ, IsKDominant s o (u' τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D))
    (hu'_gap : ∀ τ : D.Φ, HasHolGap s (u' τ) (300 * nStar D))
    (hu_le : ∀ (τ : D.Φ) (i : n), |(u τ i : ℝ)| ≤ 5 * D.b)
    {A : GInf D.E s → ℂ} {C : ℝ} (hA : Continuous A)
    (hA_le : ∀ h : GInf D.E s, ‖A h‖ ≤ C * maxOpNorm h ^ (6 * nStar D)) :
    Integrable (A * holMinorsPi s u') ∧
    ‖∫ h : GInf D.E s, A h * holMinorsPi s u' h‖ ≤
      C * D.b ^ nStar D * ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 := by
  obtain ⟨-, hint, hle⟩ : 0 < ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 ∧
      Integrable (fun h : GInf D.E s ↦ ‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D)) ∧
      ∫ h : GInf D.E s, ‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D) ≤
        D.b ^ nStar D * ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 :=
    integral_norm_holMinorsPi_mul_pow_le h_rank ho hu_dom hu'_dom hu_gap hu'_gap hu_le
  have hC : 0 ≤ C := by simpa [maxOpNorm] using (norm_nonneg _).trans (hA_le 1)
  have hcont : Continuous (holMinorsPi s u') := (isHolOfWeight_holMinorsPi ho hu'_dom).continuous
  have hbound (h : GInf D.E s) : ‖A h * holMinorsPi s u' h‖ ≤
      C * (‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D)) := by
    grw [norm_mul, hA_le, mul_assoc, mul_comm (maxOpNorm h ^ _)]
  refine ⟨(hint.const_mul C).mono' (by fun_prop) (.of_forall hbound), ?_⟩
  calc _ ≤ ∫ h : GInf D.E s, C * (‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D)) :=
        norm_integral_le_of_norm_le (hint.const_mul C) (.of_forall hbound)
    _ ≤ _ := by grw [integral_const_mul, hle, mul_assoc]

/-- Let `D : Data P`, `t = D.t`, `n_* = nStar D`, and let the rank satisfy `1 ≤ n ≤ t`. Let the
order `o` put the signs `+1` first, and let the weights `u τ` be dominant within each sign block,
with gap `300 n_*` between the blocks. Then `holMinorsPi s u`, the product of quotients of minors of
weight `u`, is integrable. -/
theorem integrable_holMinorsPi (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D)) :
    Integrable (holMinorsPi s u) := by
  have hbound (h : GInf D.E s) :
      ‖holMinorsPi s u h‖ ≤ ‖holMinorsPi s u h‖ * maxOpNorm h ^ (6 * nStar D) :=
    le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (one_le_maxOpNorm h))
  exact (integrable_norm_holMinorsPi_mul_pow h_rank ho hu_dom hu_gap).mono'
    (isHolOfWeight_holMinorsPi ho hu_dom).continuous.aestronglyMeasurable (.of_forall hbound)

/-- Let `D` be admissible data, `b = D.b`, `t = D.t`, `n_* = nStar D`, and let the rank satisfy
`1 ≤ n ≤ t`. Let the order `o` put the signs `+1` first, let the weights `u`, `u'` be dominant
within each sign block with gap `300 n_*` between the blocks, the entries of `u` at most `5 b` in
modulus. Write `m_u = holMinorsPi s u` and `|h| = maxOpNorm h`. Let `W`, `K`, `K'` be continuous,
`|W| ≤ M`, and `K`, `K'` both within `δ |h| ^ (6 n_*)` of a function `K₀`. If `∫ W K' m_u' = 0` and
`K m_u' W` is integrable, then `|∫ K m_u' W| ≤ 2 δ M b ^ n_* ∫ |m_u|²`. -/
lemma norm_integral_mul_holMinorsPi_mul_le (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ)) (hu'_dom : ∀ τ : D.Φ, IsKDominant s o (u' τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D))
    (hu'_gap : ∀ τ : D.Φ, HasHolGap s (u' τ) (300 * nStar D))
    (hu_le : ∀ (τ : D.Φ) (i : n), |(u τ i : ℝ)| ≤ 5 * D.b)
    {W K K' K₀ : GInf D.E s → ℂ} {M δ : ℝ} (hW : Continuous W) (hK : Continuous K)
    (hK' : Continuous K') (hW_le : ∀ h : GInf D.E s, ‖W h‖ ≤ M)
    (hK_close : ∀ h : GInf D.E s, ‖K h - K₀ h‖ ≤ δ * maxOpNorm h ^ (6 * nStar D))
    (hK'_close : ∀ h : GInf D.E s, ‖K' h - K₀ h‖ ≤ δ * maxOpNorm h ^ (6 * nStar D))
    (h_orth : ∫ h : GInf D.E s, W h * K' h * holMinorsPi s u' h = 0)
    (h_int : Integrable fun h : GInf D.E s ↦ (K * holMinorsPi s u') h * W h) :
    ‖∫ h : GInf D.E s, (K * holMinorsPi s u') h * W h‖ ≤
      2 * δ * M * D.b ^ nStar D * ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 := by
  -- Orthogonality lets us replace `K` by the small function `K - K'`.
  have hM : 0 ≤ M := (norm_nonneg _).trans (hW_le 1)
  have hdiff_le (h : GInf D.E s) :
      ‖(W * (K - K')) h‖ ≤ 2 * δ * M * maxOpNorm h ^ (6 * nStar D) :=
    calc ‖W h * (K h - K' h)‖ ≤ M * (‖K h - K₀ h‖ + ‖K' h - K₀ h‖) := by
          grw [norm_mul, hW_le, norm_sub_le_norm_sub_add_norm_sub _ (K₀ h), norm_sub_rev (K₀ h)]
      _ ≤ M * (δ * maxOpNorm h ^ (6 * nStar D) + δ * maxOpNorm h ^ (6 * nStar D)) := by
          grw [hK_close, hK'_close]
      _ = _ := by ring
  obtain ⟨hdiff_int, hdiff⟩ : Integrable (W * (K - K') * holMinorsPi s u') ∧
      ‖∫ h, (W * (K - K')) h * holMinorsPi s u' h‖ ≤
        2 * δ * M * D.b ^ nStar D * ∫ h, ‖holMinorsPi s u h‖ ^ 2 :=
    integrable_mul_holMinorsPi h_rank ho hu_dom hu'_dom hu_gap hu'_gap hu_le
      (hW.mul (hK.sub hK')) hdiff_le
  have hsub : ∫ h, (K * holMinorsPi s u') h * W h - (W * (K - K') * holMinorsPi s u') h = 0 :=
    (integral_congr_ae (.of_forall fun h ↦ by simp; ring)).trans h_orth
  rw [integral_sub h_int hdiff_int, sub_eq_zero] at hsub
  rwa [hsub]

omit [Nonempty n] in
/-- Let the order `o` put the signs `+1` first, let `u` be dominant within each sign block, write
`m_u = holMinorsPi s u`, and let `f` be holomorphic of weight `u`: it extends analytically to
products with `o`-triangular matrices, on which it transforms by the character `u`. Let `W θ` be a
family of functions on the group whose mean over the circle is the conjugate of `c m_u`, with
`c ≠ 0`. If `f(h) W θ h` is jointly integrable and `|∫ f W θ| ≤ B` whenever this integral converges,
then `(∫ |m_u|²) |f 1| |c| ≤ B`. -/
lemma integral_mul_norm_apply_one_mul_le (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ)) {f : GInf D.E s → ℂ} (hf : IsHolOfWeight s o u f)
    {W : UnitAddCircle → GInf D.E s → ℂ} {c : ℂ} {B : ℝ} (hc : c ≠ 0)
    (hW_mean : ∀ h : GInf D.E s,
      ∫ θ : UnitAddCircle, W θ h = starRingEnd ℂ (holMinorsPi s u h * c))
    (h_int : Integrable (Function.uncurry fun (θ : UnitAddCircle) (h : GInf D.E s) ↦ f h * W θ h)
      (volume.prod volume))
    (h_le : ∀ θ : UnitAddCircle, Integrable (fun h : GInf D.E s ↦ f h * W θ h) →
      ‖∫ h : GInf D.E s, f h * W θ h‖ ≤ B) :
    (∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2) * ‖f 1‖ * ‖c‖ ≤ B := by
  -- Exchange the integrals over `θ` and `h`, then use the reproducing formula for `f`.
  set I : ℝ := ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 with hI
  have hI_nonneg : 0 ≤ I := integral_nonneg fun h ↦ sq_nonneg _
  let A (h : GInf D.E s) : ℂ := f h * starRingEnd ℂ (holMinorsPi s u h)
  have hA (h : GInf D.E s) : ∫ θ, f h * W θ h = A h * starRingEnd ℂ c := by
    rw [integral_const_mul, hW_mean, map_mul, ← mul_assoc]
  have hA_int : Integrable A := by
    simpa [hA, integrable_mul_const_iff, hc] using h_int.integral_prod_right
  have hrepr : ∫ h, A h = I * f 1 := by
    simpa [A, ← hI] using hf.integral_mul_conj_holMinorsPi ho hu_dom hA_int
  calc _ = ‖∫ h, ∫ θ, f h * W θ h‖ := by
        simp [hA, integral_mul_const, hrepr, abs_of_nonneg hI_nonneg]
    _ = ‖∫ θ, ∫ h, f h * W θ h‖ := by rw [integral_integral_swap h_int]
    _ ≤ B * (volume : Measure UnitAddCircle).real .univ :=
        norm_integral_le_of_norm_le_const (h_int.prod_right_ae.mono h_le)
    _ = B := by simp [Measure.real]

/-- Let `D` be admissible data (`Data`), of which only these are used: the CM field `E = D.E`, the
set `D.Φ` of its `f` infinite places `τ`, the number `t = D.t`, the weight `b = D.b`, which is very
large against `t`, and `n_* = nStar D = 2 f t³`. For signs `s` on `n` indices, `1 ≤ n ≤ t`, the
group `GInf D.E s` is the product of the groups `U(diag s)` over `τ`, with its Haar measure `dh`,
and `G D.E s` is its product with the finite adelic unitary group. Let the order `o` put the signs
`+1` first. Let the weights `u τ`, `u' τ` be dominant within each sign block, with entries at the
sign `-1` larger by at least `300 n_*` than those at the sign `+1` (`HasHolGap`), and let `u` have
entries of modulus at most `5 b`. Write `m_u' = holMinorsPi s u'` for the product over `τ` of the
quotients of principal minors `holMinors s (u' τ)`, and `|h| = maxOpNorm h` for the largest operator
norm of `h` at a place.

Let `F` on `G D.E s` be continuous and holomorphic of weight `u` in the archimedean variable, with a
peak `z` (`F` is bounded and `|F z|` exceeds half of `sup |F|`), and let `K₀` be bounded. Suppose
that at every peak `x` we have `∫ conj F(x h) K(h) m_u'(h) dh = 0` for some `K` that is holomorphic
of weight `u - u'` and has `|K h - K₀ h| ≤ δ |h| ^ (6 n_*)`. Then `|K₀ 1| ≤ (4 b ^ n_* + 1) δ`. -/
theorem norm_apply_one_le_of_forall_isPeak (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ)) (hu'_dom : ∀ τ : D.Φ, IsKDominant s o (u' τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D))
    (hu'_gap : ∀ τ : D.Φ, HasHolGap s (u' τ) (300 * nStar D))
    (hu_le : ∀ (τ : D.Φ) (i : n), |(u τ i : ℝ)| ≤ 5 * D.b)
    {F : New.G D.E s → ℂ} {z : New.G D.E s} {K₀ : GInf D.E s → ℂ} {C δ : ℝ}
    (hF : Continuous F) (hF_hol : IsAdelicHol o u F) (hz : IsPeak F z)
    (hK₀_le : ∀ h : GInf D.E s, ‖K₀ h‖ ≤ C)
    (h_orth : ∀ x : New.G D.E s, IsPeak F x → ∃ K : GInf D.E s → ℂ,
      IsHolOfWeight s o (u - u') K ∧
      (∀ h : GInf D.E s, ‖K h - K₀ h‖ ≤ δ * maxOpNorm h ^ (6 * nStar D)) ∧
      ∫ h : GInf D.E s, star (F (x * (h, 1))) * K h * holMinorsPi s u' h = 0) :
    ‖K₀ 1‖ ≤ (4 * D.b ^ nStar D + 1) * δ := by
  -- Rotate `z` by a circle `rot θ`: all `z * rot θ` are peaks, so `h_orth` gives functions `K θ`.
  -- Replacing `K θ` by `K 0` has a small cost, the mean over `θ` turns the translate of `F` into
  -- `F z * m_u`, and the reproducing formula evaluates the integral.
  set I : ℝ := ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2
  have hI_pos : 0 < I := integral_norm_holMinorsPi_sq_pos h_rank ho hu_dom hu_gap
  let rot (θ : UnitAddCircle) : GInf D.E s := fun _ ↦ diagTorus s fun i ↦ θ.toCircle ^ o i
  have hpeak (θ : UnitAddCircle) : IsPeak F (z * (rot θ, 1)) := by
    have hF_rot : F (z * (rot θ, 1)) = (∏ τ, ∏ i, (↑(θ.toCircle ^ o i) : ℂ) ^ u τ i) * F z := by
      simpa [Prod.mk_one_one] using (hF_hol z).apply_mul_diagTorus 1 fun i ↦ θ.toCircle ^ o i
    exact hz.of_norm_le (by simp [hF_rot, Circle.norm_coe])
  have hK (θ : UnitAddCircle) : ∃ K : GInf D.E s → ℂ, IsHolOfWeight s o (u - u') K ∧
      (∀ h, ‖K h - K₀ h‖ ≤ δ * maxOpNorm h ^ (6 * nStar D)) ∧
      ∫ h, star (F (z * (rot θ, 1) * (h, 1))) * K h * holMinorsPi s u' h = 0 :=
    h_orth (z * (rot θ, 1)) (hpeak θ)
  choose K hK_hol hK_close hK_orth using hK
  -- `W θ` is the conjugate of the quotient of the rotated translate of `F` by the character.
  let W (θ : UnitAddCircle) (h : GInf D.E s) : ℂ :=
    starRingEnd ℂ (F (z * (rot θ * h, 1)) * ∏ τ, ∏ i, ↑((θ.toCircle ^ o i) ^ u τ i)⁻¹)
  have hW_orth (θ : UnitAddCircle) : ∫ h, W θ h * K θ h * holMinorsPi s u' h = 0 :=
    calc _ = ∫ h, star (F (z * (rot θ, 1) * (h, 1))) * K θ h * holMinorsPi s u' h *
          starRingEnd ℂ (∏ τ, ∏ i, ↑((θ.toCircle ^ o i) ^ u τ i)⁻¹) := by
          congr with h
          simp [W, mul_assoc z]
          ring
      _ = 0 := by rw [integral_mul_const, hK_orth, zero_mul]
  -- As `h ↦ F (z h)` is holomorphic of weight `u`, this quotient has circle mean `m_u * F z`.
  have hW_mean (h : GInf D.E s) : ∫ θ, W θ h = starRingEnd ℂ (holMinorsPi s u h * F z) := by
    rw [← mul_one z, ← Prod.mk_one_one, ← (hF_hol z).circle_mean_holMinorsPi ho hu_dom h,
      integral_conj]
  have hW_le (θ : UnitAddCircle) (h : GInf D.E s) : ‖W θ h‖ ≤ 2 * ‖F z‖ := by
    simpa [W, Circle.norm_coe] using hz.norm_le (z * (rot θ * h, 1))
  have hK_le (h : GInf D.E s) : ‖K 0 h‖ ≤ (C + δ) * maxOpNorm h ^ (6 * nStar D) := by
    grw [norm_le_insert' _ (K₀ h), hK_close, hK₀_le, add_mul,
      ← le_mul_of_one_le_right ((norm_nonneg _).trans (hK₀_le h))
        (one_le_pow₀ (one_le_maxOpNorm h))]
  have hK_int : Integrable (K 0 * holMinorsPi s u') :=
    (integrable_mul_holMinorsPi h_rank ho hu_dom hu'_dom hu_gap hu'_gap hu_le
      (hK_hol 0).continuous hK_le).1
  have hprod_int : Integrable
      (Function.uncurry fun θ h ↦ (K 0 * holMinorsPi s u') h * W θ h) (volume.prod volume) :=
    (hK_int.comp_snd volume).mul_bdd (g := W.uncurry) (by fun_prop)
      (.of_forall fun x ↦ hW_le x.1 x.2)
  have hslice (θ : UnitAddCircle) (hθ : Integrable fun h ↦ (K 0 * holMinorsPi s u') h * W θ h) :
      ‖∫ h, (K 0 * holMinorsPi s u') h * W θ h‖ ≤ 2 * δ * (2 * ‖F z‖) * D.b ^ nStar D * I :=
    norm_integral_mul_holMinorsPi_mul_le h_rank ho hu_dom hu'_dom hu_gap hu'_gap hu_le
      (by fun_prop) (hK_hol 0).continuous (hK_hol θ).continuous (hW_le θ) (hK_close 0) (hK_close θ)
      (hW_orth θ) hθ
  -- `K 0 * m_u'` is holomorphic of weight `u`, and its value at `1` is `K 0 1`.
  have hhol : IsHolOfWeight s o u (K 0 * holMinorsPi s u') := by
    simpa using (hK_hol 0).mul ho.1 (isHolOfWeight_holMinorsPi ho hu'_dom)
  have h_le : I * ‖K 0 1‖ * ‖F z‖ ≤ 2 * δ * (2 * ‖F z‖) * D.b ^ nStar D * I := by
    simpa using
      integral_mul_norm_apply_one_mul_le ho hu_dom hhol hz.ne_zero hW_mean hprod_int hslice
  have hK_one : ‖K 0 1‖ ≤ 4 * δ * D.b ^ nStar D :=
    le_of_mul_le_mul_right (by linarith) (mul_pos hI_pos (norm_pos_iff.2 hz.ne_zero))
  have hK_diff : ‖K 0 1 - K₀ 1‖ ≤ δ := by simpa [maxOpNorm] using hK_close 0 1
  linarith [norm_le_insert (K 0 1) (K₀ 1)]

end New.Data

end Isolation
end
end

/-!
# Products span

For admissible data D (`New.Data`) and 1 ≤ j ≤ m, let 𝖥_i = `New.Data.choiceFn j i` be the functions
on the unitary group of W_j = `New.Data.spaceW j`, one for each choice i, and let θ° be the theta
kernel of (W_j, V°). A good form (`New.Data.goodForms`) is a form of principal level at the chosen
places in the image of the idempotent `New.Data.e₀`. We show that a good form y on W_j with
∫ y(g) 𝖥_i(g) θ°(g, ·) dg = 0 for all i is zero.

We write λ₁(g) for the first minimum `New.Space.firstMinimum` of the lattice at g, cut off at 1, |h|
for the largest operator norm `New.Rows.maxOpNorm` of a real point h, and m_u for the basic
holomorphic function `New.holMinorsPi` of a weight u, a quotient of products of minors. A peak
(`New.Rows.IsPeak`) of a bounded function is a point where its modulus exceeds half of the supremum.
Suppose y ≠ 0. The peaks of y are not deep in a cusp, and the proof has four steps.

1. The integral 𝖥^g of the carrier times a kernel on (S, W̃) times m_u₁ over the real group of S is
   a combination of the 𝖥_i (`New.Data.exists_sum_choiceFn_eq_integral`).
2. For every combination 𝖥 of the 𝖥_i, the integral of y 𝖥 m_u° over the real group at any point is
   zero (`New.Data.integral_mul_sum_choiceFn_eq_zero`).
3. At every peak g, 𝖥^g(g h) is close to 𝖥⁰(h), for one bounded function 𝖥⁰ with 𝖥⁰(1) ≠ 0
   (`New.Data.exists_choiceFn_approx`).
4. The mean over a circle of peaks makes 𝖥⁰(1) too small
   (`New.Data.norm_apply_one_le_of_forall_isPeak`).

Steps 1 and 3 do not involve y and come first in this file.

## Main definitions and results

* `New.Data.exists_datum_norm_modKernel_sub_polyMatrixCoeff_le` (sparse sums): for V, V' of ranks at
  most t and Q homogeneous of degree at most b^(3/2), if λ₁(g) λ₁(g') ≥ b^(−13), then for some datum
  Ψ the theta kernel `New.modKernel` at (g h, g' h') is close to the coefficient c_Q(h, h').
* `New.Data.exists_isPeak_carrierForm`: the carrier `New.Rows.carrierForm` has a peak g₁, and
  λ₁(g₁) ≥ (5 b √b)^(−1/2).
* `New.Data.exists_choiceFn_approx`: there is a bounded F₀ with F₀(1) ≠ 0 such that, when λ₁(g) ≥ (5
  b²⁴)^(−1/2), some combination F of the 𝖥_i satisfies |F(g h) − F₀(h)| ≤ 2 b^(−19 n_*) |F₀(1)|
  |h|^(6 n_*).
* `New.Data.thetaKernelPairing`: the pairing of a form on V°, given by its values at the classes,
  with the kernel θ°.
* `New.Data.eq_zero_of_integral_choiceFn_thetaKernelPairing`: products span.

Notions from other files:
* `New.Data.b`: The large scale b of the data, the weight at the b-places, as a real number.
* `New.Data.nStar`: The number n_* = 2ft³, where f is the number of infinite places of E and t = 5r.
* `New.Data.SecondFactorIndex`: The index set of V°: the r indices of W_j and t − 9m − 1 − r further
  ones.
* `New.Data.CarrierIndex`: The index set of the space S of signature (2m, m).
* `New.Data.conjHolomorphicWeight`, `New.Data.kernelWeight`: The weights u of the conjugate of y and
  u° of θ° on W_j. The 𝖥_i have the weight u − u°.

## Relation to the literature

For a finite family of choices with small integral data, a good form on U(W_j) orthogonal to all
products of the twist-free theta forms with theta kernels of the complementary block is zero. This
makes the map Θ° on good forms injective. It is a basis problem, the spanning of a space of forms by
theta series (Eichler, The basis problem for modular forms and the traces of the Hecke operators,
1973; Waldspurger, Engendrement par des séries thêta de certains espaces de formes modulaires,
1978/79; Böcherer, Siegel modular forms and theta series, 1989). It is known that stable-range theta
kernels reach all forms, that maxima of forms avoid the cusps, and that products span for GL(2).
Related work: J.-S. Li, Non-vanishing theorems for the cohomology of certain arithmetic quotients,
1992; Poor–Yuen, Linear dependence among Siegel modular forms, 2000; Khuri-Makdisi, Moduli
interpretation of Eisenstein series, 2012.
-/

@[expose] public section

namespace New.Data

/-!
## Approximation by combinations of the 𝖥_i away from the cusps

Here S is the space of signature (2m, m), W̃ = W_j ⊕ (E^j)⁻ ⊕ E^(3m−j) is `New.Data.paddedSpace`,
W♭ = E^(6m+1), and P = `New.Data.paddedMinorProd j` is the fixed polynomial on (S, W̃).
-/

section NaturalFormNear

open NumberField Matrix MvPolynomial Finset Norms.L2Operator Rows Fock WeilData Fintype Prod Sum

variable {P : Parameters} {D : Data P} (j : D.LiftIndex)

/-- Let `1 ≤ j ≤ m`, let `W_j` be the diagonal hermitian space of rank `r` with signs `D.signsW j`,
and pad it with `j` signs `-1` and `3 m - j` signs `1` to the space `W̃` with signs `padSigns j`.
The polynomial `paddedMinorProd j` is a product of minors whose rows are indices of `W̃`: one minor
has the `m` rows `negIndex j a`, and for each column height `h` one has the `2 m` rows
`posRowIndex j h a`, which start at the basis vector of number `h` of `W_j`. Each of these families
of rows is injective; the rows `negIndex j a` have sign `-1` and the rows `posRowIndex j h a` have
sign `1`. -/
theorem negIndex_posRowIndex_injective_and_padSigns :
    ((negIndex j).Injective ∧ ∀ h : ℕ, (posRowIndex j h).Injective) ∧
    (∀ a : Fin D.m, padSigns j (negIndex j a) = -1) ∧
    ∀ (h : ℕ) (a : Fin (2 * D.m)), padSigns j (posRowIndex j h a) = 1 := by
  -- Each value of these maps is either the index `D.rowIndexOfNumber i` of number `i` in `W_j` or
  -- a padding index, so the claims become inequalities between natural numbers.
  unfold Function.Injective negIndex posRowIndex
  refine ⟨⟨fun a b ↦ ?_, fun h a b ↦ ?_⟩, fun a ↦ ?_, fun h a ↦ ?_⟩
  all_goals split_ifs
  all_goals simp [signsW, rowIndexOfNumber]
  all_goals grind

/-- Sparse sums. The data `D` give the CM field `E` with its `f` infinite places `D.Φ`, a large real
scale `b = D.b`, the numbers `t = D.t` and `n_* = nStar D = 2 f t ^ 3`, and the modulus
`untwistedModulus 2 = ϖ²`. Let `V`, `V'` be hermitian spaces of ranks at most `t`, let the
characters `χ`, `χ'` of `U(1)` have weights `γ`, `e` at the infinite places and residue characters
`ψ`, `ψ'`, and let the polynomial `Q` be homogeneous of degree `d ≤ b ^ (3 / 2)`. Write `λ₁(g)` for
the first minimum, cut off at `1`, of the lattice of `V` moved by the adelic point `g`, `|h|` for
the operator norm `maxOpNorm h`, and `c_Q = polyMatrixCoeff s s' γ e Q` for the matrix coefficient
of the real Weil representation at the Fock vector of `Q`. If `λ₁(g) λ₁(g') ≥ b ^ (-13)`, then for
some function `Ψ` on matrices modulo `ϖ²` the theta kernel `modKernel` with data `Ψ`, `Q` at
`(g h, g' h')` differs from `c_Q(h, h')` by at most
`b ^ (-20 n_*) (|h| |h'|) ^ (6 n_*) |c_Q(1, 1)|`, for all real points `h`, `h'`. -/
theorem exists_datum_norm_modKernel_sub_polyMatrixCoeff_le {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] [Nonempty n] [Nonempty n'] {s : n → ℤˣ} {s' : n' → ℤˣ}
    (V : Space D.E n s) (V' : Space D.E n' s') (h_rank : card n ≤ D.t) (h_rank' : card n' ≤ D.t)
    {χ χ' : AutChar D.E} {γ e : D.Φ → ℤ} {ψ ψ' : (w : FinPlace D.E) → MulChar (ResField w) ℂ}
    (hχ : χ.HasWeight γ ψ) (hχ' : χ'.HasWeight e ψ') {Q : MvPolynomial (D.Φ × n' × n) ℂ} {d : ℕ}
    (hQ : ∀ (r : ℝ) (y : D.Φ × n' × n → ℂ), Q.eval (r • y) = r ^ d * Q.eval y)
    (hd : d ≤ D.b * √D.b) {g : New.G D.E s} {g' : New.G D.E s'}
    (h_min : (D.b ^ 13)⁻¹ ≤ (V.move g).firstMinimum * (V'.move g').firstMinimum) :
    ∃ Ψ : Matrix n' n (D.untwistedModulus 2).ResidueRing → ℂ, ∀ (h : GInf D.E s) (h' : GInf D.E s'),
      ‖modKernel V V' χ χ' (D.untwistedModulus 2) Ψ Q (g * (h, 1)) (g' * (h', 1)) -
          polyMatrixCoeff s s' γ e Q h h'‖ ≤
        (D.b ^ (20 * nStar D))⁻¹ * (maxOpNorm h * maxOpNorm h') ^ (6 * nStar D) *
          ‖polyMatrixCoeff s s' γ e Q 1 1‖ := by
  -- The scale `c = q₁ / piM ^ 2` clears the denominators of `α` times the ideal of the modulus.
  let c : D.E := D.q₁ / algebraMap (𝓞 D.E) D.E (D.piM ^ 2)
  have piM_sq_ne_zero : algebraMap (𝓞 D.E) D.E (D.piM ^ 2) ≠ 0 := by simp
  have h_int : ∀ z : Ô D.E, (D.untwistedModulus 2).reduction z = 0 →
      algebraMap D.E (𝔸f D.E) c * (α.val * z.val) ∈ Ô D.E := by
    intro z hz
    rw [Modulus.reduction_eq_zero_iff, ideal_untwistedModulus_eq_span, Ideal.map_span,
      Set.image_singleton, Ideal.mem_span_singleton] at hz
    obtain ⟨y, rfl⟩ := hz
    have h_cancel : algebraMap D.E (𝔸f D.E) c *
        (algebraMap (𝓞 D.E) (Ô D.E) (D.piM ^ 2) : Ô D.E) = D.q₁ := by
      change _ * algebraMap D.E (𝔸f D.E) (algebraMap (𝓞 D.E) D.E (D.piM ^ 2)) = _
      rw [← map_mul, div_mul_cancel₀ _ piM_sq_ne_zero, map_natCast]
    rw [MulMemClass.coe_mul, mul_left_comm α.val, ← mul_assoc, h_cancel, ← mul_assoc]
    exact mul_mem P.q₁_mul_alpha_mem y.prop
  -- The points of the sparse lattice are `b ^ 6`-separated: the first minimum of the lattice of
  -- homomorphisms is at least `λ₁(g) λ₁(g')` over a constant, and `|Φ w c| = q₁ / M` is small.
  have h_sep (w : D.Φ) : D.b ^ 6 * ‖Φ w c‖ ≤
      √(2 * .pi * (Φ w WeilData.j).im) * ((V.move g).hom (V'.move g')).firstMinimum := by
    have h_norm : ‖Φ w c‖ = (D.q₁ : ℝ) / D.M := by
      simpa [c, sq, -Nat.cast_mul] using
        congrArg (fun x : 𝓞 D.E ↦ (D.q₁ : ℝ) / ‖Φ w (x : D.E)‖) D.piM_mul_star
    have h_cond : D.cyclotomicConductor ≠ 0 := NeZero.ne _
    have ht_pos : 0 < D.t := D.t_odd.pos
    have h_hom : (D.b ^ 13)⁻¹ / (6 * D.cyclotomicConductor * (D.f * D.t : ℝ) ^ 2 * D.t * D.t) ≤
        ((V.move g).hom (V'.move g')).firstMinimum := by
      grw [← firstMinimum_mul_le_hom _ P.conductor_mem_differentIdeal, Space.shortBasisConst,
        ← h_min, h_rank, h_rank', h_rank]
      simp [Data.f]
    grw [← h_hom, h_norm, P.phi_weilData_j]
    simpa using D.le_of_hasLogBound
  have h_dim : card (D.Φ × n' × n) < 2 * nStar D := by
    grw [card_prod, card_prod, h_rank, h_rank']
    exact D.nat_lt_of_hasLogBound
  -- The bound for the other terms of the lattice sum, to be raised to the power `2 n_*`.
  have h_ratio : 100 * (d + 2 * (2 * nStar D : ℕ)) / (D.b ^ 6) ^ 2 ≤ (D.b ^ 10)⁻¹ := by
    grw [hd]
    exact D.le_of_hasLogBound
  obtain ⟨Ψ, hΨ⟩ := exists_norm_modKernel_sub_fockInner_le (g := g) V' hχ hχ'
    (div_ne_zero (NeZero.ne (D.q₁ : D.E)) piM_sq_ne_zero) h_int g' (D.b ^ 6) (2 * nStar D)
    (by positivity) h_sep h_dim Q rfl d hQ
  refine ⟨Ψ, fun h h' ↦ (hΨ h h').trans ?_⟩
  grw [h_ratio]
  simp only [polyMatrixCoeff, Prod.mk_one_one, map_one, one_apply_eq_self]
  exact le_of_eq (by ring)

/-- Give a variable of `paddedMinorProd j` the sign `padSigns j` of its row times the sign `1 ⊕ᵥ -1`
of its column in `D.CarrierIndex`. Each of its variables has row and column of the same sign, so
`paddedMinorProd j` is a polynomial in the variables of sign `1`. -/
lemma paddedMinorProd_mem_supported :
    paddedMinorProd j ∈ supported ℂ
      {p | realSigns D.E (homSigns (n := D.CarrierIndex) (1 ⊕ᵥ -1) (padSigns j)) p = 1} := by
  simp (maxDischargeDepth := 9) [paddedMinorProd, variableMinor, det_apply', prod_mem, mul_mem,
    pow_mem,
    sum_mem, negIndex_posRowIndex_injective_and_padSigns j, pairSign]

/-- Extending a point of the group of `W_j` by the identity on the padding does not increase its
norm. -/
lemma maxOpNorm_sum_one_le (y : GInf D.E (D.signsW j)) :
    maxOpNorm (G.sum ((y, 1), (1 : New.G D.E (-1 ⊕ᵥ 1 : PadIndex j → ℤˣ)))).1 ≤ maxOpNorm y := by
  simp [G.sum, U.sum, pi_norm_le_iff_of_nonempty, one_le_maxOpNorm,
    norm_le_pi_norm (fun w ↦ (y w).val.val)]

/-- Let `S` be the space of signature `(2 m, m)`, with index set `D.CarrierIndex` and signs
`1 ⊕ᵥ -1`, and let `W̃` be the space `W_j` (`1 ≤ j ≤ m`) padded to the signs `padSigns j`. Let
`P = paddedMinorProd j` be the fixed product of minors in the variables of `(S, W̃)`. For characters
of any weights `γ`, `e`, the matrix coefficient `polyMatrixCoeff` of the real Weil representation at
the Fock vector of `P` does not vanish at the identity, and it is bounded on the product of the real
unitary groups of `S` and `W̃`. -/
lemma polyMatrixCoeff_paddedMinorProd_ne_zero_and_bounded (γ e : D.Φ → ℤ) :
    polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ e (paddedMinorProd j) 1 1 ≠ 0 ∧
    ∃ B : ℝ, ∀ (h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) (h' : GInf D.E (padSigns j)),
      ‖polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ e (paddedMinorProd j) h h'‖ ≤ B := by
  -- The Fock representation is unitary: `l` carries `fockInner` to an inner product and the action
  -- to isometries.
  let ε := realSigns D.E (homSigns (n := D.CarrierIndex) (1 ⊕ᵥ -1) (padSigns j))
  let v := polyVector ε (paddedMinorProd j)
  obtain ⟨_, _, _, l, h_inner, h_unitary⟩ :=
    (isUnitaryRep_detTwist (ε := ε) (f := .id _) (γ := 0) (one_mul _).ge).exists_innerProductSpace
  refine ⟨?_, ‖l v‖ * ‖l v‖, fun h h' ↦ ?_⟩
  · -- Each minor in `paddedMinorProd` has distinct rows and distinct columns.
    simp [polyMatrixCoeff, ε, ← h_inner, paddedMinorProd, prod_eq_zero_iff,
      negIndex_posRowIndex_injective_and_padSigns j,
      inl_injective, inr_injective, mk_one_one]
  · -- Up to factors of modulus one this is an inner product; apply Cauchy–Schwarz.
    have h_phase : ‖polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ e (paddedMinorProd j) h h'‖ =
        ‖inner ℂ (l v) (l (realWeil (pairHomInf (h, h')) v))‖ := by
      simp [polyMatrixCoeff, realPairWeil, v, ε, ← h_inner]
    have h_iso : ‖l (realWeil (pairHomInf (h, h')) v)‖ = ‖l v‖ := by
      simpa using h_unitary (pairHomInf (h, h')) v
    grw [h_phase, norm_inner_le_norm, h_iso]

/-- The product of minors `paddedMinorProd j` is homogeneous of degree at most `b ^ (3 / 2)`, where
`b = D.b` is the large scale of the data. Its variables are indexed by an infinite place, a basis
vector of `W_j` (`D.RowIndex`) or of its padding (`PadIndex j`), and a basis vector of the space of
signature `(2 m, m)` (`D.CarrierIndex`). -/
lemma exists_eval_smul_paddedMinorProd : ∃ d : ℕ, d ≤ D.b * √D.b ∧
    ∀ (r : ℝ) (y : D.Φ × (D.RowIndex ⊕ PadIndex j) × D.CarrierIndex → ℂ),
      (paddedMinorProd j).eval (r • y) = r ^ d * (paddedMinorProd j).eval y := by
  let deg (w : D.Φ) : ℕ := ∑ h : Fin (D.posRank j),
    2 * D.m * (untwistedDescentPair j).colsPlus w h +
    D.m * (card (DetIndex j w) + card (FirstFactorIndex j) + D.m)
  have h_deg (w : D.Φ) : (deg w : ℝ) ≤ 2 * D.m * (5 * D.b) := by
    have h_cols : ∑ h : Fin (D.posRank j), (untwistedDescentPair j).colsPlus w h ≤
        card (DetIndex j w) := by simp
    grw [← two_mul_card_detIndex_add_le j w]
    norm_cast
    simp only [deg, ← mul_sum]
    grw [h_cols]
    lia
  refine ⟨∑ w, deg w, ?_, fun r y ↦ ?_⟩
  · grw [Nat.cast_sum, sum_le_card_nsmul _ _ _ fun w _ ↦ h_deg w]
    simpa using D.le_of_hasLogBound
  · have h_minor {p : Type} [Fintype p] [DecidableEq p] (τ : D.Φ)
        (row : p → D.RowIndex ⊕ PadIndex j) (col : p → D.CarrierIndex) :
        (variableMinor τ row col).eval (r • y) =
          r ^ card p * (variableMinor τ row col).eval y := by
      simp [variableMinor, det_apply', mul_sum, prod_mul_distrib, mul_left_comm]
    simp only [paddedMinorProd, map_prod, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    refine prod_congr rfl fun w _ ↦ ?_
    simp only [deg, map_mul, map_pow, map_prod, h_minor, Fintype.card_fin, mul_pow,
      prod_mul_distrib, pow_add, ← pow_mul, prod_pow_eq_pow_sum]
    ring

variable (D) in
/-- The weight `u₁ = (-Δ'; 6 m + 1)` of the kernels on `(S, W♭)`, the same at every place. Here
`Δ' = reducedHalfGap` is `Δ / 2 - (t + 1) / 2`, where the gap `Δ = 2 r ^ 8` is the difference of the
weights of consecutive lifts, and `6 m + 1` is the rank of `W♭`. Here and below `(a; b)` has the
entry `a` at the signs `+1` and `b` at the signs `-1` of `S`. -/
def flatKernelWeight (_ : D.Φ) : D.CarrierIndex → ℤ :=
  (fun _ ↦ -D.reducedHalfGap) ⊕ᵥ fun _ ↦ 6 * D.m + 1

/-- The weight `(Δ'; μ₁⁺ + r + 2 m)` of the holomorphic factor in the coefficient of
`paddedMinorProd`. Here `Δ' = reducedHalfGap` is `Δ / 2 - (t + 1) / 2` for the gap `Δ`, and
`μ₁⁺ = #(DetIndex j w)` is the number of columns of the diagram `μ⁺` at the place `w`: the sum of
the column counts `colsPlus` of `untwistedDescentPair j`, plus `Δ'`. The weight is `u₂ + μ₁⁺`, where
`u₂ = (Δ' - μ₁⁺; r + 2 m)` is the weight for the standard character `υ ^ m`. The shift by `μ₁⁺` in
every entry arises because the character `carrierChar j` of the kernel has weight `m - μ₁⁺` instead
of `m`. -/
noncomputable def holomorphicWeight (w : D.Φ) : D.CarrierIndex → ℤ :=
  (fun _ ↦ D.reducedHalfGap) ⊕ᵥ fun _ ↦ card (DetIndex j w) + D.r + 2 * D.m

/-- The weight `u₃ = (0; μ₁⁺ + n'' + 2 m)` of the antiholomorphic factor in the coefficient of
`paddedMinorProd`. Here `μ₁⁺ = #(DetIndex j w)` is the number of columns of the diagram `μ⁺` at the
place `w` (the sum of the column counts `colsPlus` of `untwistedDescentPair j`, plus
`reducedHalfGap`), and `n'' = #(FirstFactorIndex j) = r + 9 m + 1` is the rank of `W̃ ⊕ W♭`. -/
noncomputable def antiholomorphicWeight (w : D.Φ) : D.CarrierIndex → ℤ :=
  (fun _ ↦ 0) ⊕ᵥ fun _ ↦ card (DetIndex j w) + card (FirstFactorIndex j) + 2 * D.m

/-- Let `S` be the space of signature `(2 m, m)`, with signs `1 ⊕ᵥ -1`, and let `W̃` be the padded
space of rank `r + 3 m` with signs `padSigns j`. Let `c_P` be the matrix coefficient
`polyMatrixCoeff` of the Fock vector of the product of minors `P = paddedMinorProd j` on `(S, W̃)`;
the weight `γ` of the first character is arbitrary, and that of the second is `m - μ₁⁺`, where
`μ₁⁺ = #(DetIndex j w)` is the number of columns of the partition `μ⁺` of the `j`-th lift at the
place `w`. Then for every real point `h` of the group of `S`,
`c_P(h, 1) = c_P(1, 1) m₂(h) conj(m₃(h))`. Here `m₂`, `m₃` are the quotients of minors `holMinorsPi`
of the weights `holomorphicWeight j = (Δ'; μ₁⁺ + r + 2 m)` and
`antiholomorphicWeight j = (0; μ₁⁺ + r + 11 m + 1)`, with `Δ' = D.reducedHalfGap` and with the
entries at the signs `+1`, `-1` before and after the semicolon. -/
lemma polyMatrixCoeff_paddedMinorProd (γ : D.Φ → ℤ) (h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) :
    polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ (fun w : D.Φ ↦ D.m - card (DetIndex j w))
      (paddedMinorProd j)
      h 1 =
    polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ (fun w : D.Φ ↦ D.m - card (DetIndex j w))
      (paddedMinorProd j)
      1 1 * holMinorsPi (1 ⊕ᵥ -1) (holomorphicWeight j) h *
        starRingEnd ℂ (holMinorsPi (1 ⊕ᵥ -1) (antiholomorphicWeight j) h) := by
  obtain ⟨-, h_neg_rows, h_pos_rows⟩ := negIndex_posRowIndex_injective_and_padSigns j
  have h_neg : Exchange.negCount (padSigns j) = D.m := by simp [negCount_signsW, j.property.2]
  let ν (w : D.Φ) : ℕ := ∑ k : Fin (D.posRank j), (untwistedDescentPair j).colsPlus w k
  let κ (w : D.Φ) : ℕ := card (DetIndex j w) + card (FirstFactorIndex j) + D.m
  -- Each minor in `paddedMinorProd` uses all columns of one sign, so a substitution multiplies it
  -- by a principal minor.
  have h_scale (u : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) :
      linSubst (complexLinearPart (pairHomInf (s' := padSigns j) (u⁻¹, 1))) (paddedMinorProd j) =
        (∏ w, principalMinor (u w).val.val (fun k ↦ (1 ⊕ᵥ -1 : _ → ℤˣ) k = 1) ^ ν w *
          principalMinor (u w).val.val (fun k ↦ (1 ⊕ᵥ -1 : _ → ℤˣ) k = -1) ^ κ w) • paddedMinorProd
            j := by
    simp [ν, κ, paddedMinorProd, prod_pow_eq_pow_sum, -card_sum,
      linSubst_variableMinor (h_pos_rows _) inl_injective,
      linSubst_variableMinor h_neg_rows inr_injective, smul_pow, prod_smul, smul_smul]
  -- Entry by entry, `holomorphicWeight j` is the weight `(-ν; rank W̃ - m) + μ₁⁺` and
  -- `antiholomorphicWeight j` is the weight `(0; κ + m)`.
  have holomorphicWeight_eq : holomorphicWeight j = fun (w : D.Φ) (i : D.CarrierIndex) ↦
      if (1 ⊕ᵥ -1 : _ → ℤˣ) i = 1 then (-ν w + (D.m - (D.m - card (DetIndex j w))) : ℤ)
      else (card (D.RowIndex ⊕ PadIndex j) - D.m : ℕ) + (D.m - (D.m - card (DetIndex j w))) := by
    ext w (_ | _)
    · simp [ν, holomorphicWeight]
    · simp [holomorphicWeight, ↓card_rowIndex]
      grind
  have antiholomorphicWeight_eq : antiholomorphicWeight j = fun (w : D.Φ) (i : D.CarrierIndex) ↦
      if (1 ⊕ᵥ -1 : _ → ℤˣ) i = 1 then (0 : ℤ) else κ w + D.m := by
    ext w (_ | _)
    · simp [antiholomorphicWeight]
    · simp [κ, antiholomorphicWeight]
      ring
  rw [holomorphicWeight_eq, antiholomorphicWeight_eq,
    polyMatrixCoeff_eq_holMinorsPi_mul_conj (1 ⊕ᵥ -1) (padSigns j) (paddedMinorProd j)
      (paddedMinorProd_mem_supported j) γ _ h_scale h, h_neg]

/-- Let `S` be the space of signature `(2 m, m)`, with index set `D.CarrierIndex` and signs
`1 ⊕ᵥ -1`. The weights `u₁ = flatKernelWeight D` and `u₃ = antiholomorphicWeight j` are integer
vectors on the indices of `S`, one for each infinite place. For every order `o` on the indices they
are `K`-dominant and have gap `300 n_*`, and `u₃` has entries of modulus at most `5 b`. Here
`b = D.b` is the large scale of the data and `n_* = nStar D = 2 f t ^ 3`, with `f` the number of
infinite places and `t = 5 r`. -/
lemma flatKernelWeight_antiholomorphicWeight_bounds (o : D.CarrierIndex → ℤ) :
    (∀ w : D.Φ, IsKDominant (1 ⊕ᵥ -1) o (flatKernelWeight D w)) ∧
    (∀ w : D.Φ, HasHolGap (1 ⊕ᵥ -1) (flatKernelWeight D w) (300 * nStar D)) ∧
    (∀ w : D.Φ, IsKDominant (1 ⊕ᵥ -1) o (antiholomorphicWeight j w)) ∧
    (∀ w : D.Φ, HasHolGap (1 ⊕ᵥ -1) (antiholomorphicWeight j w) (300 * nStar D)) ∧
    ∀ (w : D.Φ) (i : D.CarrierIndex), |(antiholomorphicWeight j w i : ℝ)| ≤ 5 * D.b := by
  have h_gap : 300 * nStar D + D.t ≤ D.halfGap := D.mul_nStar_add_t_le_halfGap
  refine ⟨by simp [flatKernelWeight, IsKDominant], ?_,
    by simp [antiholomorphicWeight, IsKDominant], ?_, fun w i ↦ ?_⟩
  · simp [flatKernelWeight, reducedHalfGap, HasHolGap]
    lia
  · simp [antiholomorphicWeight, -Nat.cast_sum, HasHolGap]
    grind [reducedHalfGap]
  · have h_le : D.m ≤ card (FirstFactorIndex j) := by grind [card_firstFactorIndex j]
    grw [← two_mul_card_detIndex_add_le j w]
    norm_cast
    cases i <;> simp [antiholomorphicWeight, -card_sum] <;> grind

/-- The character `carrierChar j` of the kernels on `(S, W̃)` and `(S, W̃ ⊕ W♭)` has weight
`m - μ₁⁺`, with `μ₁⁺ = #(DetIndex j w)` at the place `w`, and trivial tame part. -/
lemma carrierChar_hasWeight_sub_card :
    (carrierChar j).HasWeight (fun w : D.Φ ↦ D.m - card (DetIndex j w)) 1 := by
  have h_weight (w : D.Φ) :
      (D.m : ℤ) - card (DetIndex j w) = (D.m + firstFactorCharExp j : ℕ) - D.liftWeight j w := by
    grind [card_detIndex_add_firstFactorCharExp j w]
  simpa only [h_weight] using carrierChar_hasWeight j

variable (D) in
/-- Let `S = signedSpace D.E (1 ⊕ᵥ -1)` be the space of signature `(2 m, m)`, and let
`φ° = carrierForm D.E D.m` be the carrier, the theta lift of the constant function `1` from the
negative definite space of rank `m` to `S`. Assume that `φ°` is automorphic of every level and
rapidly decreasing (`rapidOfLevel`), and holomorphic in the real variable of weight `(0; 3 m)` for
an order `o` with the signs `+1` first. Then `φ°` has a peak `g₁`, and the first minimum of the
lattice of `S` at `g₁`, cut off at `1`, is at least `(5 b √b) ^ (-1 / 2)`, where `b = D.b` is the
large scale of the data. -/
lemma exists_isPeak_carrierForm {o : D.CarrierIndex → ℤ} (ho : IsPosFirstOrder (1 ⊕ᵥ -1) o)
    (h_level : ∀ N : 𝓞 D.E, carrierForm D.E D.m ∈ rapidOfLevel (signedSpace D.E (1 ⊕ᵥ -1)) N)
    (h_hol : IsAdelicHol o (fun _ : D.Φ ↦ 0 ⊕ᵥ 3 * D.m) (carrierForm D.E D.m)) :
    ∃ g₁ : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ), IsPeak (carrierForm D.E D.m) g₁ ∧
      (√(5 * D.b * √D.b))⁻¹ ≤ ((signedSpace D.E (1 ⊕ᵥ -1)).move g₁).firstMinimum := by
  obtain ⟨g₁, hg₁⟩ := exists_isPeak_of_mem_rapidOfLevel (h_level 1) carrierForm_ne_zero
  have h_gap (w : D.Φ) : HasHolGap (1 ⊕ᵥ -1) (0 ⊕ᵥ 3 * D.m : D.CarrierIndex → ℤ) 1 := by
    simp [HasHolGap]
    grind
  have h_wt (w : D.Φ) :
      ∀ i : D.CarrierIndex, |((0 ⊕ᵥ 3 * D.m : D.CarrierIndex → ℤ) i : ℝ)| ≤ 5 * D.b := by
    simpa [Real.exp_nonneg] using D.le_of_hasLogBound
  obtain ⟨⟨h_autom, -⟩, -⟩ := h_level 1
  refine ⟨g₁, hg₁, hg₁.le_firstMinimum _ _ ho h_gap h_wt D.le_of_hasLogBound D.le_of_hasLogBound
    P.star_sqrtNegDInE ?_ h_autom.rat_mul (apply_mul_of_mem_rapidOfLevel (h_level _)) h_hol⟩
  -- The level used is `√(-d)`, with `d = P.d` and `K = ℚ(√(-d))`; its norm `√d` is at most `√b`.
  simpa [P.d_prime.pos] using D.le_of_hasLogBound

/-- The space `W̃ = W_j ⊕ (E^j)⁻ ⊕ E^(3 m - j)`. -/
noncomputable abbrev paddedSpace : Space D.E (D.RowIndex ⊕ PadIndex j) (padSigns j) :=
  (D.spaceW j).sum ((stdSpace D.E (Fin j)).neg.sum (stdSpace D.E (Fin (2 * D.m + (D.m - j)))))

/-- For `g` in the group of `W_j = D.spaceW j`, the first minimum (cut off at `1`) of `W_j` moved by
`g` is at most that of the padded space `W̃ = paddedSpace j` moved by `G.sum (g, 1)`. So extending
`g` by `1` to `W̃` does not lower the first minimum. -/
lemma firstMinimum_le_paddedSpace (g : New.G D.E (D.signsW j)) :
    ((D.spaceW j).move g).firstMinimum ≤ ((paddedSpace j).move (G.sum (g, 1))).firstMinimum := by
  have h_pad : 1 ≤ (((stdSpace D.E (Fin j)).neg.sum
      (stdSpace D.E (Fin (2 * D.m + (D.m - j))))).move 1).firstMinimum := by
    rw [← G.sum.map_one]
    -- Both summands are definite, so both have first minimum at least `1`.
    exact (le_inf (Space.one_le_firstMinimum fun _ _ ↦ rfl)
      (Space.one_le_firstMinimum fun _ _ ↦ rfl)).trans inf_le_firstMinimum_sum
  grw [← inf_le_firstMinimum_sum, ← h_pad, inf_of_le_left Space.firstMinimum_le_one]

/-- Step 1 of the proof that products span. Let `1 ≤ j ≤ m`, let `W_j` be the diagonal space with
signs `D.signsW j`, let `W̃ = paddedSpace j` be its sum with a definite space of each sign, and let
`S = signedSpace D.E (1 ⊕ᵥ -1)` be the space of signature `(2 m, m)`. Assume that the order `o` puts
the signs `+1` of `S` first, that the carrier `φ° = carrierForm D.E D.m` is automorphic of every
level and rapidly decreasing (`rapidOfLevel`), and that the quotient of minors
`m_u₁ = holMinorsPi _ u₁` is integrable on the real group of `S`, where `u₁ = flatKernelWeight D` is
the weight of the kernels on `S` and `W♭ = E^(6 m + 1)`. Let `g₁` be a point of the group of `S`,
let `Ψ` be a function on matrices modulo `ϖ²` (`untwistedModulus 2`, with `ϖ` the product of the
chosen places above the level primes), and let `θ[Ψ, P]` be the theta kernel `modKernel` of
`(S, W̃)` with datum `Ψ`, polynomial the product of minors `P = paddedMinorProd j`, and characters
`υ ^ m` and `carrierChar j` of `U(1)`, where `υ = upsilonU1` has weight `1`. Then, as a function of
the point `g` of the group of `W_j`, the integral of `φ°(g₁ h) θ[Ψ, P](g₁ h, (g, 1)) m_u₁(h)` over
the real points `h` is a linear combination of the functions `choiceFn j i`. These are the integrals
of `φ°` against theta kernels of `(S, W̃ ⊕ W♭)`, one for each choice `i` of an additive character
of the matrices modulo `ϖ²`, a class of `U(W♭)` at level `ϖ²` and rows of determinants. -/
lemma exists_sum_choiceFn_eq_integral {o : D.CarrierIndex → ℤ} (ho : IsPosFirstOrder (1 ⊕ᵥ -1) o)
    (h_level : ∀ N : 𝓞 D.E, carrierForm D.E D.m ∈ rapidOfLevel (signedSpace D.E (1 ⊕ᵥ -1)) N)
    (h_int : MeasureTheory.Integrable (holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D)))
    (g₁ : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ))
    (Ψ : Matrix (D.RowIndex ⊕ PadIndex j) D.CarrierIndex (D.untwistedModulus 2).ResidueRing → ℂ) :
    ∃ c : ChoiceIndex j → ℂ, ∀ g : New.G D.E (D.signsW j),
      ∑ i : ChoiceIndex j, c i * choiceFn j i g =
      ∫ h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ), carrierForm D.E D.m (g₁ * (h, 1)) *
        modKernel (signedSpace D.E (1 ⊕ᵥ -1)) (paddedSpace j) (upsilonU1 ^ D.m) (carrierChar j)
          (D.untwistedModulus 2) Ψ (paddedMinorProd j) (g₁ * (h, 1)) (G.sum (g, 1)) *
        holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D) h := by
  -- The reproducing formula on `(S, W♭)` turns the real integral into pairings with kernels `θ₂ r`.
  -- The product of `θ[Ψ, P]` with `θ₂ r` is a kernel on `W̃ ⊕ W♭`, and Fourier expansion of its
  -- datum writes it as a combination of the kernels that define `choiceFn`.
  let S : Space D.E D.CarrierIndex (1 ⊕ᵥ -1) := signedSpace D.E (1 ⊕ᵥ -1)
  let φ : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ) → ℂ := carrierForm D.E D.m
  let 𝔪 : Modulus D.E := D.untwistedModulus 2
  have h_card : 2 * card D.CarrierIndex < card D.FlatIndex := by
    simp only [card_sum, Fintype.card_fin]
    omega
  obtain ⟨e⟩ : Nonempty (D.CarrierIndex ↪ D.FlatIndex) :=
    Function.Embedding.nonempty_of_card_le (by omega)
  let δ : Matrix D.FlatIndex D.CarrierIndex 𝔪.ResidueRing → ℂ :=
    Pi.single (inclMatrix 𝔪.ResidueRing e) 1
  let Q (r : D.RowChoice) : MvPolynomial (D.Φ × D.FlatIndex × D.CarrierIndex) ℂ :=
    pairedDetProd (fun τ a b ↦ .X (τ, a, inl b)) fun w k ↦
      ((D.shortRows r).map (Φ w)).submatrix (r.rows w k) id
  -- The kernels on `(S, W̃)`, on `(S, W♭)` and on `(S, W̃ ⊕ W♭)`.
  let θ₁ (g : New.G D.E (D.signsW j)) (x : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) : ℂ :=
    modKernel S (paddedSpace j) (upsilonU1 ^ D.m) (carrierChar j) 𝔪 Ψ (paddedMinorProd j) x
      (G.sum (g, 1))
  let θ₂ (r : D.RowChoice) (x : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) : ℂ :=
    modKernelStdSpace S (upsilonU1 ^ D.m) 1 𝔪 δ (Q r) x r.classRep
  let θ (i : ChoiceIndex j) (g : New.G D.E (D.signsW j))
      (x : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) : ℂ :=
    modKernel S ((paddedSpace j).sum (stdSpace D.E D.FlatIndex)) (upsilonU1 ^ D.m) (carrierChar j)
      𝔪 (traceChar i.matrix)
      (renameRowsCols inl id (paddedMinorProd j) * renameRowsCols inr id (Q i.rowChoice)) x
      (G.sum (G.sum (g, 1), (1, i.rowChoice.classRep)))
  have h_choiceFn (i : ChoiceIndex j) (g : New.G D.E (D.signsW j)) :
      choiceFn j i g = ∫ x, φ x * θ i g x ∂S.quotMeasure := rfl
  -- Reproduction on `(S, W♭)`: the translates of the power of one minor lie in the span of the
  -- products of determinants formed with the short basis `shortRows` of each class.
  obtain ⟨c, h_repro⟩ : ∃ c : D.RowChoice → ℂ, ∀ ψ ∈ rapidOfLevel S (D.piM ^ 2),
      ∫ h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ),
        ψ (g₁ * (h, 1)) * holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D) h =
      ∑ r, c r * ∫ x, ψ x * θ₂ r x ∂S.quotMeasure := by
    have h_weight : flatKernelWeight D =
        fun _ ↦ (-D.reducedHalfGap ⊕ᵥ card D.FlatIndex : D.CarrierIndex → ℤ) := by
      ext w (_ | _) <;> simp [flatKernelWeight]
    rw [h_weight] at h_int ⊢
    obtain ⟨minor_ne, minor_hol⟩ := prod_variableMinor_mem_holomorphicData (E := D.E) ho
      (Function.Embedding.inl.trans e) D.reducedHalfGap fun _ ↦ D.m
    have h_unit (r : D.RowChoice) : IsUnit (D.shortRows r) := by simp [shortRows]
    exact reproducing_formula_modKernel ho D.ideal_untwistedModulus_eq_span
      nonempty_modulus_places S (hasWeight_upsilonU1_pow D.m) .one (by simp [IsKDominant]) h_int
      h_card e minor_ne minor_hol (fun p rows ↦ Q (p, rows))
      (fun p ↦ realPairWeil_mem_span_pairedDetProd _ (h_unit (p, 0)) _ _) g₁
  -- The product of `Ψ` with the datum `δ` is a combination of additive characters.
  obtain ⟨f, h_fourier⟩ : ∃ f : Matrix D.CarrierIndex (FirstFactorIndex j) 𝔪.ResidueRing → ℂ,
      ∑ Λ, f Λ • traceChar Λ = fun z ↦ Ψ z.toRows₁ * δ z.toRows₂ :=
    exists_sum_smul_addChar_trace_eq 𝔪.isPrimitive_primAddChar _
  -- The two kernels multiply to the kernel of the sum of the spaces, which is linear in its datum.
  have h_seesaw (r : D.RowChoice) (g : New.G D.E (D.signsW j))
      (x : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) :
      θ₁ g x * θ₂ r x = ∑ Λ, f Λ * θ (Λ, r) g x := by
    simp only [θ₁, θ₂, θ]
    rw [← modKernel_sum_right, ← h_fourier, mul_one]
    simp only [← modKernelBilin_apply, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
  -- The products of `φ` with the kernels are rapidly decreasing of level `ϖ²`.
  have θ₁_level (g : New.G D.E (D.signsW j)) : φ * θ₁ g ∈ rapidOfLevel S (D.piM ^ 2) :=
    mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (hb := carrierChar_hasWeight j)
      (fun _ _ ↦ rfl) (h_level (D.piM ^ 2)) ..
  have θ_level (i : ChoiceIndex j) (g : New.G D.E (D.signsW j)) :
      φ * θ i g ∈ rapidOfLevel S (D.piM ^ 2) :=
    mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (hb := carrierChar_hasWeight j)
      (fun _ _ ↦ rfl) (h_level (D.piM ^ 2)) ..
  have h_pairing (r : D.RowChoice) (g : New.G D.E (D.signsW j)) :
      ∫ x, (φ * θ₁ g) x * θ₂ r x ∂S.quotMeasure = ∑ Λ, f Λ * choiceFn j (Λ, r) g := by
    simp only [Pi.mul_apply, mul_assoc, h_seesaw, h_choiceFn]
    exact integral_mul_sum_const_mul fun Λ ↦ θ_level (Λ, r) g
  refine ⟨fun i ↦ c i.rowChoice * f i.matrix, fun g ↦ ?_⟩
  calc ∑ i : ChoiceIndex j, c i.rowChoice * f i.matrix * choiceFn j i g
    _ = ∑ r, c r * ∑ Λ, f Λ * choiceFn j (Λ, r) g := by
      simp only [mul_sum, ← mul_assoc]
      exact sum_prod_type_right _
    _ = ∑ r, c r * ∫ x, (φ * θ₁ g) x * θ₂ r x ∂S.quotMeasure := by simp only [h_pairing]
    _ = ∫ h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ),
        (φ * θ₁ g) (g₁ * (h, 1)) * holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D) h :=
      (h_repro (φ * θ₁ g) (θ₁_level g)).symm

variable (D) in
/-- The identity `b ^ (-20 n_*) b ^ n_* = b ^ (-19 n_*)` for `n_* = nStar D`. -/
lemma inv_pow_twenty_mul_pow_nStar :
    (D.b ^ (20 * nStar D))⁻¹ * D.b ^ nStar D = (D.b ^ (19 * nStar D))⁻¹ := by
  field

/-- Let `S = signedSpace D.E (1 ⊕ᵥ -1)`. Suppose the first minimum of `S` moved by `g₁` is at least
`(5 b √b) ^ (-1 / 2)`. Suppose that of `D.spaceW j` moved by `g` is at least
`(5 b ^ 24) ^ (-1 / 2)`. Then the first minimum of `S` moved by `g₁`, times that of `paddedSpace j`
moved by `G.sum (g, 1)`, is at least `b ^ (-13)`. Here `b = D.b` is the large scale of the data. -/
lemma inv_pow_le_firstMinimum_mul {g₁ : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)}
    {g : New.G D.E (D.signsW j)}
    (h_g₁ : (√(5 * D.b * √D.b))⁻¹ ≤ ((signedSpace D.E (1 ⊕ᵥ -1)).move g₁).firstMinimum)
    (h_g : (√(5 * D.b * D.b ^ 23))⁻¹ ≤ ((D.spaceW j).move g).firstMinimum) :
    (D.b ^ 13)⁻¹ ≤ ((signedSpace D.E (1 ⊕ᵥ -1)).move g₁).firstMinimum *
      ((paddedSpace j).move (G.sum (g, 1))).firstMinimum := by
  have h_pos : 0 < ((signedSpace D.E (1 ⊕ᵥ -1)).move g₁).firstMinimum := Space.firstMinimum_pos
  grw [← firstMinimum_le_paddedSpace, ← h_g, ← h_g₁]
  exact D.le_of_hasLogBound

/-- Let `S` be the space with index set `D.CarrierIndex` of `3 m` elements, and let `W̃` be the
padded space `W_j ⊕ (E^j)⁻ ⊕ E^(3 m - j)`: `j` signs `-1`, then `3 m - j` signs `1`. Both have rank
at most `t = 5 r`. The index set of `W̃` is `D.RowIndex ⊕ PadIndex j`: the `r` indices of `W_j` and
the `3 m` indices of the padding. -/
lemma card_carrierIndex_le_and_card_sum_padIndex_le :
    card D.CarrierIndex ≤ D.t ∧ card (D.RowIndex ⊕ PadIndex j) ≤ D.t := by
  simp [↓card_rowIndex]
  grind

/-- Let `f` be holomorphic of weight `(0; 3 m)` on the real group of the space `S` of signature
`(2 m, m)`, for an order `o` with the signs `+1` first. Let `1 ≤ j ≤ m` and let `W̃` be the padded
space of rank `r + 3 m` with signs `padSigns j`. Let `c_P` be the matrix coefficient
`polyMatrixCoeff` of the Fock vector of the product of minors `P = paddedMinorProd j` on `(S, W̃)`;
the weight `γ` of the first character is arbitrary, and that of the second is `m - μ₁⁺`, with
`μ₁⁺ = #(DetIndex j w)` the number of columns of the partition `μ⁺` of the `j`-th lift at the place
`w`. Let `m₁`, `m₃` be the quotients of minors `holMinorsPi` of the weights
`u₁ = flatKernelWeight D`, that of the kernels on `S` and `E^(6 m + 1)`, and
`u₃ = antiholomorphicWeight j`, that of the antiholomorphic factor of `c_P(·, 1)`. If
`f c_P(·, 1) m₁` is integrable, its integral is `f(1) c_P(1, 1)` times the integral of
`|m₃| ^ 2`. -/
lemma integral_mul_polyMatrixCoeff_paddedMinorProd {o : D.CarrierIndex → ℤ}
    (ho : IsPosFirstOrder (1 ⊕ᵥ -1) o)
    {f : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ) → ℂ}
    (hf : IsHolOfWeight (1 ⊕ᵥ -1) o (fun _ : D.Φ ↦ (0 ⊕ᵥ 3 * D.m : D.CarrierIndex → ℤ)) f)
    (γ : D.Φ → ℤ)
    (h_int : MeasureTheory.Integrable fun h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ) ↦ f h *
      polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ (fun w : D.Φ ↦ D.m - card (DetIndex j w))
        (paddedMinorProd j) h 1 *
      holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D) h) :
    ∫ h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ), f h *
      polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ (fun w : D.Φ ↦ D.m - card (DetIndex j w))
        (paddedMinorProd j) h 1 *
      holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D) h =
    (∫ h, ‖holMinorsPi (1 ⊕ᵥ -1) (antiholomorphicWeight j) h‖ ^ 2 : ℝ) * (f 1 *
      polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ (fun w : D.Φ ↦ D.m - card (DetIndex j w))
        (paddedMinorProd j) 1 1) := by
  -- The holomorphic factor of `c_P(·, 1)` times `f m₁` is holomorphic of the weight of `m₃`.
  set m₁ := holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D)
  let m₂ := holMinorsPi (1 ⊕ᵥ -1) (holomorphicWeight j)
  let m₃ := holMinorsPi (1 ⊕ᵥ -1) (antiholomorphicWeight j)
  set cP := polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ (fun w ↦ D.m - card (DetIndex j w))
    (paddedMinorProd j)
  obtain ⟨h_dom₁, -, h_dom₃, -⟩ := flatKernelWeight_antiholomorphicWeight_bounds j o
  have h_dom₂ (w : D.Φ) : IsKDominant (1 ⊕ᵥ -1) o (holomorphicWeight j w) := by
    simp [holomorphicWeight, IsKDominant]
  have h_weight : antiholomorphicWeight j =
      (fun _ ↦ (0 ⊕ᵥ 3 * D.m : D.CarrierIndex → ℤ)) + flatKernelWeight D +
        holomorphicWeight j := by
    ext w (_ | _) <;> simp [antiholomorphicWeight, flatKernelWeight, holomorphicWeight, -card_sum]
    grind [card_firstFactorIndex j]
  have h_const : IsHolOfWeight (1 ⊕ᵥ -1) o (holomorphicWeight j) fun h ↦ cP 1 1 * m₂ h := by
    simpa using IsHolOfWeight.sum (T := {()}) (fun _ : Unit ↦ cP 1 1)
      fun _ ↦ isHolOfWeight_holMinorsPi ho h_dom₂
  have h_hol : IsHolOfWeight (1 ⊕ᵥ -1) o (antiholomorphicWeight j)
      fun h ↦ f h * m₁ h * (cP 1 1 * m₂ h) := by
    rw [h_weight]
    exact (hf.mul ho.1 (isHolOfWeight_holMinorsPi ho h_dom₁)).mul ho.1 h_const
  have h_integrand (h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) :
      f h * cP h 1 * m₁ h = f h * m₁ h * (cP 1 1 * m₂ h) * starRingEnd ℂ (m₃ h) := by
    simp only [cP, polyMatrixCoeff_paddedMinorProd j γ h]
    ring
  simp only [h_integrand] at h_int ⊢
  simpa [m₁, m₂, m₃] using h_hol.integral_mul_conj_holMinorsPi ho h_dom₃ h_int

/-- There is a bounded function `F₀` on the real group of `W_j` with `F₀ 1 ≠ 0` such that, at every
adelic `g` off the cusps, in the sense that the lattice of `W_j` moved by `g` has first minimum at
least `(5 b ^ 24) ^ (-1 / 2)`, some combination `F` of the `choiceFn j i` has `|F (g h) - F₀ h| ≤ 2
b ^ (-19 n_*) |F₀ 1| |h| ^ (6 n_*)` for all real `h`. Here `|h| = maxOpNorm h`, `b = D.b` is the
large scale of the data, and `n_* = nStar D = 2 f t ^ 3`, with `f` the number of infinite places and
`t = 5 r`. -/
theorem exists_choiceFn_approx : ∃ (F₀ : GInf D.E (D.signsW j) → ℂ) (C : ℝ),
    F₀ 1 ≠ 0 ∧
    (∀ h : GInf D.E (D.signsW j), ‖F₀ h‖ ≤ C) ∧
    ∀ g : New.G D.E (D.signsW j), (√(5 * D.b * D.b ^ 23))⁻¹ ≤ ((D.spaceW j).move g).firstMinimum →
      ∃ c : ChoiceIndex j → ℂ, ∀ h : GInf D.E (D.signsW j),
        ‖∑ i : ChoiceIndex j, c i * choiceFn j i (g * (h, 1)) - F₀ h‖ ≤
          2 * (D.b ^ (19 * nStar D))⁻¹ * ‖F₀ 1‖ * maxOpNorm h ^ (6 * nStar D) := by
  -- With a peak `g₁` of `φ°` put `F₀ h = ∫ φ°(g₁ h') c_P(h', h) m_u₁(h') dh'`. Its value at `1` is
  -- `c_P(1, 1) φ°(g₁) J` with `J = ∫ |m_u₃|²`. Away from the cusps a theta kernel is close to `c_P`
  -- (`exists_datum_norm_modKernel_sub_polyMatrixCoeff_le`), and the same integral with the kernel
  -- in place of `c_P` is a combination of the `choiceFn j i`. The bound `h_bound` for the integral
  -- of the difference has the same factors `|φ°(g₁)|` and `J`, so it is small against `|F₀ 1|`.
  let φ := carrierForm D.E D.m
  let S := signedSpace D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)
  obtain ⟨φ_level, o, ho, φ_hol⟩ : (∀ N, φ ∈ rapidOfLevel S N) ∧
      ∃ o, IsPosFirstOrder (1 ⊕ᵥ -1) o ∧ IsAdelicHol o (fun _ ↦ 0 ⊕ᵥ 3 * D.m) φ :=
    carrierForm_mem_rapidOfLevel_and_isAdelicHol D.m_even (isTameFor_twistedChiMPow (c := 2) j 1)
  obtain ⟨g₁, g₁_peak, g₁_min⟩ :
      ∃ g₁, IsPeak φ g₁ ∧ (√(5 * D.b * √D.b))⁻¹ ≤ (S.move g₁).firstMinimum :=
    exists_isPeak_carrierForm D ho φ_level φ_hol
  let cP := polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) (fun _ ↦ D.m) (fun w ↦ D.m - card (DetIndex j w))
    (paddedMinorProd j)
  obtain ⟨cP_ne, B, cP_le⟩ : cP 1 1 ≠ 0 ∧ ∃ B : ℝ, ∀ h h', ‖cP h h'‖ ≤ B :=
    polyMatrixCoeff_paddedMinorProd_ne_zero_and_bounded j _ _
  let m₁ := holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D)
  let J : ℝ := ∫ h, ‖holMinorsPi (1 ⊕ᵥ -1) (antiholomorphicWeight j) h‖ ^ 2
  let ι (h : GInf D.E (D.signsW j)) : GInf D.E (padSigns j) := (G.sum ((h, 1), 1)).1
  let F₀ (h : GInf D.E (D.signsW j)) : ℂ := ∫ h', φ (g₁ * (h', 1)) * cP h' (ι h) * m₁ h'
  -- The weights `u₁`, `u₃` satisfy the hypotheses of `integrable_mul_holMinorsPi`.
  obtain ⟨h_rank, h_rank'⟩ := card_carrierIndex_le_and_card_sum_padIndex_le j
  obtain ⟨u₁_dom, u₁_gap, u₃_dom, u₃_gap, u₃_le⟩ :=
    flatKernelWeight_antiholomorphicWeight_bounds j o
  have J_pos : 0 < J := integral_norm_holMinorsPi_sq_pos h_rank ho u₃_dom u₃_gap
  have h_bound {A : GInf D.E (1 ⊕ᵥ -1) → ℂ} {c : ℝ} (hA : Continuous A)
      (hA_le : ∀ h', ‖A h'‖ ≤ c * maxOpNorm h' ^ (6 * nStar D)) :
      MeasureTheory.Integrable (fun h' ↦ φ (g₁ * (h', 1)) * A h' * m₁ h') ∧
      ‖∫ h', φ (g₁ * (h', 1)) * A h' * m₁ h'‖ ≤ 2 * ‖φ g₁‖ * c * D.b ^ nStar D * J := by
    have prod_le (h' : GInf D.E (1 ⊕ᵥ -1)) :
        ‖φ (g₁ * (h', 1)) * A h'‖ ≤ 2 * ‖φ g₁‖ * c * maxOpNorm h' ^ (6 * nStar D) := by
      grw [norm_mul, g₁_peak.norm_le, hA_le, ← mul_assoc]
    exact integrable_mul_holMinorsPi h_rank ho u₃_dom u₁_dom u₃_gap u₁_gap u₃_le
      ((φ_hol g₁).continuous.fun_mul hA) prod_le
  have F₀_bound (h : GInf D.E (padSigns j)) :
      MeasureTheory.Integrable (fun h' ↦ φ (g₁ * (h', 1)) * cP h' h * m₁ h') ∧
      ‖∫ h', φ (g₁ * (h', 1)) * cP h' h * m₁ h'‖ ≤ 2 * ‖φ g₁‖ * B * D.b ^ nStar D * J :=
    h_bound (by fun_prop [polyMatrixCoeff]) fun h' ↦ (cP_le h' h).trans
      (le_mul_of_one_le_right ((norm_nonneg _).trans (cP_le 1 1))
        (one_le_pow₀ (one_le_maxOpNorm h')))
  have F₀_one : F₀ 1 = J * (φ g₁ * cP 1 1) := by
    simpa [F₀, ι, J, cP, m₁, φ, mk_one_one] using
      integral_mul_polyMatrixCoeff_paddedMinorProd j ho (φ_hol g₁) (fun _ ↦ D.m) (F₀_bound 1).1
  refine ⟨F₀, 2 * ‖φ g₁‖ * B * D.b ^ nStar D * J,
    by simp [F₀_one, J_pos.ne', g₁_peak.ne_zero, cP_ne, φ], fun h ↦ (F₀_bound (ι h)).2,
    fun g hg ↦ ?_⟩
  -- Away from the cusps the kernel `θ Ψ` of some datum `Ψ` is close to `c_P`.
  let θ (Ψ : Matrix (D.RowIndex ⊕ PadIndex j) D.CarrierIndex (D.untwistedModulus 2).ResidueRing →
    ℂ) :=
    modKernel S (paddedSpace j) (upsilonU1 ^ D.m) (carrierChar j) (D.untwistedModulus 2) Ψ
      (paddedMinorProd j)
  obtain ⟨d, hd, h_homog⟩ := exists_eval_smul_paddedMinorProd j
  obtain ⟨Ψ, θ_near⟩ : ∃ Ψ, ∀ h' h, ‖θ Ψ (g₁ * (h', 1)) (G.sum (g, 1) * (h, 1)) - cP h' h‖ ≤
      (D.b ^ (20 * nStar D))⁻¹ * (maxOpNorm h' * maxOpNorm h) ^ (6 * nStar D) * ‖cP 1 1‖ :=
    exists_datum_norm_modKernel_sub_polyMatrixCoeff_le S (paddedSpace j) h_rank h_rank'
      (hasWeight_upsilonU1_pow D.m) (carrierChar_hasWeight_sub_card j) h_homog hd
      (inv_pow_le_firstMinimum_mul j g₁_min hg)
  obtain ⟨c, sum_eq⟩ : ∃ c : ChoiceIndex j → ℂ, ∀ x, ∑ i, c i * choiceFn j i x =
      ∫ h', φ (g₁ * (h', 1)) * θ Ψ (g₁ * (h', 1)) (G.sum (x, 1)) * m₁ h' :=
    exists_sum_choiceFn_eq_integral j ho φ_level
      (integrable_holMinorsPi h_rank ho u₁_dom u₁_gap) g₁ Ψ
  refine ⟨c, fun h ↦ ?_⟩
  -- The difference is the integral of `φ° (θ Ψ - c_P) m_u₁`, to which `h_bound` applies.
  let A (h' : GInf D.E (1 ⊕ᵥ -1)) : ℂ :=
    θ Ψ (g₁ * (h', 1)) (G.sum (g, 1) * (ι h, 1)) - cP h' (ι h)
  let ε : ℝ := (D.b ^ (20 * nStar D))⁻¹ * maxOpNorm (ι h) ^ (6 * nStar D) * ‖cP 1 1‖
  have A_le (h' : GInf D.E (1 ⊕ᵥ -1)) : ‖A h'‖ ≤ ε * maxOpNorm h' ^ (6 * nStar D) :=
    (θ_near h' (ι h)).trans_eq (by ring)
  obtain ⟨diff_int, diff_le⟩ := h_bound (by fun_prop [polyMatrixCoeff, modKernel]) A_le
  have h_diff : ∑ i, c i * choiceFn j i (g * (h, 1)) - F₀ h =
      ∫ h', φ (g₁ * (h', 1)) * A h' * m₁ h' := by
    have h_point : G.sum (g * (h, 1), 1) = G.sum (g, 1) * (ι h, 1) := by
      simp [ι, G.sum, Pi.mul_def, ← map_mul]
    rw [sum_eq, h_point, sub_eq_iff_eq_add,
      ← MeasureTheory.integral_add diff_int (F₀_bound (ι h)).1]
    simp [A, ← add_mul, ← mul_add]
  have norm_one : ‖F₀ 1‖ = J * (‖φ g₁‖ * ‖cP 1 1‖) := by simp [F₀_one, abs_of_pos J_pos]
  calc ‖∑ i, c i * choiceFn j i (g * (h, 1)) - F₀ h‖
    _ ≤ 2 * ‖φ g₁‖ * ε * D.b ^ nStar D * J := by rwa [h_diff]
    _ ≤ 2 * ‖φ g₁‖ * ((D.b ^ (20 * nStar D))⁻¹ * maxOpNorm h ^ (6 * nStar D) * ‖cP 1 1‖) *
        D.b ^ nStar D * J := by
      unfold ε
      grw [maxOpNorm_sum_one_le j h]
    _ = 2 * (D.b ^ (19 * nStar D))⁻¹ * ‖F₀ 1‖ * maxOpNorm h ^ (6 * nStar D) := by
      rw [norm_one, ← inv_pow_twenty_mul_pow_nStar D]
      ring

end NaturalFormNear

/-!
## The proof that products span

The good form is called `F`. By the reproducing formula `New.Rows.reproducing_formula_modKernel`,
the vanishing pairings give a vanishing integral over the real group.
-/

section Separation

open ComplexConjugate Parameters Rows Submodule WeilData Finset Fintype Fock DescentPair

variable {P : Parameters} {D : Data P} (j : D.LiftIndex)

/-- The pairing `⟨ζ, θ°(g, ·)⟩` of a form `ζ` on the definite space `V°` with the theta kernel `θ°`
of `(W_j, V°)`; it is conjugate-linear in `ζ`. The form is given by its values at the classes
`SecondFactorClasses` of `U(V°)` at principal level `ϖ²`, where `untwistedModulus 2` is the modulus
`ϖ²`. The values lie in the Weyl module, written in the basis `WeylIndexFamily`, of the diagrams
`μ⁻` with the column counts `colsMinus` of `untwistedDescentPair j`, the `j`-th descent pair at the
trivial twist. The term of a class `c` is the kernel `modKernelStdSpace` at `(g, c)` whose datum is
the indicator of the inclusion matrix of `W_j` in `V°` modulo `ϖ²` and whose polynomial is that of
the conjugate of `ζ c` in the variables of the negative basis vectors of `W_j` (`letterPoly`). -/
noncomputable def thetaKernelPairing (ζ : D.SecondFactorClasses →
      WeylIndexFamily (fun _ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus → ℂ)
    (g : New.G D.E (D.signsW j)) : ℂ :=
  ∑ c : D.SecondFactorClasses,
    modKernelStdSpace (D.spaceW j) (untwistedDescentPair j).charW (upsilonU1 ^ (D.m / 2 - j : ℤ))
    (D.untwistedModulus 2) (Pi.single (inclMatrix (D.untwistedModulus 2).ResidueRing .inl) 1)
    (letterPoly (D.signsW j) (untwistedDescentPair j).numbering (-1)
      (untwistedDescentPair j).colsMinus
      (star (ζ c))) g c.out

variable {j}

/-- Let `1 ≤ j ≤ m`, let `W_j = D.spaceW j` be the diagonal hermitian space with signs `D.signsW j`,
and let `F` be a good form on `W_j`: an automorphic form whose real type is the discrete series of
doubled parameter `paramW`, fixed by the principal congruence subgroup at the chosen places above
the level primes, and in the image of the idempotent `e₀` of the group algebra of the finite groups
`GL_r` over their residue fields. Then for every adelic `g` the function `h ↦ conj F(g h)` on the
real group is holomorphic (`IsAdelicHol`). -/
lemma isAdelicHol_star_goodForms (F : D.goodForms (D.spaceW j)) :
    IsAdelicHol (orderW j) (conjHolomorphicWeight j) fun g : New.G D.E (D.signsW j) ↦
      star ((F : New.G D.E (D.signsW j) → ℂ) g) := by
  -- The lift `L` is injective, so its adjoint composed with it is injective, hence onto in finite
  -- dimension: `F` is a descent.
  let L : D.principalForms (D.spaceW j) →ₗ[ℂ] (D.descentPair .one j).FormV := D.singleLift .one j
  obtain ⟨y, lift⟩ : ∃ y : D.principalForms (D.spaceW j), L.adjoint (L y) = F.val :=
    (L.adjoint ∘ₗ L).surjective_of_injective
      ((LinearMap.adjoint_comp_self_injective_iff L).mpr (D.singleLift_injective .one)) F.val
  have h_descent :
      (F : New.G D.E (D.signsW j) → ℂ) = (D.descentPair .one j).normalizedDescent (L y) := by
    rw [← lift, D.coe_adjoint_singleLift]
  -- The polynomial of the highest vector is a product of joint harmonics, hence holomorphic; by
  -- equivariance so is the polynomial of every vector.
  obtain ⟨⟨harm, joint, pol_top⟩, -⟩ := (D.fitsParams_descentPair .one j).exists_isJointHarmonic
  let pol := polyVector (realSigns D.E (homSigns (D.signsW j) 1)) ∘ₗ
    (untwistedDescentPair j).fockPoly
  have hol ξ : pol ξ ∈ holomorphicData (D.signsW j) 1 (orderW j) (conjHolomorphicWeight j)
      (fun _ ↦ Exchange.negCount (untwistedDescentPair j).signs)
      (fun w ↦ (card (D.RowIndex ⊕ Fin D.t) / 2 : ℕ) + (D.descentPair .one j).weight w) :=
    mem_holomorphicData_of_highestVector pol (fun w ↦ (joint w).hasGap_row.injective)
      (realPairWeil_fockPoly _)
      (prod_mem_holomorphicData isPosFirstOrder_orderW paramW_lt_of_orderW_lt
        (fun w ↦ (joint w).isJointHighest) pol_top).2
  -- The conjugate of the descent is a finite combination of theta kernels with such polynomials.
  rw [h_descent]
  simpa [normalizedDescent, DescentPair.conjKernel, classSum, Rat.smul_def,
    ↓ finsum_eq_sum_of_fintype]
    using!
    fun g ↦ .sum _ fun _ ↦ isAdelicHol_pairTheta (hol _) g

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `1 ≤ j ≤ m`, let `F` be a good form on `W_j = D.spaceW j`, and write `F_i = choiceFn j i`
for the functions on the adelic group of `W_j` attached to the choices `i`. Let `V°` be the definite
space with index set `D.SecondFactorIndex`. A form `ζ` on `V°` assigns to each class at level `ϖ²` a
vector of the Weyl module of the diagrams with column counts `colsMinus`, in the basis
`WeylIndexFamily`, and `thetaKernelPairing j ζ g` pairs it with the theta kernel of `(W_j, V°)` at
`g`. Assume that the integrals of `F F_i` against these pairings, over the adelic group modulo its
rational points (`quotMeasure`), vanish for all `i` and `ζ`, and that the quotient of minors
`m_u° = holMinorsPi _ u°` is integrable, where `u° = kernelWeight j` is the weight of that kernel on
`W_j`. Then the integral of `F(g h) (∑ c_i F_i(g h)) m_u°(h)` over the real points `h` is zero for
every adelic `g`. -/
lemma integral_mul_sum_choiceFn_eq_zero (F : D.goodForms (D.spaceW j))
    (h_orth : ∀ (i : ChoiceIndex j) (ζ : D.SecondFactorClasses →
        WeylIndexFamily (fun _ : D.Φ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus → ℂ),
      ∫ g : New.G D.E (D.signsW j), (F : New.G D.E (D.signsW j) → ℂ) g * choiceFn j i g *
        thetaKernelPairing j ζ g ∂(D.spaceW j).quotMeasure = 0)
    (h_int : MeasureTheory.Integrable (holMinorsPi (D.signsW j) (kernelWeight j)))
    (c : ChoiceIndex j → ℂ) (g : New.G D.E (D.signsW j)) :
    ∫ h : GInf D.E (D.signsW j), (F : New.G D.E (D.signsW j) → ℂ) (g * (h, 1)) *
      (∑ i : ChoiceIndex j, c i * choiceFn j i (g * (h, 1))) *
      holMinorsPi (D.signsW j) (kernelWeight j) h = 0 := by
  classical
  have fit : (D.descentPair .one j).FitsParams D.paramW := D.fitsParams_descentPair .one j
  have prod_level (i : ChoiceIndex j) :
      F.val.val.val * choiceFn j i ∈ rapidOfLevel (D.spaceW j) (D.piM ^ 2) :=
    mul_choiceFn_mem_rapidOfLevel F i
  have rank_lt : 2 * card D.RowIndex < card D.SecondFactorIndex := by
    rw [D.card_rowIndex, card_sum, D.card_rowIndex, Fintype.card_fin, D.t_eq_five_mul_r]
    grind [D.hundred_mul_m_add_nine_lt_k, D.r_add_one]
  -- Reproduction on `(W_j, V°)`, for the basis polynomials `Q` in the negative letters; their span
  -- holds the translates of the highest vector.
  let Q := fockLetters (D.signsW j) (untwistedDescentPair j).numbering (-1) ∘
    nablaBasis ℂ (fun _ : D.Φ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus
  obtain ⟨top_ne, top_hol⟩ := letterPoly_highestVector_mem_holomorphicData
    (n' := D.SecondFactorIndex)
    (γ := fun _ ↦ Exchange.negCount (D.signsW j)) (w := fun _ ↦ D.m / 2 - j) isPosFirstOrder_orderW
    (paramW_lt_of_orderW_lt 1) (fit.paramsCorrespond 1).hasGap_left.injective (fit.numbering_eq 1) _
    fit.colsMinus_eq_zero
  obtain ⟨a, repro⟩ := reproducing_formula_modKernel isPosFirstOrder_orderW
    (D.ideal_untwistedModulus_eq_span (c := 2)) nonempty_modulus_places (D.spaceW j)
    (hasWeight_upsilonU1_pow _) (hasWeight_upsilonU1_zpow (D.m / 2 - j))
    (isKDominant_kernelWeight j) h_int rank_lt .inl top_ne top_hol (fun _ ↦ Q)
    (fun _ _ ↦ by
      -- `letterPoly` is `fockLetters` after `toPoly`.
      rw [letterPoly, LinearMap.comp_apply, AlgHom.toLinearMap_apply, realPairWeil_fockLetters]
      -- The translate of a `toPoly` is a combination of the `Q`; `clear` keeps the search short.
      clear * -
      aesop (add safe sum_mem, simp [Q, toPoly, linearCombination_apply])) g
  refine (repro _ (mul_sum_mem_rapidOfLevel prod_level)).trans
    (sum_eq_zero fun p _ ↦ mul_eq_zero_of_right _ ?_)
  -- The pairing of `F ∑ c_i F_i` with a kernel is a combination of the pairings of the `F F_i`,
  -- and each of these is that of `h_orth` for `ζ` supported at one class, where its value is the
  -- conjugate of a vector `v` whose polynomial is the basis polynomial.
  let K (x : New.G D.E (D.signsW j)) : ℂ :=
    modKernelStdSpace (D.spaceW j) (upsilonU1 ^ Exchange.negCount (D.signsW j))
      (upsilonU1 ^ (D.m / 2 - j : ℤ)) (D.untwistedModulus 2)
      (Pi.single (inclMatrix (D.untwistedModulus 2).ResidueRing .inl) 1) (Q p.2) x p.1.out
  obtain ⟨v, hv⟩ : ∃ v, toPoly _ (untwistedDescentPair j).colsMinus v = nablaBasis ℂ _ _ p.2 :=
    range_toPoly.ge prod_tableauPoly_mem_nabla
  have h_theta (x : New.G D.E (D.signsW j)) :
    thetaKernelPairing j (Pi.single p.1 (star v)) x = K x := by
    simp [thetaKernelPairing, K, Q, ← modKernelBilin_apply, apply_ite, letterPoly, hv, nablaBasis,
      Pi.single_apply]
    rfl
  have h_pair (i : ChoiceIndex j) :
      ∫ x, F.val.val x * (choiceFn j i * K) x ∂(D.spaceW j).quotMeasure = 0 := by
    simpa [h_theta, mul_assoc] using! h_orth i (Pi.single p.1 (star v))
  calc ∫ x, (F.val.val.val * fun y ↦ ∑ i, c i * choiceFn j i y) x * K x ∂(D.spaceW j).quotMeasure
    _ = ∫ x, F.val.val x * ∑ i, c i * (choiceFn j i * K) x ∂(D.spaceW j).quotMeasure := by
      simp [mul_assoc, sum_mul]
    _ = ∑ i, c i * ∫ x, F.val.val x * (choiceFn j i * K) x ∂(D.spaceW j).quotMeasure := by
      refine integral_mul_sum_const_mul (a := D.piM ^ 2) fun i ↦ ?_
      rw [← mul_assoc]
      exact mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (fun _ _ ↦ rfl)
        (prod_level i) ..
    _ = 0 := by simp only [h_pair, mul_zero, sum_const_zero]

/-- Products span. For admissible data `D` and `1 ≤ j ≤ m`, let `W_j = D.spaceW j` be the diagonal
hermitian space with signs `D.signsW j` and let `V°` be the definite space with index set
`D.SecondFactorIndex`. Let `F` be a good form on `W_j`: a form of principal level at the chosen
places in the image of the idempotent `e₀` of the group algebra of the finite groups at these
places. If `∫ F(g) F_i(g) θ°(g, ·) dg = 0` for all `i`, then `F = 0`. Here the `F_i = choiceFn j i`
are integrals of the carrier `carrierForm` against theta kernels, one for each of the finitely many
choices `i` of kernel data; the integral is over the adelic group modulo its rational points
(`quotMeasure`); and `thetaKernelPairing j ζ g` is the pairing of the theta kernel `θ°(g, ·)` of
`(W_j, V°)` with a form `ζ` on `V°`. Such a form assigns to each class at level `ϖ²` a vector of the
Weyl module, in the basis `WeylIndexFamily` indexed by the infinite places `D.Φ`, of the diagrams
whose column counts `colsMinus` belong to the data `untwistedDescentPair j` of the `j`-th lift. -/
theorem eq_zero_of_integral_choiceFn_thetaKernelPairing (F : D.goodForms (D.spaceW j))
    (h_orth : ∀ (i : ChoiceIndex j) (ζ : D.SecondFactorClasses →
        WeylIndexFamily (fun _ : D.Φ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus → ℂ),
      ∫ g : New.G D.E (D.signsW j), (F : New.G D.E (D.signsW j) → ℂ) g * choiceFn j i g *
        thetaKernelPairing j ζ g ∂(D.spaceW j).quotMeasure = 0) :
    F = 0 := by
  -- Suppose `F ≠ 0`. The peaks of `conj F` lie away from the cusp, where a combination of the
  -- `F_i` is close to a fixed `F₀`. Then `norm_apply_one_le_of_forall_isPeak` makes `F₀ 1` too
  -- small.
  have h_rank : card D.RowIndex ≤ D.t := by grind [D.card_rowIndex, D.t_eq_five_mul_r]
  obtain ⟨F₀, C, F₀_ne, F₀_le, near⟩ := exists_choiceFn_approx j
  suffices h_star : star (F : New.G D.E (D.signsW j) → ℂ) = 0 from
    Subtype.ext (Subtype.ext (Subtype.ext (star_eq_zero.1 h_star)))
  by_contra F_ne
  -- `conj F` has level `M √(-d)`, so its peaks are not deep in a cusp.
  have F_level : star (F : New.G D.E (D.signsW j) → ℂ) ∈
      rapidOfLevel (D.spaceW j) (D.M * sqrtNegDInE P D.towerExp) :=
    star_mem_rapidOfLevel
      (goodForms_mem_rapidOfLevel F (.mul_right ⟨_, D.piM_mul_star.symm⟩ _))
  have gap_one (τ : D.Φ) : HasHolGap (D.signsW j) (conjHolomorphicWeight j τ) 1 := fun a b ha hb ↦
    by
    have h_one : 1 ≤ 300 * nStar D := by linarith [D.nStar_pos]
    exact le_trans (by gcongr) (hasHolGap_conjHolomorphicWeight j τ a b ha hb)
  have peak_min {g : New.G D.E (D.signsW j)} (hg : IsPeak (fun g ↦ star (F.val.val g)) g) :
      (√(5 * D.b * D.b ^ 23))⁻¹ ≤ ((D.spaceW j).move g).firstMinimum :=
    hg.le_firstMinimum _ _ isPosFirstOrder_orderW gap_one (abs_conjHolomorphicWeight_le j)
      D.le_of_hasLogBound D.le_of_hasLogBound (by simp [star_sqrtNegDInE])
      (by simpa [NeZero.pos] using D.le_of_hasLogBound) F_level.1.1.rat_mul
      (apply_mul_of_mem_rapidOfLevel F_level) (isAdelicHol_star_goodForms F)
  obtain ⟨g, g_peak⟩ := exists_isPeak_of_mem_rapidOfLevel F_level F_ne
  have F₀_small : ‖F₀ 1‖ ≤
      (4 * D.b ^ nStar D + 1) * (2 * (D.b ^ (19 * nStar D))⁻¹ * ‖F₀ 1‖) := by
    refine norm_apply_one_le_of_forall_isPeak h_rank isPosFirstOrder_orderW
      (isKDominant_conjHolomorphicWeight j)
      (isKDominant_kernelWeight j) (hasHolGap_conjHolomorphicWeight j) (hasHolGap_kernelWeight j)
      (abs_conjHolomorphicWeight_le j) F.1.1.2.continuous.star (isAdelicHol_star_goodForms F) g_peak
        F₀_le
      fun x hx ↦ ?_
    obtain ⟨c, close⟩ := near x (peak_min hx)
    refine ⟨fun h ↦ ∑ i, c i * choiceFn j i (x * (h, 1)),
      .sum _ fun i ↦ isAdelicHol_choiceFn i x, close, ?_⟩
    simpa only [Pi.star_apply, star_star] using integral_mul_sum_choiceFn_eq_zero F h_orth
      (integrable_holMinorsPi h_rank isPosFirstOrder_orderW (isKDominant_kernelWeight j)
        (hasHolGap_kernelWeight j)) c x
  -- This is absurd: with `B = b ^ n_* > 10` we have `(4 B + 1) 2 < B ^ 2 ≤ B ^ 19`.
  have h_pow : 10 < D.b ^ nStar D :=
    have hb : 10 < D.b := D.lt_of_hasLogBound
    hb.trans_le (le_self_pow₀ (by linarith) D.nStar_pos.ne')
  have h_lt : (4 * D.b ^ nStar D + 1) * (2 * (D.b ^ (19 * nStar D))⁻¹) < 1 := by
    rw [← mul_assoc, mul_inv_lt_iff₀ (by positivity), one_mul, mul_comm 19, pow_mul D.b (nStar D)]
    calc (4 * D.b ^ nStar D + 1) * 2 < (D.b ^ nStar D) ^ 2 := by nlinarith
      _ ≤ (D.b ^ nStar D) ^ 19 := pow_le_pow_right₀ (by linarith) (by norm_num)
  nlinarith [norm_pos_iff.2 F₀_ne]

end Separation

end New.Data
