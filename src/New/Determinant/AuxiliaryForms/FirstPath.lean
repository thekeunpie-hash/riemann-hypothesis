module

import Mathlib.Algebra.Order.Star.Int
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.MeasureTheory.Integral.Pi
public import New.Determinant.AuxiliaryForms.DeepLevelPoincarePeriod
public import New.Determinant.AuxiliaryForms.PathData
public import Lib.Adelic.AutomorphicForms.Cuspidality
import Lib.Adelic.TraceFormula.OrbitalUnfolding
import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
import New.Appendix.DiscreteSeries.PositionGroup
import New.OneLift.ComparisonOperator.ExchangeData
import New.UpperBound.Objects.RowChain
public import New.Determinant.AuxiliaryForms.GridFirstColumns
public import New.Determinant.Chain.TriangleLifts
public import New.Determinant.Chain.TriangleNorms
import New.Determinant.Chain.ChainNorms

section
/-!
# Vanishing of forms on Y₀ orthogonal to the deep level on Ỹ^0_0

A form `y` of level `J_M = D.chosenLevel` on a hermitian space `V` is zero if it is orthogonal to
the restrictions of all forms of the deep level `J(𝔟)` on `V ⊕ ⟨1⟩`, translated by a suitable real
point `ω`. This requires size conditions on the level and a lower bound for the pairing of the
matrix coefficients for the parameter `l` of `V` and the parameter `l'` of `V ⊕ ⟨1⟩`.

Every bound `S` of `‖y‖` is halved. The smoothing of `y` is its convolution with the translated
coefficient for `l'`; the point `ω` with the lower bound for the pairing comes from steepness, in
the proof of `New.Data.exists_eq_zero_of_orthogonal_gridLevelForms`.

1. Decay: `New.Exchange.integral_typeKernelMajorant_le`.
2. The cusp: `New.Exchange.norm_le_half_of_firstMinimum_lt`.
3. A Poincaré series is a form, so its period is zero:
   `New.Exchange.poincare_period_translatedCoeff_eq_zero`.
4. Unfolding shows that the smoothing of `y` is small: `New.Exchange.norm_poincare_period_sub_le`
   and `New.Exchange.norm_realConv_translatedCoeff_le`.
5. Undoing the smoothing: `New.Exchange.norm_le_half_of_le_firstMinimum`.

## Main definitions and results

* `New.Exchange.HasDeepLevelSizes`: the size conditions. The real number `m` in them is at least a
  power of `β` that absorbs all constants in the estimates.
* `New.Exchange.eq_zero_of_petersson_translate_eq_zero`: the criterion at a given real point;
  `New.Exchange.exists_forall_eq_zero_of_petersson_restrict_eq_zero` chooses the point place by
  place.
* `New.Data.exists_eq_zero_of_orthogonal_gridLevelForms`: the forms of level `J(𝔟)` on `Ỹ^0_0`,
  restricted to `U(Y₀)` after translation by one real point, detect every nonzero form of level
  `J_M` on `Y₀`.

Notions from other files:
* `New.typeKernel`: `typeKernel l s` is the product over the infinite places `w` of the formal
  degree times the conjugate matrix coefficient `(l w).dsCoeff` of the parameter `l w`.
* `New.Space.IsForm`: `V.IsForm e F` says that `F` is automorphic, bounded, and fixed by the right
  convolution `New.realConv` with `e` over the real points (if `e` is integrable).
* `New.Space.firstMinimum`: the least norm of a nonzero vector of the lattice of a space, cut off at
  `1`; `V.move x` is the space `V` with its adelic frame multiplied by `x`.
* `New.Data.principalForms`, `New.Data.gridLevelForms`: the forms fixed by `D.chosenLevel`, and the
  forms on `Ỹ^i_0` fixed by the deep level, that is, the principal level of
  `D.gridLevelGen = D.piM ^ D.natB`, where `D.piM * star D.piM = D.M` is `M`.
* `New.Data.spaceY`: the hermitian space `Y_j` with its adelic frame, chosen as in
  `New.Data.exists_space_isStd_of_le_and_gram_eq_of_lt`.
* `(l w).HasLargeGap B`: the entries of `l w = 2λ` are distinct, of the parity of `card n - 1`, and
  entries of `λ` with different signs are at least `500 n³ + B` apart; `dsCoeff` is the matrix
  coefficient of the parameter and `dsKernel` its conjugate times the formal degree.

## Relation to the literature

Nonvanishing periods via Poincaré series of deep level and restriction results of Burger–Sarnak type
are known in the literature. Related work: Prasad–Schulze-Pillot, Generalised form of a conjecture
of Jacquet, 2008; Harris, Testing rationality of coherent cohomology of Shimura varieties, 2014;
Muić, Fourier coefficients of automorphic forms and integrable discrete series, 2015.
-/

@[expose] public section

/-!
## A vanishing criterion through restrictions of deep level forms

The parameter `l` of the forms on `V` has large gaps for `4 A`, and the parameter `l'` of the forms
on `V ⊕ ⟨1⟩` has large gaps for `2 A`, with `8 (card n + 1)² < A`.
-/

section DeepLevelTest

open New MeasureTheory Matrix Finset Fintype Norms.L2Operator ComplexConjugate Space DiscreteSeries
  U

variable {P : Parameters} {D : Data P} (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
  {s : n → ℤˣ} {V : Space D.E n s} (A : ℕ) {L N : ℕ}

/-- A Lipschitz bound under left translation for the product over the infinite places `w` of the
conjugate matrix coefficients `(l w).dsCoeff`. The parameters `l w` are integer vectors with entries
bounded by `L` and large gaps: entries of `l w / 2` with different signs differ by at least
`500 n³ + 4 A`. If `β` bounds `2000 (card n + L + 1)⁶` and the number `D.f` of infinite places and
`u` is a real point within `δ` of `1`, the values at `u⁻¹ * z` and `z` differ by at most `β² δ`. -/
lemma New.Exchange.norm_prod_conj_dsCoeff_inv_mul_sub_le {β δ : ℝ}
    {l : NumberField.InfinitePlace D.E → HCParam s}
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (hl : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L)
    (hβ : 2000 * (card n + L + 1) ^ 6 ≤ β) (hfβ : D.f ≤ β) {u : GInf D.E s} (hu : dist u 1 ≤ δ)
    (z : GInf D.E s) :
    ‖∏ w : NumberField.InfinitePlace D.E, conj ((l w).dsCoeff ((u⁻¹ * z) w)) -
      ∏ w : NumberField.InfinitePlace D.E, conj ((l w).dsCoeff (z w))‖ ≤ β * (β * δ) := by
  -- There are at most `β` factors, each of norm at most `1` and with Lipschitz constant `β`.
  have β_nonneg : 0 ≤ β := hβ.trans' (by positivity)
  let c (g : GInf D.E s) (w : NumberField.InfinitePlace D.E) : ℂ := conj ((l w).dsCoeff (g w))
  have factor_le (w : NumberField.InfinitePlace D.E) : ‖c (u⁻¹ * z) w - c z w‖ ≤ β * δ := by
    have const_le : (100 * (card n + L + 1) ^ 5 : ℝ) ≤ β := hβ.trans' (mod_cast by lia)
    -- `conj (dsCoeff g) = dsCoeff g⁻¹`, and `dsCoeff` is Lipschitz under right translation.
    calc ‖c (u⁻¹ * z) w - c z w‖
      _ = ‖(l w).dsCoeff ((z w)⁻¹ * u w : USign s) - (l w).dsCoeff ((z w)⁻¹ : USign s)‖ := by
        simp_rw [c, ← dsCoeff_inv (h_gap w), Pi.mul_apply, Pi.inv_apply, _root_.mul_inv_rev,
          inv_inv]
      _ ≤ 100 * (card n + L + 1) ^ 5 * ‖(u w : Matrix n n ℂ) - 1‖ :=
        norm_dsCoeff_sub_le (hg := h_gap w) (hl w) _ _
      _ ≤ β * δ := by
        gcongr
        exact (dist_eq_norm _ _).symm.trans_le ((dist_le_pi_dist u 1 w).trans hu)
  have sub_le : ‖c (u⁻¹ * z) - c z‖ ≤ β * δ := (pi_norm_le_iff_of_nonempty _).2 factor_le
  have norm_le_one (g : GInf D.E s) : ‖c g‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonempty _).2 fun w ↦ by simp [c, norm_dsCoeff_le_one (h_gap w)]
  -- `prodMap` is the product map `c ↦ ∏ w, c w`, multilinear of norm `1`.
  let prodMap : ContinuousMultilinearMap ℂ (fun _ : NumberField.InfinitePlace D.E ↦ ℂ) ℂ :=
    .mkPiAlgebra ℂ (NumberField.InfinitePlace D.E) ℂ
  calc ‖prodMap (c (u⁻¹ * z)) - prodMap (c z)‖
    _ ≤ ‖prodMap‖ * D.f * max ‖c (u⁻¹ * z)‖ ‖c z‖ ^ (D.f - 1) * ‖c (u⁻¹ * z) - c z‖ :=
      prodMap.norm_image_sub_le _ _
    _ ≤ ‖prodMap‖ * β * 1 ^ (D.f - 1) * (β * δ) := by
      grw [norm_le_one, norm_le_one, max_self, hfβ, sub_le]
    _ = β * (β * δ) := by simp [prodMap]

variable {n A} {β m : ℝ}

/-- The size conditions of the vanishing criterion for a space of rank `card n` over the field `D.E`
of the data `D`. The exponent `A` dominates the rank, the exponent `N` of a lower bound
`v * β ^ (-N)`, with `v` a volume, for local pairings of matrix coefficients, and the real
dimension; `β` dominates the constants, among them the cusp constant
`cuspConst D.E n D.cyclotomicConductor` and the bound `L` of the parameters; `m` is at least a large
power of `β`; and the generator of the deep level is large against `m` at every infinite place `w`,
with embedding `Φ w`. The radius `m` is a real number, not the number `D.m` of lifts. -/
structure New.Exchange.HasDeepLevelSizes (D : Data P) (n : Type) [Fintype n] (A L N : ℕ)
    (β m : ℝ) : Prop where
  /-- `A` is large against the square of the rank. -/
  rank_sq_lt : 8 * (card n + 1) ^ 2 < A
  /-- `A` exceeds the exponent `N` of the lower bound for the local pairings. -/
  exponent_lt : N < A
  /-- `A` exceeds by `2` or more the real dimension of a space of rank `card n + 1` over `E ⊗ ℝ`. -/
  dim_le : 2 * D.f * (card n + 1) + 2 ≤ A
  /-- `β` bounds the constant of the cusp estimate: `D.M` is the level and `cuspConst` depends on
  the rank and on the number `D.cyclotomicConductor` in the different of `D.E`. -/
  cuspConst_sq_le : D.M * cuspConst D.E n D.cyclotomicConductor ^ 2 ≤ β
  /-- `β` bounds a polynomial in the rank and the bound `L` of the parameters. -/
  rank_pow_le : 2000 * (card n + L + 1) ^ 6 ≤ β
  /-- `β` bounds the number of infinite places. -/
  places_le : D.f ≤ β
  /-- `m` is at least a large power of `β`. -/
  pow_le : β ^ (20 * A * (D.f + 1)) ≤ m
  /-- The level is deep: its generator is large at every infinite place. -/
  pow_le_norm_gridLevelGen : ∀ w : NumberField.InfinitePlace D.E,
    m ^ (3 * card n + 2) ≤ ‖Φ w D.gridLevelGen.val‖

section Sizes
omit [Nonempty n]

section

omit [DecidableEq n]

lemma New.Exchange.HasDeepLevelSizes.sixteen_le
    (h_size : Exchange.HasDeepLevelSizes D n A L N β m) : 16 ≤ β :=
  h_size.rank_pow_le.trans' (mod_cast by lia)

/-- The size conditions for the deep level force the constant `β` to be at most the radius `m`,
which is at least a power of `β`. -/
lemma New.Exchange.HasDeepLevelSizes.beta_le_m (h_size : Exchange.HasDeepLevelSizes D n A L N β m) :
    β ≤ m := by
  have one_le : 1 ≤ β := by linarith [h_size.sixteen_le]
  have hA : N < A := h_size.exponent_lt
  exact (le_self_pow₀ one_le (by lia)).trans h_size.pow_le

/-- The comparison of constants behind `integral_typeKernelMajorant_le`. Of the size conditions for
the deep level it uses `8 (card n + 1)² < A`, `N < A`, `2000 (card n + L + 1)⁶ ≤ β` and
`β ^ (20 A (D.f + 1)) ≤ m`. The left side is the `D.f`-th power of the bound for the local
integrals; it is small against `m`. -/
lemma New.Exchange.HasDeepLevelSizes.pow_places_le_div
    (h_size : Exchange.HasDeepLevelSizes D n A L N β m) :
    (8 * (2000 * (card n + L + 1) ^ 6) ^ (2 * card n ^ 2) * 2 ^ (2 * A)) ^ D.f ≤
      m / (16 * β) / (β ^ N * (2 * β) ^ (3 * A)) ^ D.f := by
  have hA : 8 * (card n + 1) ^ 2 < A := h_size.rank_sq_lt
  have hN : N < A := h_size.exponent_lt
  have hβ₁₆ : 16 ≤ β := h_size.sixteen_le
  have exponent_le : 1 + 2 * card n ^ 2 + 2 * A + (N + 2 * (3 * A)) ≤ 20 * A := by nlinarith
  rw [le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  calc
    _ ≤ (β * β ^ (2 * card n ^ 2) * β ^ (2 * A)) ^ D.f * (β ^ N * (β * β) ^ (3 * A)) ^ D.f *
        (β * β) := by
      gcongr
      exacts [by linarith, h_size.rank_pow_le, by linarith, by linarith]
    _ = β ^ ((1 + 2 * card n ^ 2 + 2 * A + (N + 2 * (3 * A))) * D.f + 2) := by ring
    _ ≤ β ^ (20 * A * (D.f + 1)) :=
      pow_le_pow_right₀ (by linarith) (by linarith [Nat.mul_le_mul_right D.f exponent_le])
    _ ≤ m := h_size.pow_le

end

/-- Under the size conditions `HasDeepLevelSizes`, `D.M * κ²` is at most `β ≤ m`. Here
`κ = cuspConst D.E n D.cyclotomicConductor` is the constant of the cusp estimate
`IsForm.norm_le_of_firstMinimum_lt`. So where `V.firstMinimum` is at least the threshold
`(m⁻² / (D.M κ²)) ^ card n` of that estimate, `m² ≤ m ^ (3 card n + 2) * V.firstMinimum`. -/
lemma New.Exchange.HasDeepLevelSizes.sq_le_pow_mul_firstMinimum
    (h_size : Exchange.HasDeepLevelSizes D n A L N β m)
    (h_large : (m⁻¹ ^ 2 / (D.M * cuspConst D.E n D.cyclotomicConductor ^ 2)) ^ card n ≤
      V.firstMinimum) :
    m ^ 2 ≤ m ^ (3 * card n + 2) * V.firstMinimum := by
  have m_ge : 16 ≤ m := h_size.sixteen_le.trans h_size.beta_le_m
  have const_le : D.M * cuspConst D.E n D.cyclotomicConductor ^ 2 ≤ m :=
    h_size.cuspConst_sq_le.trans h_size.beta_le_m
  have const_pos : 0 < D.M * cuspConst D.E n D.cyclotomicConductor ^ 2 := by
    grw [← one_le_cuspConst]
    simp [NeZero.pos]
  calc m ^ 2
    _ = m ^ (3 * card n + 2) * (m⁻¹ ^ 2 / m) ^ card n := by
      rw [show m⁻¹ ^ 2 / m = (m ^ 3)⁻¹ by field, inv_pow, ← pow_mul, pow_add]
      field
    _ ≤ m ^ (3 * card n + 2) * V.firstMinimum := by grw [← h_large, const_le]

end Sizes

/-- The function `u ↦ ∏_w deg(l w) (2 / ‖u w‖) ^ (2 A)` on the real points, with `deg` the formal
degree. It is a majorant of `‖typeKernel l s‖` that keeps half of its decay when the parameters
`l w` have large gaps for `4 A`. -/
noncomputable def New.Exchange.typeKernelMajorant (l : NumberField.InfinitePlace D.E → HCParam s)
    (A : ℕ) (u : GInf D.E s) : ℝ :=
  ∏ w : NumberField.InfinitePlace D.E, (l w).formalDegree * (2 / ‖(u w).val.val‖) ^ (2 * A)

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let the parameters `l w` have large gaps for `4 A` and entries bounded by `L`. Then
`typeKernelMajorant l A`, the product over the infinite places `w` of the formal degree of `l w`
times `(2 / ‖u w‖) ^ (2 A)`, is integrable over the real points `u`. Under the size conditions for
the deep level, where `β` dominates the constants, `β ^ N` is the loss in the local pairings and
`m` is at least a large power of `β`, its integral is at most
`m / (16 β) / (β ^ N (2 β) ^ (3 A)) ^ D.f`, with `D.f` the number of infinite places. -/
lemma New.Exchange.integral_typeKernelMajorant_le {l : NumberField.InfinitePlace D.E → HCParam s}
    (h_size : HasDeepLevelSizes D n A L N β m)
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (hl : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L) :
    Integrable (typeKernelMajorant l A) ∧
    ∫ u : GInf D.E s, typeKernelMajorant l A u ≤
      m / (16 * β) / (β ^ N * (2 * β) ^ (3 * A)) ^ D.f := by
  have hA : 8 * (card n + 1) ^ 2 < A := h_size.rank_sq_lt
  let factor (w : NumberField.InfinitePlace D.E) (g : USign s) : ℝ :=
    (l w).formalDegree * (2 / ‖(g : Matrix n n ℂ)‖) ^ (2 * A)
  let C : ℝ := 8 * (2000 * (card n + L + 1) ^ 6) ^ (2 * card n ^ 2) * 2 ^ (2 * A)
  have tail (w : NumberField.InfinitePlace D.E) :
      Integrable (factor w) ∧ ∫ g : USign s, factor w g ≤ C :=
    integral_tail_le (hg := h_gap w) (hl w) (2 * A) (by lia)
  refine ⟨.fintype_prod fun w ↦ (tail w).left, ?_⟩
  calc ∫ u : GInf D.E s, ∏ w, factor w (u w)
    _ = ∏ w, ∫ g : USign s, factor w g := integral_fintype_prod_volume_eq_prod factor
    _ ≤ C ^ D.f := (prod_le_prod₀ (fun w _ ↦ by positivity [formalDegree_pos (h_gap w)])
      fun w _ ↦ (tail w).right).trans_eq (by rw [prod_const, card_univ])
    _ ≤ m / (16 * β) / (β ^ N * (2 * β) ^ (3 * A)) ^ D.f := h_size.pow_places_le_div

/-- The kernel `typeKernel l s` varies slowly. Let the parameters `l w` have large gaps for `4 A`
and entries bounded by `L`, and assume the size conditions `HasDeepLevelSizes D n A L N β m`: `β`
dominates the constants and `m` is at least a large power of `β`. For a real point `u` within
`m⁻¹ ^ 2` of `1`, the values of the kernel at `u⁻¹ * z` and `z` differ by at most `β / m` times the
sum of the values at these points of `typeKernelMajorant l A`, the function
`u ↦ ∏ w, deg(l w) (2 / ‖u w‖) ^ (2 A)` with `deg` the formal degree. -/
lemma New.Exchange.norm_typeKernel_inv_mul_sub_le {l : NumberField.InfinitePlace D.E → HCParam s}
    (h_size : HasDeepLevelSizes D n A L N β m)
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (hl : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L)
    {u : GInf D.E s} (hu : dist u 1 ≤ m⁻¹ ^ 2) (z : GInf D.E s) :
    ‖typeKernel l s (u⁻¹ * z) - typeKernel l s z‖ ≤
      (typeKernelMajorant l A (u⁻¹ * z) + typeKernelMajorant l A z) * (β / m) := by
  have hβ₁₆ : 16 ≤ β := h_size.sixteen_le
  have m_ge : 16 ≤ m := hβ₁₆.trans h_size.beta_le_m
  let deg : ℝ := ∏ w, (l w).formalDegree
  let ψ (g : GInf D.E s) : ℂ := ∏ w, conj ((l w).dsCoeff (g w))
  let decay (g : GInf D.E s) : ℝ := ∏ w, (2 / ‖(g w : Matrix n n ℂ)‖) ^ (2 * A)
  have deg_pos : 0 < deg := prod_pos fun w _ ↦ formalDegree_pos (h_gap w)
  have kernel_eq (g : GInf D.E s) : typeKernel l s g = deg * ψ g := by
    simp [typeKernel, dsKernel, deg, ψ, prod_mul_distrib]
  have majorant_eq (g : GInf D.E s) : typeKernelMajorant l A g = deg * decay g := prod_mul_distrib
  have ψ_le (g : GInf D.E s) : ‖ψ g‖ ≤ decay g ^ 2 :=
    calc ‖ψ g‖
      _ = ∏ w, ‖(l w).dsCoeff (g w)‖ := by simp only [ψ, norm_prod, RCLike.norm_conj]
      _ ≤ ∏ w, (2 / ‖(g w : Matrix n n ℂ)‖) ^ (4 * A) := by
        gcongr with w
        exact norm_dsCoeff_le_pow (h_gap w) le_add_self (g w)
      _ = decay g ^ 2 := by simp only [decay, ← prod_pow, ← pow_mul]; ring_nf
  have lipschitz : ‖ψ (u⁻¹ * z) - ψ z‖ ≤ β * (β * m⁻¹ ^ 2) :=
    norm_prod_conj_dsCoeff_inv_mul_sub_le n A h_gap hl h_size.rank_pow_le h_size.places_le hu z
  have ψ_sub_le : ‖ψ (u⁻¹ * z) - ψ z‖ ≤ (decay (u⁻¹ * z) + decay z) * (β / m) := by
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    calc ‖ψ (u⁻¹ * z) - ψ z‖ ^ 2
      _ ≤ β * (β * m⁻¹ ^ 2) * (decay (u⁻¹ * z) ^ 2 + decay z ^ 2) := by
        rw [sq ‖_‖]
        nth_grw 1 [lipschitz, norm_sub_le, ψ_le, ψ_le]
      _ ≤ β * (β * m⁻¹ ^ 2) * (decay (u⁻¹ * z) + decay z) ^ 2 := by
        gcongr
        exact pow_add_pow_le (by positivity) (by positivity) two_ne_zero
      _ = ((decay (u⁻¹ * z) + decay z) * (β / m)) ^ 2 := by ring
  calc ‖typeKernel l s (u⁻¹ * z) - typeKernel l s z‖
    _ = deg * ‖ψ (u⁻¹ * z) - ψ z‖ := by
      rw [kernel_eq, kernel_eq, ← mul_sub, norm_mul, Complex.norm_of_nonneg deg_pos.le]
    _ ≤ deg * ((decay (u⁻¹ * z) + decay z) * (β / m)) := by gcongr
    _ = _ := by rw [majorant_eq, majorant_eq, ← mul_add, mul_assoc]

/-- High in a cusp a form is at most half of its bound. Assume the size conditions
`HasDeepLevelSizes D n A L N β m`, and let the parameters `l w` have large gaps for `4 A` and
entries bounded by `L`. Let `y` be a form on `V` of type `l`, right invariant under the principal
congruence subgroup of level `D.M` (`HasLevel`) and bounded by `S`. Where the first minimum of the
lattice of `V.move x` is below the threshold of the cusp estimate, whose constant is
`cuspConst D.E n D.cyclotomicConductor`, we have `‖y x‖ ≤ S / 2`. -/
lemma New.Exchange.norm_le_half_of_firstMinimum_lt {l : NumberField.InfinitePlace D.E → HCParam s}
    (h_size : HasDeepLevelSizes D n A L N β m)
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (hl : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L)
    {y : G D.E s → ℂ} (hy : V.IsForm (typeKernel l s) y)
    (hy_level : HasLevel y (principalLevel n D.M))
    {S : ℝ} (hS : ∀ g : G D.E s, ‖y g‖ ≤ S) {x : G D.E s}
    (h_small : (V.move x).firstMinimum <
      (m⁻¹ ^ 2 / (D.M * cuspConst D.E n D.cyclotomicConductor ^ 2)) ^ card n) :
    ‖y x‖ ≤ S / 2 := by
  -- By cuspidality (`IsForm.norm_le_of_firstMinimum_lt`) it is enough to bound
  -- `‖y (x * (u, 1)) - y x‖` by `S / 2` for real points `u` within `m⁻¹ ^ 2` of `1`.
  have hβ₁₆ : 16 ≤ β := h_size.sixteen_le
  have m_ge : 16 ≤ m := hβ₁₆.trans h_size.beta_le_m
  have S_nonneg : 0 ≤ S := (norm_nonneg (y x)).trans (hS x)
  have cusp : IsCuspKernel (4 * A) (typeKernel l s) := isCuspKernel_typeKernel h_gap
  let major : GInf D.E s → ℝ := typeKernelMajorant l A
  obtain ⟨major_int, integral_major⟩ := integral_typeKernelMajorant_le h_size h_gap hl
  have integral_le : ∫ u, major u ≤ m / (16 * β) :=
    integral_major.trans (div_le_self (by positivity) (by bound))
  refine hy.norm_le_of_firstMinimum_lt cusp P.conductor_mem_differentIdeal NeZero.out hy_level
    (δ := m⁻¹ ^ 2) (by positivity) (by bound) h_small fun u hu ↦ ?_
  have integrand_le (z : GInf D.E s) :
      ‖typeKernel l s (u⁻¹ * z) * y (x * (u, 1) * (u⁻¹ * z, 1)) -
        typeKernel l s z * y (x * (z, 1))‖ ≤ (major (u⁻¹ * z) + major z) * (β / m) * S := by
    rw [show x * (u, 1) * (u⁻¹ * z, 1) = x * (z, 1) by simp [mul_assoc], ← sub_mul]
    exact norm_mul_le_of_le (norm_typeKernel_inv_mul_sub_le h_size h_gap hl hu z) (hS _)
  -- Write both values of `y` as convolutions with its kernel, and integrate.
  have conv_int (g : G D.E s) : Integrable fun z ↦ typeKernel l s z * y (g * (z, 1)) :=
    hy.isBoundedMeasurable.integrable_mul_comp cusp.integrable _
  have shift_int : Integrable fun z ↦ major (u⁻¹ * z) := major_int.comp_mul_left u⁻¹
  calc ‖y (x * (u, 1)) - y x‖
    _ = ‖∫ z, typeKernel l s (u⁻¹ * z) * y (x * (u, 1) * (u⁻¹ * z, 1)) -
        typeKernel l s z * y (x * (z, 1))‖ := by
      nth_rw 1 2 [← hy.realConv_eq cusp.integrable]
      rw [realConv, realConv, ← integral_mul_left_eq_self _ u⁻¹,
        ← integral_sub ((conv_int _).comp_mul_left _) (conv_int _)]
    _ ≤ ∫ z, (major (u⁻¹ * z) + major z) * (β / m) * S :=
      norm_integral_le_of_norm_le (((shift_int.add major_int).mul_const _).mul_const _)
        (.of_forall integrand_le)
    _ = 2 * (∫ z, major z) * (β / m) * S := by
      rw [integral_mul_const, integral_mul_const, integral_add shift_int major_int,
        integral_mul_left_eq_self major, two_mul]
    _ ≤ 2 * (m / (16 * β)) * (β / m) * S := by gcongr
    _ = S / 8 := by field
    _ ≤ S / 2 := by linarith

omit [Nonempty n] in
/-- Let `y` be a function on the group of `V` whose Petersson product with `x ↦ φ ((x ⊕ 1) ω)` is
zero for all forms `φ` on `Z = V ⊕ ⟨1⟩` of type `l'` and level `K`, where the parameters `l' w` have
large gaps for `2 A` and `8 (card n + 1)² < A`. Fix a real point `α` and put `c g = ∏ w, conj ((l'
w).dsCoeff ((α w)⁻¹ * g w * ω w))`, the translated coefficient for `l'`. Then the Poincaré series
over the rational points `γ` of `Z` of `c` times the indicator of `K` at the finite part
(`poincareKernel`), centred at `x ⊕ 1`, has zero period against `y` over the quotient of the group
of `V` by its rational points (`quotMeasure`). -/
lemma New.Exchange.poincare_period_translatedCoeff_eq_zero
    {l' : NumberField.InfinitePlace D.E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (hA : 8 * (card n + 1) ^ 2 < A)
    (h_gap' : ∀ w : NumberField.InfinitePlace D.E, (l' w).HasLargeGap (2 * A))
    {ω : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))} {y : G D.E s → ℂ}
    {K : Subgroup (Gf D.E (n ⊕ Unit))} [IsLevel K]
    (h_orth : ∀ φ ∈ levelSpace
        ((V.sum (signedSpace D.E (1 : Unit → ℤˣ))).formRep (typeKernel l' (s ⊕ᵥ 1))) K,
      V.petersson y (fun x : G D.E s ↦ φ (G.sum (x, 1) * (ω, 1))) = 0)
    (x : G D.E s) (α : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))) :
    ∫ h : G D.E s, ∑' γ : (V.sum (signedSpace D.E (1 : Unit → ℤˣ))).Γ,
      poincareKernel (translatedCoeff l' α ω) K
        ((G.inlLine D.E s x)⁻¹ * γ * G.inlLine D.E s h) * y h ∂V.quotMeasure = 0 := by
  -- The Poincaré series is, up to the nonzero formal degrees, the conjugate of the value at
  -- `G.sum (h, 1) * (ω, 1)` of a form `Q` of type `l'` and level `K` on `Z`; the series converges
  -- to a form by the decay of the coefficient.
  let Z : Space D.E (n ⊕ Unit) (s ⊕ᵥ 1) := V.sum (signedSpace D.E 1)
  let term (γ : Z.Γ) (h : G D.E s) : ℂ :=
    poincareKernel (translatedCoeff l' α ω) K ((G.inlLine D.E s x)⁻¹ * γ.val * G.inlLine D.E s h)
  let deg : ℂ := ∏ w, (l' w).formalDegree
  have deg_ne : deg ≠ 0 := by simp [deg, prod_ne_zero_iff, (formalDegree_pos (h_gap' _)).ne']
  have h_order : 8 * card (n ⊕ Unit) ^ 2 < 2 * A := by grind [card_sum, card_unit]
  let centreInv : G D.E (s ⊕ᵥ 1) := (G.sum (x, 1) * (α, 1))⁻¹
  obtain ⟨Q, hQ⟩ : ∃ Q : levelSpace (Z.formRep (typeKernel l' (s ⊕ᵥ 1))) K,
      ∀ g : G D.E (s ⊕ᵥ 1), conj (Q.val g) = ∑' γ : Z.Γ,
        typeKernel l' (s ⊕ᵥ 1) (centreInv * γ * g).1 * Set.indicator K 1 (centreInv * γ * g).2 :=
    Z.exists_kernel_form h_order (isCuspKernel_typeKernel h_gap') centreInv K
  have conj_Q (h : G D.E s) :
      conj (Q.val (G.sum (h, 1) * (ω, 1))) = deg * ∑' γ : Z.Γ, term γ h := by
    rw [hQ, ← tsum_mul_left]
    congr! 2 with γ
    simp [term, deg, centreInv, poincareKernel, G.inlLine, translatedCoeff, typeKernel, dsKernel,
      prod_mul_distrib, mul_assoc]
  refine (mul_eq_zero_iff_left deg_ne).1 ?_
  calc deg * ∫ h : G D.E s, ∑' γ : Z.Γ, term γ h * y h ∂V.quotMeasure
    _ = V.petersson (fun h : G D.E s ↦ Q.val (G.sum (h, 1) * (ω, 1))) y := by
      simp_rw [petersson, conj_Q, tsum_mul_right, ← integral_const_mul, mul_assoc]
    _ = 0 := by rw [← conj_petersson, h_orth Q.val Q.prop, map_zero]

omit [Nonempty n] in
/-- Assume the size conditions `HasDeepLevelSizes D n A L N β m` and large gaps for `2 A` of the
parameters `l' w`. Let `y` be automorphic on `V`, of the deep level
`principalLevel n D.gridLevelGen`, and bounded by `S`. Let it also be orthogonal to
`x ↦ φ ((x ⊕ 1) ω)` for all forms `φ` on `V ⊕ ⟨1⟩` of type `l'` and deep level. For a real point
`α`, the translated coefficient `translatedCoeff l' α ω g` is
`∏ w, conj ((l' w).dsCoeff ((α w)⁻¹ * g w * ω w))`. Where
`m² ≤ m ^ (3 card n + 2) * (V.move x).firstMinimum`, its restriction along the block embedding
`inl s 1` is integrable. The convolution of this restriction with `y` at `x` is then at most
`10 S / m` times `sliceConst A α ω = ∏ w, (2 (‖α w‖ ‖ω w‖)²) ^ A * 16 ^ A * v`, with `v` the volume
of the unit ball around `1` in `U(s)`. -/
lemma New.Exchange.norm_realConv_translatedCoeff_le
    {l' : NumberField.InfinitePlace D.E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (h_size : HasDeepLevelSizes D n A L N β m)
    (h_gap' : ∀ w : NumberField.InfinitePlace D.E, (l' w).HasLargeGap (2 * A))
    {ω : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))} {y : G D.E s → ℂ} (hy : V.IsAutomorphic y)
    (hy_level : HasLevel y (principalLevel n D.gridLevelGen))
    (h_orth : ∀ φ ∈ levelSpace
        ((V.sum (signedSpace D.E (1 : Unit → ℤˣ))).formRep (typeKernel l' (s ⊕ᵥ 1)))
        (principalLevel (n ⊕ Unit) D.gridLevelGen),
      V.petersson y (fun x : G D.E s ↦ φ (G.sum (x, 1) * (ω, 1))) = 0)
    {S : ℝ} (hS : ∀ g : G D.E s, ‖y g‖ ≤ S) {x : G D.E s}
    (h_large : m ^ 2 ≤ m ^ (3 * card n + 2) * (V.move x).firstMinimum)
    (α : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))) :
    Integrable (fun r : GInf D.E s ↦ translatedCoeff l' α ω (inl s 1 ∘ r)) ∧
    ‖realConv (fun r : GInf D.E s ↦ translatedCoeff l' α ω (inl s 1 ∘ r)) y x‖ ≤
      sliceConst A α ω * S * (10 / m) := by
  -- The period of the Poincaré series of the coefficient against `y` is `0` by `h_orth`, so its
  -- identity term is as small as the error in `norm_poincare_period_sub_le`.
  have m_ge : 16 ≤ m := h_size.sixteen_le.trans h_size.beta_le_m
  let vol : ℝ := volume.real (principalLevel n D.gridLevelGen : Set (Gf D.E n))
  let slice (r : GInf D.E s) : ℂ := translatedCoeff l' α ω (inl s 1 ∘ r)
  have key : Integrable slice ∧
      ‖0 - vol • realConv slice y x‖ ≤ vol * sliceConst A α ω * S * (10 / m) := by
    rw [← poincare_period_translatedCoeff_eq_zero h_size.rank_sq_lt h_gap' h_orth x α]
    exact norm_poincare_period_sub_le hy hS Fact.out hy_level h_size.pow_le_norm_gridLevelGen
      h_size.dim_le
      h_size.rank_sq_lt h_gap' (by positivity) x h_large (h_size.places_le.trans h_size.beta_le_m)
      (by linarith) ω α
  -- The positive volume `vol` of the level cancels.
  simpa [vol, measureReal_pos_of_isLevel, abs_of_pos, mul_assoc] using key

/-- Let the parameter `l` have large gaps for `4 * A` (`HasLargeGap`), let `16 ≤ β` and
`‖ω‖ ^ 2 ≤ β`. Then the norm of the kernel `dsKernel l r`, times
`(2 (‖inl s 1 r * ω‖ ‖ω‖)²) ^ A * 16 ^ A`, is at most
`l.formalDegree * (2 / ‖r‖) ^ (2 A) * (2 β) ^ (3 A)`. Here `inl s 1 r = diag(r, 1)`. -/
lemma New.Exchange.norm_dsKernel_mul_pow_le {l : HCParam s} (h_gap : l.HasLargeGap (4 * A))
    (hβ : 16 ≤ β) {ω : USign (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (hω : ‖(ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β) (r : USign s) :
    ‖dsKernel l r‖ *
      ((2 * (‖((inl s 1 r * ω : USign (s ⊕ᵥ 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ *
        ‖(ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖) ^ 2) ^ A * 16 ^ A) ≤
      l.formalDegree * (2 / ‖(r : Matrix n n ℂ)‖) ^ (2 * A) * (2 * β) ^ (3 * A) := by
  set ρ : ℝ := ‖(r : Matrix n n ℂ)‖
  set σ : ℝ := ‖(ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖
  have ρ_pos : 0 < ρ := one_pos.trans_le (one_le_norm r)
  have hdeg : 0 < l.formalDegree := formalDegree_pos h_gap
  have kernel_le : ‖dsKernel l r‖ ≤ l.formalDegree * (2 / ρ) ^ (4 * A) := by
    grw [← norm_dsCoeff_le_pow h_gap le_add_self r]
    simp [dsKernel, abs_of_pos hdeg]
  have norm_le :
      ‖((inl s 1 r * ω : USign (s ⊕ᵥ 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ≤ ρ * σ :=
    (norm_mul_le _ _).trans_eq (by simp [ρ, σ, one_le_norm])
  calc
    _ ≤ l.formalDegree * (2 / ρ) ^ (4 * A) * ((2 * (ρ * β) ^ 2) ^ A * β ^ A) := by
      grw [kernel_le, norm_le, mul_assoc ρ, ← sq, hω, hβ]
    _ = l.formalDegree * (2 / ρ) ^ (2 * A) * (2 * β) ^ (3 * A) := by
      simp only [pow_mul, mul_assoc, ← mul_pow]
      congr 2
      field

/-- Let the parameters `l w` have large gaps for `4 A`, so that their formal degrees are positive,
and let `ω` be a real point, with a component `ω w` in `U(s ⊕ᵥ 1)` at each infinite place `w`. Pair
the conjugate of the kernel `typeKernel l s`, divided by the value of the kernel at `1`, with the
restriction along `inl s 1 : r ↦ r ⊕ 1` of
`translatedCoeff l' ω ω g = ∏ w, conj ((l' w).dsCoeff ((ω w)⁻¹ * g w * ω w))`. This integral over
the real points is the product over `w` of the local pairings of the matrix coefficients. -/
lemma New.Exchange.integral_translatedCoeff_mul_eq_prod
    {l : NumberField.InfinitePlace D.E → HCParam s}
    {l' : NumberField.InfinitePlace D.E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (ω : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))) :
    ∫ z : GInf D.E s,
        translatedCoeff l' ω ω (inl s 1 ∘ z) * (conj (typeKernel l s z) / typeKernel l s 1) =
      ∏ w : NumberField.InfinitePlace D.E, ∫ r : USign s, (l w).dsCoeff r *
        conj ((l' w).dsCoeff ((ω w)⁻¹ * inl s 1 r * ω w : USign (s ⊕ᵥ 1))) := by
  rw [← integral_fintype_prod_volume_eq_prod]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  -- The formal degrees in `dsKernel` are positive and cancel in the quotient.
  simp [translatedCoeff, field, typeKernel, dsKernel, prod_mul_distrib, prod_eq_zero_iff, ne_of_gt,
    formalDegree_pos (h_gap _)]

omit [Nonempty n] in
/-- Right translation of the point by the real point `u` moves `u ⊕ 1` into the left argument of
the translated coefficient. -/
lemma New.Exchange.realConv_translatedCoeff_mul
    (l' : NumberField.InfinitePlace D.E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ)))
    (α ω : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))) (y : G D.E s → ℂ) (x : G D.E s) (u : GInf D.E s) :
    realConv (fun r : GInf D.E s ↦ translatedCoeff l' α ω (inl s 1 ∘ r)) y (x * (u, 1)) =
      realConv (fun r : GInf D.E s ↦ translatedCoeff l' (inl s 1 ∘ u * α) ω (inl s 1 ∘ r)) y x := by
  rw [realConv, realConv, ← integral_mul_left_eq_self (fun z ↦ _ * y (x * (z, 1))) u]
  -- The products stay in the group, where `(inl u)⁻¹ * inl u` cancels.
  simp [translatedCoeff, mul_assoc, -Subgroup.coe_mul, -MulMemClass.coe_mul]

/-- Let `y` be a form on `V` of type `l` and of the deep level `D.gridLevelGen`, bounded by `S` and
orthogonal to `x ↦ φ ((x ⊕ 1) ω)` for all forms `φ` on `V ⊕ ⟨1⟩` of type `l'` and deep level. Assume
the size conditions for the deep level, large gaps of the parameters, bounded entries of `l`, that
`ω` is not large (`hω`) and that the local pairings of the coefficients for `l` and `l'` are bounded
from below (`h_pair`). Where the first minimum of `V.move x` is at least the threshold of the cusp
estimate, whose constant `cuspConst D.E n D.cyclotomicConductor` depends on the rank and on a number
in the different of `D.E`, we have `‖y x‖ ≤ S / 2`. -/
lemma New.Exchange.norm_le_half_of_le_firstMinimum {l : NumberField.InfinitePlace D.E → HCParam s}
    {l' : NumberField.InfinitePlace D.E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (h_size : HasDeepLevelSizes D n A L N β m)
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (h_gap' : ∀ w : NumberField.InfinitePlace D.E, (l' w).HasLargeGap (2 * A))
    (hl : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L)
    {ω : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (hω : ∀ w : NumberField.InfinitePlace D.E,
      ‖(ω w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β)
    (h_pair : ∀ w : NumberField.InfinitePlace D.E,
      volume.real {r : USign s | ‖(r : Matrix n n ℂ) - 1‖ ≤ 1} ≤ β ^ N *
        ‖∫ r : USign s, (l w).dsCoeff r *
          conj ((l' w).dsCoeff ((ω w)⁻¹ * inl s 1 r * ω w : USign (s ⊕ᵥ 1)))‖)
    {y : G D.E s → ℂ} (hy : V.IsForm (typeKernel l s) y)
    (hy_level : HasLevel y (principalLevel n D.gridLevelGen))
    (h_orth : ∀ φ ∈ levelSpace
        ((V.sum (signedSpace D.E (1 : Unit → ℤˣ))).formRep (typeKernel l' (s ⊕ᵥ 1)))
        (principalLevel (n ⊕ Unit) D.gridLevelGen),
      V.petersson y (fun x : G D.E s ↦ φ (G.sum (x, 1) * (ω, 1))) = 0)
    {S : ℝ} (hS : ∀ g : G D.E s, ‖y g‖ ≤ S) {x : G D.E s}
    (h_large : (m⁻¹ ^ 2 / (D.M * cuspConst D.E n D.cyclotomicConductor ^ 2)) ^ card n ≤
      (V.move x).firstMinimum) :
    ‖y x‖ ≤ S / 2 := by
  -- Average the small convolution of `norm_realConv_translatedCoeff_le` over the kernel of `y`.
  -- The result is `η * y x`, where `η` is the product of the local pairings of `h_pair`.
  set v : ℝ := volume.real {r : USign s | ‖(r : Matrix n n ℂ) - 1‖ ≤ 1}
  have hβ₁₆ : 16 ≤ β := h_size.sixteen_le
  have m_ge : 16 ≤ m := hβ₁₆.trans h_size.beta_le_m
  have S_nonneg : 0 ≤ S := (norm_nonneg (y x)).trans (hS x)
  have v_pos : 0 < v := ENNReal.toReal_pos (measure_sublevel_ne_zero volume (by simp))
    (measure_ball_ne_top_of_isProperMap volume .monoidHom_id 1)
  have cusp : IsCuspKernel (4 * A) (typeKernel l s) := isCuspKernel_typeKernel h_gap
  obtain ⟨major_int, integral_major⟩ := integral_typeKernelMajorant_le h_size h_gap hl
  let ψ (α : GInf D.E (s ⊕ᵥ 1)) (r : GInf D.E s) : ℂ := translatedCoeff l' α ω (inl s 1 ∘ r)
  let growth (α : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))) (w : NumberField.InfinitePlace D.E) : ℝ :=
    (2 * (‖(α w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ *
      ‖(ω w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖) ^ 2) ^ A
  have conv_bound (α : GInf D.E (s ⊕ᵥ 1)) : Integrable (ψ α) ∧
      ‖realConv (ψ α) y x‖ ≤ (∏ w, growth α w * (16 ^ A * v)) * S * (10 / m) :=
    norm_realConv_translatedCoeff_le h_size h_gap' hy.toIsAutomorphic hy_level h_orth hS
      (h_size.sq_le_pow_mul_firstMinimum h_large) α
  -- Fubini, then the rank one formula `realConv_translate`.
  let η : ℂ := ∫ z, ψ ω z * (conj (typeKernel l s z) / typeKernel l s 1)
  have average : ∫ u, typeKernel l s u * realConv (ψ ω) y (x * (u, 1)) = η * y x := by
    rw [integral_mul_realConv hy.isBoundedMeasurable (conv_bound ω).1 cusp.integrable _]
    simp_rw [hy.realConv_translate cusp, ← mul_assoc, integral_mul_const, η]
  have η_ge : (v / β ^ N) ^ D.f ≤ ‖η‖ := by
    simp only [η, ψ, integral_translatedCoeff_mul_eq_prod h_gap, norm_prod]
    grw [← fun w ↦ (div_le_iff₀' (by bound)).2 (h_pair w)]
    simp [div_pow]
  have integrand_le (u : GInf D.E s) : ‖typeKernel l s u * realConv (ψ ω) y (x * (u, 1))‖ ≤
      typeKernelMajorant l A u * (((2 * β) ^ (3 * A) * v) ^ D.f * S * 10 / m) := by
    calc ‖typeKernel l s u * realConv (ψ ω) y (x * (u, 1))‖
      _ ≤ (∏ w, ‖dsKernel (l w) (u w)‖ * (growth (inl s 1 ∘ u * ω) w * 16 ^ A) * v) *
          (S * (10 / m)) := by
        grw [norm_mul, realConv_translatedCoeff_mul, (conv_bound (inl s 1 ∘ u * ω)).2]
        simp [typeKernel, prod_mul_distrib, mul_assoc]
      _ ≤ (∏ w, (l w).formalDegree * (2 / ‖(u w : Matrix n n ℂ)‖) ^ (2 * A) *
          (2 * β) ^ (3 * A) * v) * (S * (10 / m)) := by
        gcongr (∏ w, ?_ * _) * _ with w
        exact norm_dsKernel_mul_pow_le (h_gap w) hβ₁₆ (hω w) (u w)
      _ = typeKernelMajorant l A u * (((2 * β) ^ (3 * A) * v) ^ D.f * S * 10 / m) := by
        simp only [typeKernelMajorant, prod_mul_distrib, prod_const, card_univ]
        ring
  -- Integrate: the constants of `η_ge`, `integrand_le` and `integral_major` cancel.
  have average_le : (v / β ^ N) ^ D.f * ‖y x‖ ≤
      m / (16 * β) / (β ^ N * (2 * β) ^ (3 * A)) ^ D.f *
        (((2 * β) ^ (3 * A) * v) ^ D.f * S * 10 / m) := by
    grw [η_ge, ← norm_mul, ← average, ← integral_major, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (major_int.mul_const _) (.of_forall integrand_le)
  have norm_le : ‖y x‖ * 16 * β ≤ S * 10 := by simpa [field, mul_pow, div_pow] using average_le
  grw [← hβ₁₆] at norm_le
  linarith

/-- The vanishing criterion at a real point `ω` of `GInf D.E (s ⊕ᵥ 1)`. Assume the following. First,
the size conditions `HasDeepLevelSizes D n A L N β m`. Second, large gaps of the parameters: entries
of `l w / 2` with different signs differ by at least `500 n³ + 4 A`, and likewise for `l'` with
`n + 1` and `2 A`. Third, entries of `l` bounded by `L`. Fourth, `ω` is not large (`hω`). Fifth, at
each infinite place the coefficient for `l` pairs nontrivially with the restriction of the
coefficient for `l'` conjugated by `ω`, with the explicit lower bound `h_pair`. Then a form `y` on
`V` of type `l` and level `D.chosenLevel` vanishes if it is orthogonal to `x ↦ φ ((x ⊕ 1) ω)` for
every form `φ` on `V ⊕ ⟨1⟩` of type `l'` and of the deep level
`principalLevel (n ⊕ Unit) D.gridLevelGen`. -/
theorem New.Exchange.eq_zero_of_petersson_translate_eq_zero
    {l : NumberField.InfinitePlace D.E → HCParam s}
    {l' : NumberField.InfinitePlace D.E → HCParam (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (h_size : HasDeepLevelSizes D n A L N β m)
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (h_gap' : ∀ w : NumberField.InfinitePlace D.E, (l' w).HasLargeGap (2 * A))
    (hl : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L)
    {ω : GInf D.E (s ⊕ᵥ (1 : Unit → ℤˣ))}
    (hω : ∀ w : NumberField.InfinitePlace D.E,
      ‖(ω w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β)
    (h_pair : ∀ w : NumberField.InfinitePlace D.E,
      volume.real {r : USign s | ‖(r : Matrix n n ℂ) - 1‖ ≤ 1} ≤ β ^ N *
        ‖∫ r : USign s, (l w).dsCoeff r *
          conj ((l' w).dsCoeff ((ω w)⁻¹ * inl s 1 r * ω w : USign (s ⊕ᵥ 1)))‖)
    {y : G D.E s → ℂ} (hy : V.IsForm (typeKernel l s) y) (hy_level : HasLevel y D.chosenLevel)
    (h_orth : ∀ φ ∈ levelSpace
        ((V.sum (signedSpace D.E (1 : Unit → ℤˣ))).formRep (typeKernel l' (s ⊕ᵥ 1)))
        (principalLevel (n ⊕ Unit) D.gridLevelGen),
      V.petersson y (fun x : G D.E s ↦ φ (G.sum (x, 1) * (ω, 1))) = 0) :
    y = 0 := by
  -- By `le_of_halving` it is enough to halve every bound `S` of `‖y‖`.
  -- Where `(V.move x).firstMinimum` is large this follows from the orthogonality, by unfolding a
  -- Poincaré series; where it is small, from cuspidality and the fact that `y` varies slowly.
  have level (a : NumberField.RingOfIntegers D.E) (ha : D.piM ∣ a) :
      HasLevel y (principalLevel n a) :=
    fun k hk ↦ hy_level k (D.principalLevel_le_chosenLevel ha hk)
  have half (S : ℝ) (hS : ∀ g : G D.E s, ‖y g‖ ≤ S) (x : G D.E s) : ‖y x‖ ≤ S / 2 := by
    obtain h_large | h_small := le_or_gt
      ((m⁻¹ ^ 2 / (D.M * cuspConst D.E n D.cyclotomicConductor ^ 2)) ^ card n)
      (V.move x).firstMinimum
    · exact norm_le_half_of_le_firstMinimum h_size h_gap h_gap' hl hω h_pair hy
        (level D.gridLevelGen D.piM_dvd_gridLevelGen) h_orth hS h_large
    · exact norm_le_half_of_firstMinimum_lt h_size h_gap hl hy
        (level D.M (Dvd.intro _ D.piM_mul_star)) hS h_small
  obtain ⟨C, hC⟩ := hy.bounded
  exact funext fun x ↦
    norm_le_zero_iff.1 (le_of_halving hC le_rfl (fun S _ hS x ↦ .inl (half S hS x)) x)

variable (n A β) in
/-- Let `l` be the parameters of the forms on `V` and `l'` those of the forms on `V ⊕ ⟨1⟩`, whose
signs `t` are `s ⊕ᵥ 1`. Assume large gaps for `4 A` of `l w` and for `2 A` of `l' w`, `|l w i| ≤ L`,
the size conditions of `HasDeepLevelSizes`, and that at each infinite place some point `ω` with
`‖ω‖ ^ 2 ≤ β` makes the pairing for `l` and `l'` not small (`h_place`). Then there is a real point
`g` such that a form `y` on `V` of type `l` and level `D.chosenLevel` vanishes if it is orthogonal
to `x ↦ φ ((x ⊕ 1) g)` for all forms `φ` on `V ⊕ ⟨1⟩` of type `l'` and of the deep level
`D.gridLevelGen`. -/
lemma New.Exchange.exists_forall_eq_zero_of_petersson_restrict_eq_zero {t : n ⊕ Unit → ℤˣ}
    {l : NumberField.InfinitePlace D.E → HCParam s}
    {l' : NumberField.InfinitePlace D.E → HCParam t} {h_signs : s ⊕ᵥ 1 = t}
    (h_gap : ∀ w : NumberField.InfinitePlace D.E, (l w).HasLargeGap (4 * A))
    (h_gap' : ∀ w : NumberField.InfinitePlace D.E, (l' w).HasLargeGap (2 * A))
    (h_entry : ∀ (w : NumberField.InfinitePlace D.E) (i : n), |l w i| ≤ L)
    (h_rank : 8 * (card n + 1) ^ 2 < A) (h_exponent : N < A)
    (h_dim : 2 * D.f * (card n + 1) + 2 ≤ A)
    (h_cusp : D.M * cuspConst D.E n D.cyclotomicConductor ^ 2 ≤ β)
    (h_rank_pow : 2000 * (card n + L + 1) ^ 6 ≤ β) (h_places : D.f ≤ β)
    (h_pow_le : β ^ (20 * A * (D.f + 1)) ≤ m)
    (h_level : ∀ w : NumberField.InfinitePlace D.E,
      m ^ (3 * card n + 2) ≤ ‖Φ w D.gridLevelGen.val‖)
    (h_place : ∀ w : NumberField.InfinitePlace D.E, ∃ ω : USign (s ⊕ᵥ (1 : Unit → ℤˣ)),
      ‖(ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β ∧
      volume.real {r : USign s | ‖(r : Matrix n n ℂ) - 1‖ ≤ 1} ≤ β ^ N *
        ‖∫ r : USign s, (l w).dsCoeff r *
          conj ((toHCParam (s ⊕ᵥ 1) (l' w)).dsCoeff
            (ω⁻¹ * inl s 1 r * ω : USign (s ⊕ᵥ (1 : Unit → ℤˣ))))‖) :
    ∃ g : GInf D.E t, ∀ y ∈ levelSpace (V.formRep (typeKernel l s)) D.chosenLevel,
      (∀ φ ∈ levelSpace
          (((V.sum (signedSpace D.E 1)).reindex (.refl (n ⊕ Unit)) h_signs).formRep
            (typeKernel l' t))
          (principalLevel (n ⊕ Unit) D.gridLevelGen),
        V.petersson y
          (fun x : G D.E s ↦ φ (G.reindex (.refl (n ⊕ Unit)) h_signs (.sum (x, 1)) * (g, 1))) = 0) →
      y.val = 0 := by
  subst h_signs
  choose ω hω_norm h_pair using h_place
  exact ⟨ω, fun y hy_level h_orth ↦ eq_zero_of_petersson_translate_eq_zero
    ⟨h_rank, h_exponent, h_dim, h_cusp, h_rank_pow, h_places, h_pow_le, h_level⟩ h_gap h_gap'
    h_entry hω_norm h_pair y.prop (mem_levelSpace_formRep_iff.1 hy_level) h_orth⟩

end DeepLevelTest

/-! ## Forms of level `J_M` on Y₀ -/

section RowsReached

open Matrix.Norms.L2Operator

/-- At every infinite place the generator `D.gridLevelGen = D.piM ^ D.natB` of the deep level
has modulus `√D.M ^ D.natB`. -/
lemma New.Data.norm_gridLevelGen {P : Parameters} (D : Data P)
    (w : NumberField.InfinitePlace D.E) : ‖Φ w D.gridLevelGen.val‖ = √D.M ^ D.natB := by
  have h_sq : ‖Φ w D.piM‖ ^ 2 = D.M := by
    simpa [sq] using congrArg (fun a : NumberField.RingOfIntegers D.E ↦ ‖Φ w a‖) D.piM_mul_star
  simp [← h_sq]

/-- There is a real point `g` of `GInf D.E (D.gridSigns true 0 0 0)`, the archimedean unitary group
on the index type `D.Y 0 ⊕ Unit`, the index type of `Ỹ^0_0 = Y₀ ⊕ ⟨1⟩`, with the following property.
Let `y` lie in `D.principalForms`, so it is a form on `Y₀ = D.spaceY 0` of type `D.paramW` and level
`J_M = D.chosenLevel`. Then `y` vanishes if it is Petersson orthogonal to `x ↦ φ ((x ⊕ 1) g)` for
all `φ` in `D.gridLevelForms 0`, the forms on `Ỹ^0_0` of type `D.gridKernel true 0 0 true` and of
the principal level of `D.gridLevelGen`. -/
lemma New.Data.exists_eq_zero_of_orthogonal_gridLevelForms {P : Parameters} (D : Data P) :
    ∃ g : GInf (n := D.Y 0 ⊕ Unit) D.E (D.gridSigns true 0 0 0),
      ∀ y ∈ D.principalForms (D.spaceY 0),
      (∀ φ ∈ D.gridLevelForms 0, (D.spaceY 0).petersson y.val
        (fun x : New.G D.E (D.signsY 0) ↦
          φ (G.reindex (.refl (D.Y 0 ⊕ Unit)) D.gridSigns_true_zero.symm (.sum (x, 1)) * (g, 1))) =
            0) →
      y.val = 0 := by
  -- At each infinite place `IsSteep.exists_volume_le_mul_norm_integral_dsCoeff` gives a point at
  -- which the pairing of the matrix coefficients of the two types is bounded from below. Then
  -- `Exchange.exists_forall_eq_zero_of_petersson_restrict_eq_zero` applies with the sizes `h_sizes`
  -- below.
  obtain ⟨e, h_steep⟩ : ∃ e : D.InitIndex 0 ⊕ Fin (2 * D.ϱ + 2) ≃ D.GridIndex false 0 0,
      ∀ w : D.Φ, DiscreteSeries.IsSteep (D.gridParam false 0 0 0 w) (D.liftWeight 0 w) e :=
    D.exists_isSteep false
  obtain ⟨e', h_steep'⟩ : ∃ e' : D.InitIndex 0 ⊕ Fin (2 * D.ϱ + 2 + 1) ≃ D.GridIndex true 0 0,
      ∀ w : D.Φ, DiscreteSeries.IsSteep (D.gridParam true 0 0 0 w) (D.liftWeight 0 w) e' :=
    D.exists_isSteep true
  have h_mono : Monotone fun k : ℕ ↦ √D.M ^ k := pow_right_mono₀ D.le_of_hasLogBound
  have abs_param_le (z : Bool) (w : D.Φ) (x : D.GridIndex z 0 0) :
      |D.gridParam z 0 0 0 w x| ≤ ⌈20 * D.b⌉₊ :=
    D.abs_gridParam_le (z := z) w bot_le bot_le x
  -- These bounds for `β` and for the two ranks are found as instances by `D.le_of_hasLogBound` and
  -- its versions for natural numbers, which compare quantities by their logarithmic bounds.
  have β_lb : D.HasLogLower (√D.M ^ ⌈D.x⌉₊) (3 * (20 * D.logB / 2)) :=
    D.hasLogLower_of_le (G := √D.M ^ 3) (h_mono D.nat_le_of_hasLogBound)
  have rank_ub : D.HasLogUpper (Fintype.card (D.Y 0)) (5 * D.logX + 3) :=
    D.hasLogUpper_of_le_of_nonneg (F := D.r) (by simp [D.card_rowIndex]) (Nat.cast_nonneg _)
  have rank_ub' : D.HasLogUpper (Fintype.card (D.Y 0 ⊕ Unit)) (max (5 * D.logX + 3) 0 + 1) :=
    D.hasLogUpper_of_le_of_nonneg (F := D.r + 1) (by simp [D.card_rowIndex]) (Nat.cast_nonneg _)
  let β : ℝ := √D.M ^ ⌈D.x⌉₊
  let A : ℕ := D.r ^ 4
  let N : ℕ := 20 * (Fintype.card (D.Y 0 ⊕ Unit) + Fintype.card (D.Y 0)) ^ 2
  have h_sizes : Exchange.HasDeepLevelSizes D (D.Y 0) A ⌈20 * D.b⌉₊ N β
      (β ^ (20 * A * (D.f + 1))) :=
    { rank_sq_lt := D.nat_lt_of_hasLogBound
      exponent_lt := D.nat_lt_of_hasLogBound
      dim_le := D.nat_le_of_hasLogBound
      cuspConst_sq_le := by rw [cuspConst]; exact D.le_of_hasLogBound
      rank_pow_le := D.le_of_hasLogBound
      places_le := D.le_of_hasLogBound
      pow_le := le_rfl
      pow_le_norm_gridLevelGen := fun w ↦ by
        rw [D.norm_gridLevelGen w, ← pow_mul, ← pow_mul]
        exact h_mono D.nat_le_of_hasLogBound }
  refine Exchange.exists_forall_eq_zero_of_petersson_restrict_eq_zero (D.Y 0) A β
    (h_gap := fun w ↦ (D.hasGap_signsY_paramW w).mono D.nat_le_of_hasLogBound)
    (h_gap' := fun w ↦ (D.hasGap_gridParam w true 0 0 0).neg.mono D.nat_le_of_hasLogBound)
    (h_entry := abs_param_le false) h_sizes.rank_sq_lt h_sizes.exponent_lt h_sizes.dim_le
      h_sizes.cuspConst_sq_le
    h_sizes.rank_pow_le h_sizes.places_le h_sizes.pow_le h_sizes.pow_le_norm_gridLevelGen fun w ↦ ?_
  -- `gridSigns_true_zero` writes the signs of `Ỹ^0_0` as those of `Y₀` followed by `1`; along this
  -- equality the facts on `D.gridParam true 0 0 0 w` are facts on `l'`.
  let l' : HCParam (Sum.elim (D.signsY 0) (1 : Unit → ℤˣ)) := D.gridParam true 0 0 0 w
  obtain ⟨h_steep_l', h_gap'⟩ : DiscreteSeries.IsSteep l' (D.liftWeight 0 w) e' ∧ l'.HasGap D.gap :=
    D.gridSigns_true_zero ▸ ⟨h_steep' w, D.hasGap_gridParam w true 0 0 0⟩
  have h_steep_neg : DiscreteSeries.IsSteep (-(-l')) (D.liftWeight 0 w) e' := by rwa [neg_neg]
  have h_card_bound : (Fintype.card (D.Y 0 ⊕ Unit) : ℝ) ^ 4 *
      (6 * D.liftWeight 0 w) ^ (2 * (2 * D.ϱ + 2) + 2) ≤ β := by
    grw [show (Fintype.card (D.Y 0 ⊕ Unit) : ℝ) ≤ √D.M from D.le_of_hasLogBound,
      show (6 * D.liftWeight 0 w : ℝ) ≤ √D.M from D.le_of_hasLogBound, ← pow_add]
    exact h_mono D.nat_le_of_hasLogBound
  have h_log : 10 ^ 30 * (((Fintype.card (D.Y 0 ⊕ Unit) : ℝ) + Fintype.card (D.Y 0)) ^ 2 *
      Real.log β) ^ 3 ≤ (D.r ^ 7 : ℕ) := by
    rw [Real.log_pow]
    exact D.le_of_hasLogBound
  have h_even : Even (2 * D.ϱ + 2) := by grind
  exact (h_steep w).exists_volume_le_mul_norm_integral_dsCoeff h_even h_steep_neg
    (hB := D.le_of_hasLogBound)
    (hl := (D.hasGap_signsY_paramW w).mono D.nat_le_of_hasLogBound)
    (hl' := h_gap'.neg.mono D.nat_le_of_hasLogBound)
    (hL := abs_param_le false w) (hL' := fun x ↦ (abs_neg _).trans_le (abs_param_le true w x))
    (hβ := D.le_of_hasLogBound) (hn := D.le_of_hasLogBound) h_card_bound h_log

end RowsReached
end
end

/-!
# The maps `Θ^♭` and `res^♭`, and the first path

The first path consists of the spaces `Ỹ^m_0, …, Ỹ^0_0` and `Y₀, …, Y_m`, which are hermitian spaces
over the CM field `D.E`. These are the nodes `(z, 0, i)`, the first columns of the two grids:
`(false, 0, i)` is `Y_i` and `(true, 0, i)` is `Ỹ^i_0`. The iterated transposed lifts
`New.Data.transposedChain` along such a column are the transposes of the chain of theta lifts
`New.Exchange.weightedChain`. In the grid of the `Ỹ` the composite of all `m` of them is
`Θ^♭ = D.transposedChain 1 true 0`. The letter `ϑ` stands for an `m`-fold twist (`D.MFoldTwist`): a
tame character whose powers up to the `m`-th are non-trivial at each place of its modulus `Q`.

Notions from other files:
* `New.Data.GridForm` and `New.Data.TriangleForm`: in the grid of the `Y` (the Boolean `false`) the
  conjugate forms and the forms at a node; in the grid of the `Ỹ` (the Boolean `true`) the forms and
  the conjugate forms.
* `New.Data.triangleModulus`: the modulus of the point data along the first column of a grid. It is
  `𝔪₀ = π_M Q` for the `Y` and `𝔟 = π_M ^ b` for the `Ỹ`, with `π_M = D.piM`.
* `New.Data.triangleGLCard`: the index `n_𝔪₀(Y_i)` or `n_𝔟(Ỹ^i_0)` of the level of that modulus.
  Each lift and each transposed lift along the column is multiplied by the index of its smaller
  space; for the `Ỹ` these factors are constants.
* `New.Data.principalForms`: the forms of the level `J_M = D.chosenLevel`, here on `Y₀`.
* `New.Data.lowerChainUpTo`: the chain of twisted lifts from `Y₀` to `Y_j`; for `j = m` it is `Θ_ϑ`.

## Main definitions and results

* `New.Data.eq_zero_of_weightedChain_triangleLift_eq_zero`,
  `New.Data.gridLevelForms_eq_map_transposedChain`: the chain of the `Ỹ` is injective on level `𝔟`,
  and its transpose `Θ^♭` is onto that level.
* `New.Data.IsFlatRestriction`: the map `res^♭`, given by its pairings;
  `New.Data.exists_isFlatRestriction_range_eq_top`: at a suitable real point it is onto.
* `New.Data.exists_isPathDatum_integral_eq`: the pairing with the lifts of a restriction is a
  constant multiple of a period of path data on the first path.

## Relation to the literature

See `New.Determinant.AuxiliaryForms.DeepLevelVanishing` for related work.
-/

@[expose] public section

namespace New.Data

/-! ## Transposes of the chains of lifts, and surjectivity of `Θ^♭` -/

section DescentOnto

open Space Submodule MeasureTheory Modulus

variable {P : Parameters} (D : Data P)

/-- Grid `z` is the grid of the `Y` for `z = false` and that of the `Ỹ` for `z = true`; its first
column has the nodes `0, …, m`. Let `χ = gridChar ϑ (!z) i n'` be the idele class character of
`U(1)` attached to the edge between the nodes `i` and `i + 1` of this column. It carries the twist
`ϑ ^ (i + 1)` for the `Y` and no twist for the `Ỹ`; the type `n'` enters only through the exponent
of the restriction `upsilonU1` to `U(1)` of the splitting character of the Weil representation.
Then `χ` is trivial on the determinant `detFin s u` of every finite integral point `u` of a unitary
group that is trivial modulo `triangleModulus z ϑ`, the ideal `π_M Q` for the `Y` and
`π_M ^ D.natB` for the `Ỹ`. The signs `s` are those of the hermitian form at the infinite places
and do not matter at the finite ones. -/
lemma gridChar_detFin_eq_one (z : Bool) (ϑ : D.MFoldTwist) (i : ℕ) (n' : Type) [Fintype n']
    {n : Type} [Fintype n] [DecidableEq n] (s : n → ℤˣ) {u : stdLevel D.E n}
    (hu : (triangleModulus z ϑ).reductionGL u = 1) :
    (gridChar ϑ (!z) i n').val (detFin s u.val) = 1 := by
  -- The tame part is trivial outside the modulus, so the value depends only on `u` modulo it.
  have h_unramified (w : FinPlace D.E) (hw : w ∉ (triangleModulus z ϑ).places) :
      gridTamePart ϑ (!z) i w = 1 := by
    -- The places of the modulus are the chosen and twist places, outside which the part is trivial.
    cases z <;> rw [Rows.places_levelModulus] at hw
    · exact (D.descentPair (ϑ.pow (i + 1)) (i + 1)).tame_eq_one w hw
    · exact (D.descentPair .one (i + 1)).tame_eq_one w hw
  have h_value : ((gridChar ϑ (!z) i n').val (detFin s u.val) : ℂ) =
      (triangleModulus z ϑ).charOfTamePart (gridTamePart ϑ (!z) i)
        ((triangleModulus z ϑ).reductionGL u).val.det :=
    (gridChar_hasWeight ϑ (!z) i n').apply_det_eq_charOfTamePart h_unramified u
  ext
  simp [h_value, hu]

/-- Let `S` and `T` be the hermitian spaces `D.gridSpace 0 z 0 i` and `D.gridSpace 0 z 0 (i + 1)` at
the nodes `i` and `i + 1` of the first column of the grid of the `Y` (`z = false`) or of the `Ỹ`
(`z = true`); the first argument `0`, the offset, selects the grids themselves. The product of their
adelic unitary groups acts on the data on `Hom(S, T)` by `New.pairWeil`, the Weil representation
times the characters `gridChar` of the edge on the two determinants. A pair `(u, u')` of finite
integral points that are trivial modulo the ideal `𝔫 = triangleModulus z ϑ` fixes the datum
`New.modDatum S T 𝔫 Ψ v`. This is the product of `v` at the infinite places, a vector of the Fock
model for the signs of `Hom(S, T)`, the function `Ψ` of matrices modulo `𝔫` at the places of `𝔫`,
and the vacuum elsewhere. -/
lemma pairWeil_gridChar_modDatum_eq_self (z : Bool) (ϑ : D.MFoldTwist) (i : ℕ)
    {u : stdLevel D.E (D.GridIndex z 0 i)} (hu : (triangleModulus z ϑ).reductionGL u = 1)
    {u' : stdLevel D.E (D.GridIndex z 0 (i + 1))} (hu' : (triangleModulus z ϑ).reductionGL u' = 1)
    (Ψ : Matrix (D.GridIndex z 0 (i + 1)) (D.GridIndex z 0 i) (triangleModulus z ϑ).ResidueRing → ℂ)
    (v : Heisenberg.IsVacuum.Model
      (Fock.realHeisenberg
        (realSigns D.E (homSigns (D.gridSigns z 0 0 i) (D.gridSigns z 0 0 (i + 1)))))) :
    pairWeil (D.gridSpace 0 z 0 i) (D.gridSpace 0 z 0 (i + 1))
        (gridChar ϑ (!z) i (D.GridIndex z 0 i)) (gridChar ϑ (!z) i (D.GridIndex z 0 (i + 1)))
        ((1, u.val), 1, u'.val)
        (modDatum (D.gridSpace 0 z 0 i) (D.gridSpace 0 z 0 (i + 1)) (triangleModulus z ϑ) Ψ v) =
      modDatum (D.gridSpace 0 z 0 i) (D.gridSpace 0 z 0 (i + 1)) (triangleModulus z ϑ) Ψ v := by
  -- The pair acts through its reduction modulo the modulus and through the two characters.
  rw [pairWeil_modDatum_stdLevel, D.gridChar_detFin_eq_one z ϑ i _ _ hu,
    D.gridChar_detFin_eq_one z ϑ i _ _ hu', hu, hu']
  simp

/-- Let `φ` be an element of `GridForm z 0 D.m`: a conjugate form on `Y_m` for `z = false`, a form
on `Ỹ^m_0` for `z = true`. For a node `i < m` of that column, `transposedChain ϑ z i φ` is the image
of `φ` at the node `i` under the composite of the transposed theta lifts between neighbouring nodes,
a form with the weight `gridKernel z 0 i true`. Right translation `formRep` by a finite integral
point `u` that is trivial modulo `triangleModulus z ϑ` fixes this image. -/
lemma formRep_transposedChain_eq_self (z : Bool) (ϑ : D.MFoldTwist) {i : ℕ} (hi_lt : i < D.m)
    (φ : D.GridForm z 0 D.m) (u : stdLevel D.E (D.GridIndex z 0 i))
    (hu : (triangleModulus z ϑ).reductionGL u = 1) :
    (D.gridSpace 0 z 0 i).formRep (D.gridKernel z 0 i true) u.val (transposedChain ϑ z i φ) =
      transposedChain ϑ z i φ := by
  -- The last transposed lift has a datum that `(u, 1)` fixes.
  have h_pointLift_fixed (x : D.GridForm z 0 (i + 1)) :
      (D.gridSpace 0 z 0 i).formRep (D.gridKernel z 0 i true) u.val (pointTransposedLift ϑ z i x) =
        pointTransposedLift ϑ z i x := by
    obtain ⟨-, h_arrow⟩ := (isEdgeFamily_grid_succ_right (z := z) id zero_le hi_lt).isArrow_modDatum
      (i := ϑ) (S := D.gridSpace 0 z 0 i) (T := D.gridSpace 0 z 0 (i + 1))
      (Ψ := Exchange.pointDatum (triangleModulus z ϑ).ResidueRing)
    -- As `(u, 1)` fixes the datum, `u` fixes every transposed lift.
    have h_datum := D.pairWeil_gridChar_modDatum_eq_self z ϑ i hu (u' := 1) (map_one _)
    simp only [pointTransposedLift, LinearMap.smul_apply, map_smul]
    apply congrArg ((triangleGLCard z ϑ i : ℂ) • ·)
    simpa using! h_arrow.formRep_formLift_of_eq_smul (c := 1)
      ((h_datum _ _).trans (one_smul ℂ _).symm) x
  rw [transposedChain_of_lt ϑ hi_lt, LinearMap.comp_apply, h_pointLift_fixed]

/-- The space `TriangleForm z 0 i` consists of forms on `Y_i` for `z = false` and of conjugate forms
on `Ỹ^i_0` for `z = true`. For `0 < i ≤ m` let `y` be such a form at the node `0`. Its image under
the weighted chain of the `i` theta lifts `triangleLift` between neighbouring nodes, the one from
the node `b` multiplied by `triangleGLCard z ϑ b`, is fixed under right translation `triangleRep` by
every finite integral point `u` of the unitary group at the node `i` that is trivial modulo
`triangleModulus z ϑ`. -/
lemma triangleRep_weightedChain_eq_self (z : Bool) (ϑ : D.MFoldTwist) {i : ℕ} (hi_ne : i ≠ 0)
    (hi_le : i ≤ D.m) (y : D.TriangleForm z 0 0) (u : stdLevel D.E (D.GridIndex z 0 i))
    (hu : (triangleModulus z ϑ).reductionGL u = 1) :
    D.triangleRep z 0 i u.val (Exchange.weightedChain (D.triangleGLCard z) (D.triangleLift z) ϑ 0 i
      y) =
      Exchange.weightedChain (D.triangleGLCard z) (D.triangleLift z) ϑ 0 i y := by
  -- The last lift has a datum that `(1, u)` fixes.
  obtain ⟨i, rfl⟩ : ∃ j : ℕ, i = j + 1 := Nat.exists_eq_succ_of_ne_zero hi_ne
  have h_lift (x : D.TriangleForm z 0 i) :
      D.triangleRep z 0 (i + 1) u.val (D.triangleLift z ϑ 0 i x) = D.triangleLift z ϑ 0 i x := by
    obtain ⟨h_arrow, -⟩ := (isEdgeFamily_grid_succ_right (z := z) id zero_le hi_le).isArrow_modDatum
      (i := ϑ) (S := D.gridSpace 0 z 0 i) (T := D.gridSpace 0 z 0 (i + 1))
      (Ψ := Exchange.pointDatum (triangleModulus z ϑ).ResidueRing)
    -- As `(1, u)` fixes the datum, `u` fixes every lift.
    have h_datum := D.pairWeil_gridChar_modDatum_eq_self z ϑ i (u := 1) (map_one _) hu
    simpa using! h_arrow.formRep_formLift_of_eq_smul (c := 1)
      ((h_datum _ _).trans (one_smul ℂ _).symm) x
  rw [Exchange.weightedChain_succ_apply, map_smul, h_lift]

/-- For a node `i ≤ m`, let `U` be the image of `y` under the weighted chain of the `i` theta lifts
`triangleLift`, the one from the node `b` multiplied by `triangleGLCard z ϑ b`, the index at `b` of
the level of modulus `triangleModulus z ϑ`. Let `T b = transposedChain ϑ z b` be the composite of
the transposed lifts, equally weighted, from the node `m` to the node `b`; it acts on `φ`, which has
the conjugate weight to that of `y`. Then `∫ T i φ * U = ∫ T 0 φ * y`, each integral over the adelic
unitary group `New.G` of the node with its measure `quotMeasure` on the automorphic quotient. -/
lemma integral_transposedChain_mul_weightedChain (z : Bool) (ϑ : D.MFoldTwist) {i : ℕ}
    (hi_le : i ≤ D.m) (y : D.TriangleForm z 0 0) (φ : D.GridForm z 0 D.m) :
    ∫ g : New.G D.E (D.gridSigns z 0 0 i),
        transposedChain ϑ z i φ g *
          Exchange.weightedChain (D.triangleGLCard z) (D.triangleLift z) ϑ 0 i y g
        ∂(D.gridSpace 0 z 0 i).quotMeasure =
      ∫ g : New.G D.E (D.gridSigns z 0 0 0), transposedChain ϑ z 0 φ g * y g
        ∂(D.gridSpace 0 z 0 0).quotMeasure := by
  -- Induction on `i`; the step uses the edge from node `i` to node `i + 1`.
  induction i with
  | zero => rfl
  | succ i ih => ?_
  obtain ⟨h_lift, h_transposed⟩ :=
    (isEdgeFamily_grid_succ_right (z := z) id zero_le hi_le).isArrow_modDatum
      (i := ϑ) (S := D.gridSpace 0 z 0 i) (T := D.gridSpace 0 z 0 (i + 1))
      (Ψ := Exchange.pointDatum (triangleModulus z ϑ).ResidueRing)
  -- The lift and the transposed lift along the edge carry the same weight.
  have h_transpose (x : D.GridForm z 0 (i + 1)) (w : D.TriangleForm z 0 i) :
      ∫ g, x g * ((triangleGLCard z ϑ i : ℂ) • D.triangleLift z ϑ 0 i w) g
          ∂(D.gridSpace 0 z 0 (i + 1)).quotMeasure =
        ∫ g, pointTransposedLift ϑ z i x g * w g ∂(D.gridSpace 0 z 0 i).quotMeasure := by
    -- Move the weight inside the lift, transpose, and regroup it with the transposed lift.
    rw [← map_smul]
    refine (h_lift.integral_mul_formLift_swap h_transposed
      ((triangleGLCard z ϑ i : ℂ) • w) x).trans ?_
    congr 1 with g
    exact mul_right_comm (triangleGLCard z ϑ i : ℂ) (w g) _
  rw [Exchange.weightedChain_succ_apply, h_transpose, ← ih (Nat.le_of_succ_le hi_le),
    transposedChain_of_lt ϑ hi_le, LinearMap.comp_apply]

/-- The grid of the `Ỹ` (the Boolean `true`) has the weight of the `Y` with the opposite sign, so
its `TriangleForm`s are conjugate forms; `D.triangleBase true` consists of those on `Ỹ^0_0` of level
`𝔟 = D.piM ^ D.natB`. The weighted chain of all `D.m` theta lifts `New.Data.triangleLift` from
`Ỹ^0_0` to `Ỹ^m_0`, for the trivial twist `1`, is injective on this space. -/
lemma eq_zero_of_weightedChain_triangleLift_eq_zero {y : D.triangleBase true}
    (hy : Exchange.weightedChain (D.triangleGLCard true) (D.triangleLift true) 1 0 D.m y = 0) :
    y = 0 := by
  obtain ⟨d, h_triangle, -⟩ := D.exists_isTriangle true
  exact h_triangle.eq_zero_of_weightedChain_eq_zero D.m 0 (by simp) y hy

/-- Let `Ỹ^i_0` be the hermitian space at the node `(0, i)` of the grid of the `Ỹ` (the Boolean
`true`), and `D.gridLevelForms i` the forms of level `𝔟` on it: those fixed under right translation
by the finite integral points congruent to `1` modulo `𝔟 = D.piM ^ D.natB`, a power of the generator
of the product of the chosen places. For `i < m` the transposed theta lift from `Ỹ^(i+1)_0` to
`Ỹ^i_0` is weighted by the index of that level on `Ỹ^i_0`. The composite
`Θ^♭ = D.transposedChain 1 true 0` of all `D.m` of them, for the trivial twist `1`, maps forms of
level `𝔟` on `Ỹ^m_0` to forms of level `𝔟` on `Ỹ^0_0`. -/
lemma map_transposedChain_le_gridLevelForms :
    (D.gridLevelForms D.m).map (D.transposedChain 1 true 0) ≤ D.gridLevelForms 0 := by
  rintro _ ⟨φ, -, rfl⟩
  refine mem_levelSpace_formRep_iff.2 fun k hk g ↦ ?_
  have h_fixed : (D.gridSpace 0 true 0 0).formRep (D.gridKernel true 0 0 true) k
      (D.transposedChain 1 true 0 φ) = D.transposedChain 1 true 0 φ :=
    D.formRep_transposedChain_eq_self true 1 (Nat.pos_of_neZero D.m) φ ⟨k, hk.1⟩
      ((mem_principalLevel_iff gridModulus_one_ideal _).1 hk)
  exact congrFun (congrArg Subtype.val h_fixed) g

/-- Take the transposed theta lifts from `Ỹ^(i+1)_0` to `Ỹ^i_0` for `i < D.m`. Their composite
`Θ^♭ = D.transposedChain 1 true 0`, for the trivial twist `1`, maps the forms of level `𝔟` on
`Ỹ^m_0` onto those on `Ỹ^0_0`. -/
lemma gridLevelForms_eq_map_transposedChain :
    D.gridLevelForms 0 = (D.gridLevelForms D.m).map (D.transposedChain 1 true 0) := by
  have : Module.Finite ℂ (D.gridLevelForms D.m) := finite_levelSpace
    (isConjKernelPair_gridKernel (by simp) _).1 ⟨_, isOpen_principalLevel Fact.out⟩
  suffices orth_le :
      ((D.gridLevelForms D.m).map (D.transposedChain 1 true 0))ᗮ ⊓ D.gridLevelForms 0 ≤ ⊥ by
    simpa [le_bot_iff.1 orth_le] using
      (sup_orthogonal_inf_of_hasOrthogonalProjection D.map_transposedChain_le_gridLevelForms).symm
  rintro z ⟨hz_orth, hz_level⟩
  -- `y` is the conjugate of `z`, `U` its chain of lifts, and `φ` the conjugate of `U`.
  let y : D.triangleBase true := ⟨conjForm (isConjKernelPair_gridKernel (by simp) true).2 z,
    mem_levelSpace_formRep_iff.2 fun k hk g ↦
      congrArg star (mem_levelSpace_formRep_iff.1 hz_level k hk g)⟩
  let U := Exchange.weightedChain (D.triangleGLCard true) (D.triangleLift true) 1 0 D.m y
  let φ := conjForm (isConjKernelPair_gridKernel (by simp) false).2 U
  have φ_mem : φ ∈ D.gridLevelForms D.m := mem_levelSpace_formRep_iff.2 fun k hk g ↦
    congrArg star <| congrFun (congrArg Subtype.val <|
      D.triangleRep_weightedChain_eq_self true 1 (NeZero.ne D.m) le_rfl y ⟨k, hk.1⟩
        ((mem_principalLevel_iff gridModulus_one_ideal _).1 hk)) g
  -- By transposition, `⟪U, U⟫ = ⟪z, Θ^♭ φ⟫ = 0`, so `U = 0` and hence `z = 0`.
  have h := D.integral_transposedChain_mul_weightedChain true 1 le_rfl y φ
  simp only [transposedChain_self, mul_comm (D.transposedChain 1 true 0 φ _)] at h
  have hU : inner ℂ U U = 0 :=
    (h : inner ℂ U U = _).trans (inner_eq_zero_symm.1 (hz_orth _ ⟨φ, φ_mem, rfl⟩))
  exact Subtype.ext <| star_eq_zero.1 <| congrArg (fun x ↦ x.val.val)
    (D.eq_zero_of_weightedChain_triangleLift_eq_zero (inner_self_eq_zero.1 hU))

end DescentOnto

/-!
## The first path

Restrictions of forms that come from the definite space `Ỹ^m_0` reach every form of level `J_M` on
`Y₀`, and the pairing with the chain of lifts of such a restriction is a period of path data on the
first path.
-/

section FirstPath

open MeasureTheory Function Exchange Space Submodule

variable {P : Parameters} (D : Data P)

/-- Every form is reached. Here `Y₀ = D.spaceY 0`, and `Ỹ^0_0` is its orthogonal sum with a line.
The level `J_M` consists of the finite integral points that are congruent to `1` modulo every chosen
place, that is, modulo every prime divisor of `π_M = D.piM`; `principalForms` are the forms of this
level. There is a real point `g₀` of `U(Ỹ^0_0)` such that for every such form `y ≠ 0` on `Y₀` there
is a form `φ` of level `𝔟 = π_M ^ D.natB` on the definite space `Ỹ^m_0` (`gridLevelForms D.m`) with
a nonzero pairing `diagonalPeriodForm` of the conjugate `conjForm` of `y` and `Θ^♭ φ` at `g₀`: the
integral of `star (y h)` times `(Θ^♭ φ) (h g₀)` over `U(Y₀)`. Here `Θ^♭` is
`D.transposedChain 1 true 0`, the composite of the transposed theta lifts whose datum at the places
of `𝔟` is the indicator of the inclusion matrix (`pointDatum`), each weighted by the index of the
level `𝔟` on its target. -/
lemma exists_forall_diagonalPeriodForm_ne_zero :
    ∃ g₀ : GInf D.E (D.gridSigns true 0 0 0), ∀ y ∈ D.principalForms (D.spaceY 0), y ≠ 0 →
      ∃ φ ∈ D.gridLevelForms D.m,
        diagonalPeriodForm 1 zero_le g₀ (conjForm D.gridKernel_zero_true_eq_star y)
          (D.transposedChain 1 true 0 φ) ≠ 0 := by
  -- `Θ^♭` is onto the forms of level `𝔟`, and no `y ≠ 0` is orthogonal to all their restrictions.
  obtain ⟨g₀, h_eq_zero_of_orthogonal⟩ := D.exists_eq_zero_of_orthogonal_gridLevelForms
  refine ⟨g₀, fun y hy hy_ne ↦ ?_⟩
  by_contra! h_zero
  refine hy_ne (Subtype.ext (h_eq_zero_of_orthogonal y hy fun ψ hψ ↦ ?_))
  obtain ⟨φ, hφ, rfl⟩ := D.gridLevelForms_eq_map_transposedChain.le hψ
  -- The pairing of `y` with a restriction is, by definition, the period of the conjugate of `y`.
  have h_period (F : D.GridForm true 0 0) :
      (D.spaceY 0).petersson y.val
          (fun x ↦ F (G.reindex (.refl (D.Y 0 ⊕ Unit)) D.gridSigns_true_zero.symm (.sum (x, 1)) *
            (g₀, 1))) =
        diagonalPeriodForm 1 zero_le g₀ (conjForm D.gridKernel_zero_true_eq_star y) F := by
    simp [petersson, periodPairing]
    rfl
  exact (h_period _).trans (h_zero φ hφ)

variable {D} in
/-- `r` is a restriction map `res^♭` at the real point `g` of the unitary group of `Ỹ^0_0`, the sum
of `Y₀` and a line, in the sense of its pairings: every form `y` on `Y₀` of level `𝔪₀ = π_M Q`,
where `Q` is the modulus of some twist, has the same pairing with `r φ` as with the function
`h ↦ (Θ^♭ φ) (h g)` on `U(Y₀)`. Here `φ` is a form of level `𝔟` on `Ỹ^m_0` and `Θ^♭` is
`D.transposedChain 1 true 0`. The forms `y` of the level `J_M` (that of the prime divisors of
`π_M`) are among these, and their pairings determine `r`. -/
def IsFlatRestriction (g : GInf D.E (D.gridSigns true 0 0 0))
    (r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)) : Prop :=
  ∀ (φ : D.gridLevelForms D.m) (ϑ : D.MFoldTwist),
    ∀ y ∈ levelSpace ((D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 false))
      (levelY ϑ 0),
    (D.spaceY 0).petersson y (r φ) =
      diagonalPeriodForm ϑ zero_le g (conjForm D.gridKernel_zero_true_eq_star y)
        (D.transposedChain 1 true 0 φ)

/-- Let `g` be a real point (`GInf`) of the unitary group of `Ỹ^0_0`, the sum of `Y₀ = D.spaceY 0`
and a line. Some linear map `r` from the forms of level `𝔟 = π_M ^ D.natB`, where `π_M = D.piM`, on
`Ỹ^m_0` (`gridLevelForms D.m`) to the forms on `Y₀` of level `J_M` (`principalForms`: integral
points congruent to `1` modulo the prime divisors of `π_M`) satisfies `IsFlatRestriction g`. -/
lemma exists_isFlatRestriction (g : GInf D.E (D.gridSigns true 0 0 0)) :
    ∃ r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0), IsFlatRestriction g r := by
  obtain ⟨proj, h_proj⟩ := D.exists_petersson_eq_diagonalPeriodForm g
  let thetaFlat : D.gridLevelForms D.m →ₗ[ℂ] D.gridLevelForms 0 :=
    (D.transposedChain 1 true 0).restrict
      fun φ hφ ↦ D.gridLevelForms_eq_map_transposedChain.ge (mem_map_of_mem hφ)
  exact ⟨proj ∘ₗ thetaFlat, fun φ ↦ h_proj (thetaFlat φ)⟩

/-- Let `Ỹ^0_0` be the orthogonal sum of `Y₀` and a line. There are a real point `g` of its unitary
group and a surjective linear map `r` from the forms of level `𝔟 = π_M ^ D.natB` on `Ỹ^m_0` to the
forms on `Y₀` of level `J_M` with `IsFlatRestriction g r`: every form `y` on `Y₀` of level
`𝔪₀ = π_M Q`, for an `m`-fold twist with modulus `Q`, has the same Petersson product with `r φ` as
with the function `h ↦ (Θ^♭ φ) (h g)` on `U(Y₀)`. -/
lemma exists_isFlatRestriction_range_eq_top :
    ∃ (g : GInf D.E (D.gridSigns true 0 0 0))
      (r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)),
      IsFlatRestriction g r ∧ r.range = ⊤ := by
  obtain ⟨g, h_reach⟩ := D.exists_forall_diagonalPeriodForm_ne_zero
  obtain ⟨r, hr⟩ := D.exists_isFlatRestriction g
  -- The space is finite-dimensional, and a form `y` orthogonal to the range is zero.
  refine ⟨g, r, hr, orthogonal_eq_bot_iff.1 (bot_unique fun y hy ↦ Subtype.ext ?_)⟩
  by_contra hy_ne
  obtain ⟨φ, hφ, h_ne⟩ := h_reach _ y.property hy_ne
  have h_orthogonal : (D.spaceY 0).petersson y.val.val (r ⟨φ, hφ⟩).val.val = 0 :=
    inner_eq_zero_symm.1 (hy _ (LinearMap.mem_range_self r ⟨φ, hφ⟩))
  -- The forms of level `J_M` have the level `𝔪₀` of the trivial twist.
  have h_pairing : (D.spaceY 0).petersson y.val.val (r ⟨φ, hφ⟩).val.val =
      diagonalPeriodForm 1 zero_le g (conjForm D.gridKernel_zero_true_eq_star y.val)
        (D.transposedChain 1 true 0 φ) :=
    hr ⟨φ, hφ⟩ 1 _ (levelSpace_anti (levelY_le_chosenLevel ..) y.property)
  exact h_ne (h_pairing.symm.trans h_orthogonal)

variable {D} in
/-- Let `r` be a restriction map at `g` (`IsFlatRestriction`): it sends a form `φ` of level `𝔟` on
`Ỹ^m_0` to the form on `Y₀` with the Petersson products of `h ↦ (Θ^♭ φ) (h g)`. Let `y'` be in
`GridForm false 0 D.m`, a form on `Y_m` of the conjugate weight, and `ϑ` an `m`-fold twist. Then the
integral of `y'` times `lowerChainUpTo` of `r φ`, its image under the theta lifts twisted by `ϑ` and
weighted by level indices, is the period `diagonalPeriodForm` at `g`: the integral over `U(Y₀)` of
`y'Lift h * (Θ^♭ φ) (h g)`, where `y'Lift = transposedChain ϑ false 0 y'`. -/
lemma IsFlatRestriction.integral_lowerChainUpTo {g : GInf D.E (D.gridSigns true 0 0 0)}
    {r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)} (hr : IsFlatRestriction g r)
    (ϑ : D.MFoldTwist) (y' : D.GridForm false 0 D.m) (φ : D.gridLevelForms D.m) :
    ∫ x, y' x * D.lowerChainUpTo ϑ D.m (r φ) x ∂(D.spaceY D.m).quotMeasure =
      diagonalPeriodForm ϑ zero_le g (transposedChain ϑ false 0 y')
        (D.transposedChain 1 true 0 φ) := by
  -- Transpose to `Y₀`; against the transposed lift `y'Lift` of `y'`, of level `𝔪₀`, one may
  -- replace `r φ` by the restriction of `Θ^♭ φ`.
  let y'Lift : D.GridForm false 0 0 := transposedChain ϑ false 0 y'
  let y'Lift_conj : (D.gridSpace 0 false 0 0).Form (D.gridKernel false 0 0 false) :=
    conjForm (isConjKernelPair_gridKernel (by simp) true).2 y'Lift
  have h_level : y'Lift_conj ∈
      levelSpace ((D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 false))
        (levelY ϑ 0) := by
    refine mem_levelSpace_formRep_iff.2 fun k hk x ↦ ?_
    have h_fix :
        (D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 true) k y'Lift = y'Lift :=
      D.formRep_transposedChain_eq_self false ϑ (Nat.pos_of_neZero D.m) y' ⟨k, (mem_levelOf.1 hk).1⟩
        ((LevelPlaces.ker_reductionGL_eq _).ge (mem_levelOf.1 hk).2)
    exact congrArg (fun F : D.GridForm false 0 0 ↦ star (F x)) h_fix
  have h_restrict :
      ∫ x, y'Lift x * (r φ).val x ∂(D.spaceY 0).quotMeasure =
        diagonalPeriodForm ϑ zero_le g y'Lift (D.transposedChain 1 true 0 φ) := by
    simpa [y'Lift_conj, petersson, periodPairing] using! hr φ ϑ y'Lift_conj h_level
  -- The chain of lifts is `weightedChain` with the weight written as the order of a group.
  have h_chain : D.lowerChainUpTo ϑ D.m (r φ) =
      weightedChain (D.triangleGLCard false) (D.triangleLift false) ϑ 0 D.m (r φ).val := by
    simp +unfoldPartialApp [liftY, lowerChainUpTo, ← LevelPlaces.card_GL_levelModulus]
    rfl
  -- By transposition the left side is `∫ y'Lift x * r φ x`.
  refine Eq.trans ?_ h_restrict
  simpa [transposedChain_self, h_chain] using!
    D.integral_transposedChain_mul_weightedChain false ϑ le_rfl (r φ).val y'

/-- The twisted edges are those that carry a power of the twist `ϑ` (`IsVerticalEdge`). There are
functions `Ψ ϑ`, one for each twist `ϑ`, of tuples `EdgeTuple ϑ` and a constant `α` as follows.
* `Ψ ϑ` is a path datum (`IsPathDatum`) on the first path: a function of the matrices on its edges,
  invariant up to the edge characters under admissible families of group elements at the nodes, zero
  unless those on twisted edges have left inverses, with values sums of at most
  `edgeMatrixCountBound ϑ ^ (2 * D.m)` roots of unity.
* Whenever `r` is a restriction map at `g`, the pairing of a conjugate form `y'` on `Y_m` with the
  chain `lowerChainUpTo` of theta lifts of `r φ` is `α` times `gridPeriod`: the sum over the tuples
  `S` on the path of `Ψ ϑ S` times the period `diagonalPeriodForm` at `g` of the images of `y'` and
  `φ` under the transposed lifts with the matrices of `S` along the two halves. -/
lemma exists_isPathDatum_integral_eq :
    ∃ Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ,
      (∀ ϑ : D.MFoldTwist,
        IsPathDatum (edgeMatrixCountBound ϑ ^ (2 * D.m)) (TwoGridPath.first D.m).edges (Ψ ϑ)) ∧
      ∃ α : ℂ, ∀ (g : GInf D.E (D.gridSigns true 0 0 0))
        (r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)), IsFlatRestriction g r →
        ∀ (ϑ : D.MFoldTwist) (y' : D.GridForm false 0 D.m) (φ : D.gridLevelForms D.m),
          ∫ x, y' x * D.lowerChainUpTo ϑ D.m (r φ) x ∂(D.spaceY D.m).quotMeasure =
            α * gridPeriod (.first D.m) Ψ g (ϑ, y', φ) := by
  obtain ⟨α, Ψ, hΨ⟩ := exists_isPathDatum_diagonalPeriodForm_eq (D := D)
  exact ⟨Ψ, fun ϑ ↦ (hΨ ϑ).1, α, fun g r hr ϑ y' φ ↦
    (hr.integral_lowerChainUpTo ϑ y' φ).trans ((hΨ ϑ).2 g y' φ)⟩

/-- There are functions `Ψ ϑ`, one for each twist `ϑ`, of tuples `EdgeTuple ϑ`, a real point `g`, a
constant `α` and a map `r` from the forms of level `𝔟` on `Ỹ^m_0` onto the forms on `Y₀` of level
`J_M` as follows.
* `Ψ ϑ` is a path datum (`IsPathDatum`) on the first path: a function of the matrices on its edges,
  invariant up to the edge characters under admissible families of group elements at the nodes, zero
  unless those on twisted edges have left inverses, with values sums of at most
  `edgeMatrixCountBound ϑ ^ (2 * D.m)` roots of unity.
* The pairing of a conjugate form `y'` on `Y_m` with the chain `lowerChainUpTo` of theta lifts of
  `r φ` is `α` times `gridPeriod`: the sum over the tuples `S` on the path of `Ψ ϑ S` times the
  period `diagonalPeriodForm` at `g` of the images of `y'` and `φ` under the transposed lifts with
  the matrices of `S` along the two halves. -/
lemma exists_isPathDatum_first :
    ∃ Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ,
      (∀ ϑ : D.MFoldTwist,
        IsPathDatum (edgeMatrixCountBound ϑ ^ (2 * D.m)) (TwoGridPath.first D.m).edges (Ψ ϑ)) ∧
      ∃ (g : GInf D.E (D.gridSigns true 0 0 0)) (α : ℂ)
        (r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)),
        r.range = ⊤ ∧
        ∀ (ϑ : D.MFoldTwist) (y' : D.GridForm false 0 D.m) (φ : D.gridLevelForms D.m),
          ∫ x, y' x * D.lowerChainUpTo ϑ D.m (r φ) x ∂(D.spaceY D.m).quotMeasure =
            α * gridPeriod (.first D.m) Ψ g (ϑ, y', φ) := by
  obtain ⟨Ψ, hΨ, α, h_period⟩ := D.exists_isPathDatum_integral_eq
  obtain ⟨g, r, hr, h_onto⟩ := D.exists_isFlatRestriction_range_eq_top
  exact ⟨Ψ, hΨ, g, α, r, h_onto, h_period g r hr⟩

end FirstPath

end New.Data
