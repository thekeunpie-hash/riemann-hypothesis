module

import Mathlib.Algebra.Order.Star.Int
public import New.Spanning.RemainingTerms.Box
import Lib.General.Analysis.PackingAndSobolev
import Lib.General.NumberTheory.SUnitsAndClassNumber
import New.Spanning.Unfolding.ReducedPoints
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Topology.UniformSpace.Uniformizable
public import Lib.General.NumberTheory.LatticeCovolumes
public import New.Spanning.RemainingTerms.SiegelLemma
public import New.Spanning.Unfolding.BesselLevelStructure
import Lib.Cohomology.Etale.Basic
public import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import TauCeti.MeasureTheory.Integral.Pi
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import New.Spanning.Unfolding.Setup
import New.Spanning.Bessel.Orthonormality

section
section
/-!
# Class cutoffs and counting frames in boxes

The translates of the cutoff `S.classCutoff c` of a class `c` are shown to add up to one, and
weights bounded by cutoffs are shown to add up to at most a bound for the number of frames in a box.

## Main definitions and results

* `New.Filling.frameImage_eq_frameImage_one_of_close`: a term that moves the frame vectors of a
  point in a box very little fixes the frame.
* `New.Filling.encard_image_frameImage_le`: terms `γ` with `γ⁻¹ y` in a box have few images of the
  frame, since the frame vectors of the points `γ⁻¹ y` lie in a ball and are separated.
* `New.Filling.tsum_le_of_le_classCutoff_mul`: weights bounded by cutoffs add up to at most that
  bound for the number of frames.

Notions from other files:
* `New.frameImage`, `New.frameVector`: the image `γ f` of the frame `f = (e₁, …, e_ϱ, z)` under a
  matrix `γ`, and the vector `y⁻¹ f_a` in Euclidean space.
* `New.frameBox`, `New.besselLength`: the points whose frame vectors have norm at most `ρ`, and the
  infimum of `‖s y‖ + 1` (operator norm) over `s` in the Bessel subgroup.
* `New.Filling.frameBoxRadius`, `New.Filling.basisScale`: the number `S.b ^ (37 n)`, and the scales
  of the normalised basis at an infinite place.
* `New.Filling.classUnipotent`, `New.Filling.classCutoff`: the congruence group of rational
  unipotent elements attached to a class `c`, and a cutoff for its subgroup fixing the frame times
  the indicator of the reduced points.
* `New.Filling.termsOver`: the rational `γ` with `h_c⁻¹ γ h_c'` integral and of reduction `s`, where
  `h_c` is the representative `New.Filling.classRep` of the class `c`.
* `New.Filling.IsAdmissible`: the standing hypotheses, among them the size inequalities between
  `S.b`, `S.realM v` and `S.N`.
-/

@[expose] public section

section BoxPartition

open ENNReal Fin Matrix Module Set Norms.L2Operator Subgroup

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
/-- Let `γ`, `γ'` be rational elements of the unitary group whose images `γ f`, `γ' f` of the frame
`f = (e₁, …, e_ϱ, z)` differ only in the coordinates along the `e_a`. At an infinite place `v`, the
`b`-th frame vectors of `γ⁻¹ y` and `γ'⁻¹ y` then differ by a combination of the vectors `y⁻¹ e_a`.
The coefficient of `y⁻¹ e_a` is the difference of the coordinates along `e_a`, embedded by `Φ v` and
multiplied by the ratio of the scales of `f_b` and `e_a` in the normalised basis at `v`
(`S.basisScale v`). -/
lemma frameVector_sub_eq_sum {γ γ' : S.G E}
    (h_rows : (frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₂ =
      (frameImage (γ' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₂)
    (y : 𝔰.G₁) (v : NumberField.InfinitePlace E) (b : Fin (𝔰.ϱ + 1)) :
    frameVector ((S.ratToInf γ v)⁻¹ * y) b - frameVector ((S.ratToInf γ' v)⁻¹ * y) b =
      ∑ a : Fin 𝔰.ϱ,
        (Φ v ((γ - γ' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (Sum.inl a) (𝔰.besselFrame b)) *
            (S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame a.castSucc))) •
          frameVector y a.castSucc := by
  ext i
  -- The coordinates of `(u⁻¹ y)⁻¹ f_b = y⁻¹ (u f_b)`.
  have h_coord (u : S.G E) : frameVector ((S.ratToInf u v)⁻¹ * y) b i =
      ∑ j : 𝔰.BesselIndex, y⁻¹.val i j * (Φ v (u.val j (𝔰.besselFrame b)) *
        (S.basisScale v (𝔰.besselFrame b) / S.basisScale v j)) := by
    simp [frameVector, Matrix.mul_apply]
  have h_lower (j : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) :
      γ.val (Sum.inr j) (𝔰.besselFrame b) = γ'.val (Sum.inr j) (𝔰.besselFrame b) :=
    congr_fun₂ h_rows j b
  rw [PiLp.sub_apply, h_coord, h_coord, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [h_lower]
  simp [frameVector, mul_sub, mul_comm]

/-- The indicator of the reduced points for the chosen set of representatives is a partition of
unity in boxes (`IsBoxPartitionOfUnity`) for every class `c`. -/
lemma isBoxPartitionOfUnity_reducedIndicator [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (c : S.Classes) :
    S.IsBoxPartitionOfUnity c S.reducedIndicator :=
  IsResidueDomain.isBoxPartitionOfUnity (Classical.epsilon_spec S.exists_isResidueDomain) c

/-- Let `ω` be a partition of unity in boxes for the class `c`: a weight whose translates under
`S.classUnipotent c` add up to one modulo the subgroup fixing the frame, and which vanishes unless
the frame vectors `(y v)⁻¹ f_a` have norm at most `b ^ 27` times `besselLength (y v)`, the infimum
of `‖s (y v)‖ + 1` over `s` in the Bessel subgroup. Here `b = S.b`. If `ω y ≠ 0` and
`besselLength (y v)` is at most `b ^ (6 n + 2) R` with `n = 𝔰.n`, then the frame vectors of `y v`
have norm at most `frameBoxRadius * R`. -/
lemma IsBoxPartitionOfUnity.mem_frameBox {c : S.Classes}
    {ω : (NumberField.InfinitePlace E → 𝔰.G₁) → ℝ≥0∞}
    (hω : S.IsBoxPartitionOfUnity c ω) {y : NumberField.InfinitePlace E → 𝔰.G₁} (hy : ω y ≠ 0)
    {v : NumberField.InfinitePlace E} {R : ℝ} (hR : 0 ≤ R)
    (h_size : besselLength (y v) ≤ S.b ^ (6 * 𝔰.n + 2) * R) :
      y v ∈ frameBox (S.frameBoxRadius * R) := by
  intro a
  have hb : 1 ≤ S.b := S.one_le_b
  grw [hω.mem_frameBox_besselLength y v hy a, h_size, frameBoxRadius, ← mul_assoc, ← pow_add]
  -- Exponents of `b`: `27 + 6 n + 2 ≤ 37 n`.
  gcongr
  linarith only [S.ten_pow_five_le_varrho]

/-- The cutoff `S.classCutoff c` of a class `c` is a cutoff for the rational unipotent elements
fixing the frame, times the indicator of the reduced points. If it is not zero at `y` and
`besselLength (y v)`, the infimum of `‖s (y v)‖ + 1` over `s` in the Bessel subgroup, is at most
`b ^ (6 n + 2) R`, with `b = S.b` and `n = 𝔰.n`, then the frame vectors `(y v)⁻¹ f_a` have norm at
most `frameBoxRadius * R`, where `frameBoxRadius = b ^ (37 n)`. -/
lemma mem_frameBox_of_classCutoff_ne_zero [HasPrimitiveRoot5040 E] [S.IsAdmissible] {c : S.Classes}
    {y : NumberField.InfinitePlace E → 𝔰.G₁} (hy : S.classCutoff c y ≠ 0)
    {v : NumberField.InfinitePlace E} {R : ℝ} (hR : 0 ≤ R)
    (h_size : besselLength (y v) ≤ S.b ^ (6 * 𝔰.n + 2) * R) :
      y v ∈ frameBox (S.frameBoxRadius * R) := by
  rw [classCutoff] at hy
  exact (isBoxPartitionOfUnity_reducedIndicator c).mem_frameBox (right_ne_zero_of_mul hy) hR h_size

/-- If the cutoff of the class `c` is not zero at `y` and all components of `y` have length at most
`S.b ^ (6 n + 2)` with `n = 𝔰.n` (`InCut`), then `y` lies in the set `boxedPoints` of reduced points
in the cut. -/
lemma mem_boxedPoints_of_classCutoff_ne_zero {c : S.Classes}
    {y : NumberField.InfinitePlace E → 𝔰.G₁} (hy : S.classCutoff c y ≠ 0)
    (h_cut : ∀ v : NumberField.InfinitePlace E, InCut (y v) S.b) : y ∈ S.boxedPoints := by
  rw [classCutoff] at hy
  exact mem_boxedPoints_of_reducedIndicator_ne_zero (right_ne_zero_of_mul hy) h_cut

/-- The translates of `S.classCutoff c` under the congruence group `S.classUnipotent c` of rational
unipotent elements add up to one at every point `y`. -/
lemma tsum_classCutoff_eq_one [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (c : S.Classes) (y : NumberField.InfinitePlace E → 𝔰.G₁) :
    ∑' u : S.classUnipotent c, S.classCutoff c (S.ratToInf u * y) = 1 := by
  obtain ⟨β, hβ, -, hβ_sum⟩ := S.exists_classCutoff_eq_mul c
  -- The translates of `β` add up to one on each coset of `S.classUnipotent₀ c`.
  rw [hβ]
  refine (isBoxPartitionOfUnity_reducedIndicator c).tsum_mul_eq_one y
    (fun u ↦ β (S.ratToInf u * y)) fun γ ↦ ?_
  simpa [mul_assoc] using hβ_sum (S.ratToInf γ * y)

/-- Let `f = (e₁, …, e_ϱ, z)` be the frame. If the hermitian products `S.frameProducts g b a` of
`f_b` with `g f_a` equal those of `f_b` with `f_a` for all `b`, then `g` moves `f_a` only along the
vectors `e_i`: all other coordinates of `g f_a` and `f_a` agree. -/
lemma frameImage_inr_eq_of_frameProducts_eq {g : S.G E} {a : Fin (𝔰.ϱ + 1)}
    (h : ∀ b : Fin (𝔰.ϱ + 1), S.frameProducts g b a = S.frameProducts 1 b a) :
    ∀ i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ,
      frameImage (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (Sum.inr i) a =
        frameImage 1 (Sum.inr i) a := by
  -- `h` gives the coordinates along `e*_i` and `z`. Unitarity then says that the middle part of
  -- `g f_a - f_a` is isotropic for `S.ratMiddle E`, which is anisotropic off `z`, so that part
  -- vanishes too.
  let w (i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) : E :=
    (g - 1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (Sum.inr i) (𝔰.besselFrame a)
  have h_dual (i : Fin 𝔰.ϱ) : w (Sum.inr i) = 0 := by
    cases a using lastCases <;>
      simpa [w, frameGram, splitGram, Matrix.mul_apply, Matrix.one_apply] using h i.castSucc
  have h_z : w (Sum.inl (Sum.inr ())) = 0 := by
    cases a using lastCases <;>
      simpa [w, frameGram, splitGram, middleGram, Matrix.mul_apply, Matrix.one_apply, sub_eq_zero,
        S.N_prime.ne_zero] using h (last 𝔰.ϱ)
  have h_unitary :
      ((g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)ᴴ * (S.ratMiddle E).splitGram * g).diag
        (𝔰.besselFrame a) = (S.ratMiddle E).splitGram.diag (𝔰.besselFrame a) :=
    congr_fun₂ (mem_unitaryGroupOf_iff.1 g.prop) (𝔰.besselFrame a) (𝔰.besselFrame a)
  have h_isotropic : star (w ∘ Sum.inl) ⬝ᵥ S.ratMiddle E *ᵥ (w ∘ Sum.inl) = 0 := by
    -- Expand `h_unitary`; the terms pairing `e_i` with `e*_i` vanish by `h_dual`.
    cases a using lastCases with
    | last =>
      have h_dual_zero (i : Fin 𝔰.ϱ) : g.val (Sum.inr (Sum.inr i)) 𝔰.z = 0 := by
        simpa [w, Matrix.one_apply] using h_dual i
      have h_z_one : g.val 𝔰.z 𝔰.z = 1 := by simpa [w, sub_eq_zero] using h_z
      simpa [w, splitGram, middleGram, mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply,
        h_dual_zero, h_z_one] using h_unitary
    | cast a =>
      have h_dual_zero (i : Fin 𝔰.ϱ) : g.val (Sum.inr (Sum.inr i)) (Sum.inl a) = 0 := by
        simpa [w, Matrix.one_apply] using h_dual i
      simpa [w, splitGram, middleGram, mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply,
        h_dual_zero, mul_assoc] using h_unitary
  have h_middle : w ∘ Sum.inl = 0 := S.eq_zero_of_ratMiddle_form_eq_zero _ h_z h_isotropic
  rintro (j | i)
  · exact sub_eq_zero.1 (congr_fun h_middle j)
  · exact sub_eq_zero.1 (h_dual i)

/-- The hermitian products `S.frameProducts` of the frame vector `f_b` with `γ f_a` and with
`γ' f_a` differ, under the embedding `Φ v` at the place `v`, by at most `S.N` times the norm of
`y⁻¹ f_b` times the distance of the `a`-th frame vectors of `γ⁻¹ y` and `γ'⁻¹ y`. -/
lemma norm_Φ_frameProducts_sub_le [S.IsAdmissible]
    (γ γ' : S.G E) (y : 𝔰.G₁) (v : NumberField.InfinitePlace E) (a b : Fin (𝔰.ϱ + 1)) :
    ‖Φ v (S.frameProducts γ b a - S.frameProducts γ' b a)‖ ≤
      S.N * (‖frameVector y b‖ *
        ‖frameVector ((S.ratToInf γ v)⁻¹ * y) a - frameVector ((S.ratToInf γ' v)⁻¹ * y) a‖) := by
  let F (u : S.G E) : EuclideanSpace ℂ 𝔰.BesselIndex := frameVector ((S.ratToInf u v)⁻¹ * y) a
  let t : ℝ := S.realM v ^ (𝔰.ϱ - b) * S.realM v ^ (𝔰.ϱ - a)
  have ht : 1 ≤ |t| := by
    rw [abs_mul, abs_pow, abs_pow]
    bound [S.one_le_abs_realM]
  have hN : (S.N : ℝ) ≠ 0 := mod_cast S.N_prime.ne_zero
  have h_inner (u : S.G E) : inner ℂ (frameVector y b) (toEuclideanLin 𝔰.J₁ (F u)) =
      (t / S.N : ℝ) * Φ v (S.frameProducts u b a) := by
    rw [← realFrameGram_eq_inner, realFrameGram_ratToInf]
  have h_sub : inner ℂ (frameVector y b) (toEuclideanLin 𝔰.J₁ (F γ - F γ')) =
      (t / S.N : ℝ) * Φ v (S.frameProducts γ b a - S.frameProducts γ' b a) := by
    rw [map_sub, inner_sub_right, h_inner, h_inner, map_sub, mul_sub]
  calc _ ≤ |t| * ‖Φ v (S.frameProducts γ b a - S.frameProducts γ' b a)‖ :=
        le_mul_of_one_le_left (norm_nonneg _) ht
    _ = S.N * ‖inner ℂ (frameVector y b) (toEuclideanLin 𝔰.J₁ (F γ - F γ'))‖ := by
        rw [h_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, Nat.abs_cast]
        field
    _ ≤ S.N * (‖frameVector y b‖ * ‖F γ - F γ'‖) := by grw [norm_inner_J₁_le]

/-- For a term `γ` over `(c, s, c')`, the coordinates along the `e_a` of the images `γ f_b` of the
frame vectors `e₁, …, e_ϱ, z` are algebraic integers. -/
lemma termsOver.isIntegral_inl_besselFrame {c c' : S.Classes} {s : S.ResidueGL} {γ : S.G E}
    (hγ : γ ∈ S.termsOver c s c') (a : Fin 𝔰.ϱ) (b : Fin (𝔰.ϱ + 1)) :
    IsIntegral ℤ (γ.val (Sum.inl a) (𝔰.besselFrame b)) := by
  have h_int : (S.translateByClassReps c c' γ).val (Sum.inl a) (𝔰.besselFrame b) ∈ Ô E :=
    termsOver.isIntMatrix_translateByClassReps hγ (Sum.inl a) (𝔰.besselFrame b)
  -- The change to the lattice bases of `c` and `c'` keeps this entry.
  cases b using lastCases <;>
    simpa [coe_translateByClassReps, classBasis, toBesselH, besselLatticeBasis, Matrix.mul_apply,
      Matrix.one_apply] using h_int

/-- The scales `S.basisScale v` that normalise the basis at the place `v`
(`S.realM v ^ (ϱ - a + 1) / √N` on `e_a`, `1 / √N` on `z`) of two frame vectors differ by a factor
of at most `S.b ^ (23 ϱ)`. -/
lemma one_le_pow_mul_norm_basisScale_div [S.IsAdmissible]
    (v : NumberField.InfinitePlace E) (a b : Fin (𝔰.ϱ + 1)) :
    1 ≤ S.b ^ (23 * 𝔰.ϱ) *
      ‖S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame a)‖ := by
  have h_realM : 1 ≤ |S.realM v| := S.one_le_abs_realM v
  have hN : (√S.N : ℂ) ≠ 0 := by simp [S.N_prime.ne_zero]
  have h_quot : ‖S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame a)‖ =
      |S.realM v| ^ (𝔰.ϱ - b) / |S.realM v| ^ (𝔰.ϱ - a) := by
    rw [basisScale_besselFrame, basisScale_besselFrame, div_div_div_cancel_right₀ hN]
    simp
  rw [h_quot, ← mul_div_assoc, one_le_div₀ (by positivity)]
  calc |S.realM v| ^ (𝔰.ϱ - a) ≤ (S.b ^ 23) ^ 𝔰.ϱ := by grw [Nat.sub_le, abs_realM_le]
    _ ≤ S.b ^ (23 * 𝔰.ϱ) * |S.realM v| ^ (𝔰.ϱ - b) := by
        rw [← pow_mul]
        exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans S.one_le_b) _)
          (one_le_pow₀ h_realM)

/-- Let `f = (e₁, …, e_ϱ, z)` be the frame. Suppose that `γ f` and `γ' f` differ only along the
`e_x`, and that `γ f_b` and `γ' f_b` have the same coordinates along `e_x` for `x > a`. Then the
difference of their coordinates along `e_a`, times the ratio of the scales of `f_b` and `e_a` in
the normalised basis at `v` (`S.basisScale v`), is at most the operator norm `‖w y‖` times the
distance of the `b`-th frame vectors of `γ⁻¹ y` and `γ'⁻¹ y`, for every `w` in the unipotent
subgroup `besselU`, whose rows along the `e_a` are unitriangular. -/
lemma norm_Φ_sub_mul_norm_basisScale_div_le {γ γ' : S.G E}
    (h_rows : (frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₂ =
      (frameImage (γ' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₂)
    {a : Fin 𝔰.ϱ} {b : Fin (𝔰.ϱ + 1)}
    (h_later : ∀ x : Fin 𝔰.ϱ, a < x →
      γ.val (Sum.inl x) (𝔰.besselFrame b) = γ'.val (Sum.inl x) (𝔰.besselFrame b))
    {w : 𝔰.G₁} (hw : w ∈ besselU) (y : 𝔰.G₁) (v : NumberField.InfinitePlace E) :
    ‖Φ v (γ.val (Sum.inl a) (𝔰.besselFrame b) - γ'.val (Sum.inl a) (𝔰.besselFrame b))‖ *
        ‖S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame a.castSucc)‖ ≤
      ‖((w * y : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ *
        ‖frameVector ((S.ratToInf γ v)⁻¹ * y) b - frameVector ((S.ratToInf γ' v)⁻¹ * y) b‖ := by
  have h_triangular (x : Fin 𝔰.ϱ) (hx : x ≤ a) :
      w.val (Sum.inl a) (𝔰.besselFrame x.castSucc) = if a = x then 1 else 0 := by
    simpa [Matrix.one_apply] using mem_besselU.1 hw (Sum.inl a) (Sum.inl x) hx
  rw [frameVector_sub_eq_sum h_rows, ← norm_mul]
  refine Eq.trans_le ?_ (norm_sum_le_mul_norm_sum_frameVector castSucc _ (Sum.inl a))
  -- Only the term `x = a` is left in row `a` of `w` applied to the combination.
  rw [Fintype.sum_eq_single a, h_triangular a le_rfl, ite_eq_left rfl, mul_one, Matrix.sub_apply]
  intro x hx
  rcases hx.lt_or_gt with h_lt | h_gt
  · rw [h_triangular x h_lt.le, ite_eq_right hx.symm, mul_zero]
  · rw [Matrix.sub_apply, h_later x h_gt, sub_self, map_zero, zero_mul, zero_mul]

variable [S.IsAdmissible]

/-- **Rigidity of frames.** Let `E` be a CM field and `S` admissible filling data over `E`
(`IsAdmissible`), with parameters `b = S.b` and `N = S.N`, a prime. Let `g` be a term over some
`(d, r, d')`: a rational element with `h_d⁻¹ g h_d'` integral and of reduction `r`, where `h_d` is
the representative of the class `d` (`termsOver`). Let `R ≥ 1`, `n = 𝔰.n` and
`ρ = frameBoxRadius * R` with `frameBoxRadius = b ^ (37 n)`. The frame is `f = (e₁, …, e_ϱ, 𝔰.z)`.
Let `z` be a point at the infinite places such that at every place the infimum `besselLength` of
`‖s z‖ + 1` over the Bessel subgroup is at most `b ^ (6 n + 2) R` and the frame vectors `z⁻¹ f_a`
have norm at most `ρ`. If the frame vectors of `g⁻¹ z` and `z` are at distance less than `(N ρ)⁻¹`
at every place, then `g` fixes the frame, that is, `g f = f`. -/
lemma frameImage_eq_frameImage_one_of_close {g : S.G E} {d : S.Classes} {r : S.ResidueGL}
    {d' : S.Classes}
    (hg : g ∈ S.termsOver d r d') {z : NumberField.InfinitePlace E → 𝔰.G₁} {R : ℝ} (hR : 1 ≤ R)
    (h_box : ∀ v : NumberField.InfinitePlace E, z v ∈ frameBox (S.frameBoxRadius * R))
    (h_size : ∀ v : NumberField.InfinitePlace E, besselLength (z v) ≤ S.b ^ (6 * 𝔰.n + 2) * R)
    (h_close : ∀ (v : NumberField.InfinitePlace E) (a : Fin (𝔰.ϱ + 1)),
      ‖frameVector ((S.ratToInf g v)⁻¹ * z v) a - frameVector (z v) a‖ <
        (S.N * (S.frameBoxRadius * R))⁻¹) :
    frameImage (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) = frameImage 1 := by
  have hb_one : 1 ≤ S.b := S.one_le_b
  have hρ : 0 < S.frameBoxRadius * R := by
    rw [frameBoxRadius]
    positivity
  have hNρ : 0 < S.N * (S.frameBoxRadius * R) := mul_pos (mod_cast S.N_prime.pos) hρ
  let δ (v : NumberField.InfinitePlace E) (a : Fin (𝔰.ϱ + 1)) : ℝ :=
    ‖frameVector ((S.ratToInf g v)⁻¹ * z v) a - frameVector ((S.ratToInf 1 v)⁻¹ * z v) a‖
  -- An integral function whose change from `1` to `g` is at most `N ρ` times the move `δ` of a
  -- frame vector does not change: the change is an algebraic integer of norm `< 1` at all places.
  have h_rigid {f : S.G E → E}
      (h_int : ∀ {c : S.Classes} {s : S.ResidueGL} {c' : S.Classes} {γ : S.G E},
        γ ∈ S.termsOver c s c' → IsIntegral ℤ (f γ))
      (a : Fin (𝔰.ϱ + 1))
      (h_le : ∀ v : NumberField.InfinitePlace E,
        ‖Φ v (f g - f 1)‖ ≤ S.N * (S.frameBoxRadius * R) * δ v a) : f g = f 1 := by
    have h_sub : IsIntegral ℤ (f g - f 1) := (h_int hg).sub (h_int (S.classUnipotent d).one_mem.2)
    refine sub_eq_zero.1 (eq_zero_of_forall_norm_lt_one h_sub fun v ↦ (h_le v).trans_lt ?_)
    rw [← lt_div_iff₀' hNρ]
    simpa [δ] using h_close v a
  have h_gram (a b : Fin (𝔰.ϱ + 1)) : S.frameProducts g b a = S.frameProducts 1 b a := by
    refine h_rigid (fun hγ ↦ isIntegral_frameProducts hγ b a) a fun v ↦ ?_
    grw [norm_Φ_frameProducts_sub_le g 1 (z v), h_box v b, ← mul_assoc]
  have h_lower (i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) (b : Fin (𝔰.ϱ + 1)) :
      frameImage (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (Sum.inr i) b =
        frameImage 1 (Sum.inr i) b :=
    frameImage_inr_eq_of_frameProducts_eq (h_gram b) i
  -- The coordinates along the `e_a` remain: downward induction on `a`.
  refine Matrix.ext (Sum.forall.2 ⟨fun a b ↦ ?_, h_lower⟩)
  induction a using WellFoundedGT.induction with | ind a ih => ?_
  refine h_rigid (f := fun γ ↦ γ.val (Sum.inl a) (𝔰.besselFrame b))
    (fun hγ ↦ termsOver.isIntegral_inl_besselFrame hγ a b) b fun v ↦ ?_
  obtain ⟨w, hw, hw_norm⟩ : ∃ w ∈ besselU,
      ‖((w * z v : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ S.b ^ (6 * 𝔰.n + 2) * R :=
    RealPlace.exists_norm_le_of_besselLength_le (h_size v)
  have h_exp : S.b ^ (23 * 𝔰.ϱ) * S.b ^ (6 * 𝔰.n + 2) ≤ S.frameBoxRadius := by
    rw [frameBoxRadius, ← pow_add]
    gcongr
    linarith only [S.ten_pow_five_le_varrho]
  set ε : ℝ := ‖Φ v (g.val (Sum.inl a) (𝔰.besselFrame b) -
    (1 : S.G E).val (Sum.inl a) (𝔰.besselFrame b))‖
  calc ε ≤ ε * (S.b ^ (23 * 𝔰.ϱ) *
        ‖S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame a.castSucc)‖) :=
        le_mul_of_one_le_right (norm_nonneg _) (one_le_pow_mul_norm_basisScale_div v _ b)
    _ ≤ S.b ^ (23 * 𝔰.ϱ) * (S.b ^ (6 * 𝔰.n + 2) * R * δ v b) := by
        grw [mul_left_comm, norm_Φ_sub_mul_norm_basisScale_div_le (Matrix.ext h_lower) ih hw (z v),
          hw_norm]
    _ = S.b ^ (23 * 𝔰.ϱ) * S.b ^ (6 * 𝔰.n + 2) * R * δ v b := by ring
    _ ≤ S.N * (S.frameBoxRadius * R) * δ v b := by
        grw [h_exp, ← S.N_prime.one_le, Nat.cast_one, one_mul]

variable [HasPrimitiveRoot5040 E]

omit [HasPrimitiveRoot5040 E] in
/-- **Packing of frames.** Let `E` be a CM field, `𝔰` a shape (`𝔰.ϱ` hyperbolic planes), and `S`
admissible data of the filling theorem over `E` (`IsAdmissible`), with parameter `b = S.b`. Let
`n = 𝔰.n`, `R ≥ 1` and `frameBoxRadius = b ^ (37 n)`. The frame is `f = (e₁, …, e_ϱ, z)`, and the
frame vectors of `x ∈ 𝔰.G₁` are the `x⁻¹ f_a` (`frameVector x a`). Let `A` be a set of rational `γ`,
each in `termsOver c s c'` for the given class `c` and some `s`, `c'`. Let `y` be a point of `𝔰.G₁`
at each infinite place. Suppose that for `γ ∈ A` the point `x = (S.ratToInf γ)⁻¹ y` has, at every
place, infimum of `‖s x‖ + 1` over the Bessel subgroup (`besselLength`) at most `b ^ (6 n + 2) R`.
Suppose also that it has frame vectors of norm at most `frameBoxRadius * R` (`frameBox`), and that
the frame vectors of any two of these points differ by an element of the real subspace `V`. Then the
images `γ f` (`frameImage`) of the frame take at most `(b ^ (6 n ^ 2) R ^ 2) ^ dim V` values on
`A`. -/
theorem encard_image_frameImage_le {c : S.Classes} {y : NumberField.InfinitePlace E → 𝔰.G₁}
    {R : ℝ} (hR : 1 ≤ R) {A : Set (S.G E)}
    (h_over : ∀ γ ∈ A, ∃ (s : S.ResidueGL) (c' : S.Classes), γ ∈ S.termsOver c s c')
    (h_size : ∀ γ ∈ A, ∀ v : NumberField.InfinitePlace E,
      besselLength (((S.ratToInf γ)⁻¹ * y) v) ≤ S.b ^ (6 * 𝔰.n + 2) * R)
    (h_box : ∀ γ ∈ A, ∀ v : NumberField.InfinitePlace E,
      ((S.ratToInf γ)⁻¹ * y) v ∈ frameBox (S.frameBoxRadius * R))
    {V : Submodule ℝ
      (NumberField.InfinitePlace E → Fin (𝔰.ϱ + 1) → EuclideanSpace ℂ 𝔰.BesselIndex)}
    (hV : ∀ γ ∈ A, ∀ γ' ∈ A,
      (fun v : NumberField.InfinitePlace E ↦ frameVector (((S.ratToInf γ)⁻¹ * y) v)) -
        (fun v : NumberField.InfinitePlace E ↦ frameVector (((S.ratToInf γ')⁻¹ * y) v)) ∈ V) :
    ((fun γ : S.G E ↦ frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)) '' A).encard ≤
      ENNReal.ofReal ((S.b ^ (6 * 𝔰.n ^ 2) * R ^ 2) ^ finrank ℝ V) := by
  -- With `ρ = frameBoxRadius * R`, terms with different frames give points of `V` at distance at
  -- least `(N ρ)⁻¹` (`frameImage_eq_frameImage_one_of_close`) in the ball of radius `2 ρ`;
  -- `encard_le_of_separated` compares volumes.
  rcases A.eq_empty_or_nonempty with rfl | ⟨γ₀, hγ₀⟩
  · simp
  have hb : 1000 ≤ S.b := S.thousand_le_b
  set ρ : ℝ := S.frameBoxRadius * R with hρ_eq
  have hρ : 0 < ρ := by
    rw [hρ_eq, frameBoxRadius]
    positivity
  have hNρ : 0 < S.N * ρ := mul_pos (mod_cast S.N_prime.pos) hρ
  let frame (p : A) : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) E :=
    frameImage (p.val : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)
  obtain ⟨u, h_image, h_inj⟩ : ∃ u : Set A, frame '' u = range frame ∧ InjOn frame u :=
    exists_image_eq_injOn_of_subset_range le_rfl
  let F (γ : S.G E) (v : NumberField.InfinitePlace E) :
      Fin (𝔰.ϱ + 1) → EuclideanSpace ℂ 𝔰.BesselIndex :=
    frameVector (((S.ratToInf γ)⁻¹ * y) v)
  let f (p : A) : V := ⟨F γ₀ - F p, hV γ₀ hγ₀ p p.property⟩
  have h_sep : u.Pairwise fun p q ↦ (S.N * ρ)⁻¹ ≤ ‖f p - f q‖ := by
    refine fun p hp q hq h_ne ↦ not_lt.1 fun h_close ↦ h_ne (h_inj hp hq ?_)
    obtain ⟨s, d, hp_over⟩ : ∃ (s : S.ResidueGL) (d : S.Classes), p.val ∈ S.termsOver c s d :=
      h_over p p.property
    obtain ⟨s', d', hq_over⟩ : ∃ (s : S.ResidueGL) (d : S.Classes), q.val ∈ S.termsOver c s d :=
      h_over q q.property
    -- The inverse of the term `p⁻¹ q` sends `p⁻¹ y` to `q⁻¹ y`, whose frame vectors are close.
    refine frameImage_inv_mul_eq_iff.1 (frameImage_eq_frameImage_one_of_close
      (termsOver.mul (termsOver.inv hp_over) hq_over) hR
      (h_box p p.property) (h_size p p.property) fun v a ↦ lt_of_le_of_lt ?_ h_close)
    have h_point : (S.ratToInf (p.val⁻¹ * q.val) v)⁻¹ * ((S.ratToInf p.val)⁻¹ * y) v =
        ((S.ratToInf q.val)⁻¹ * y) v := by
      simp [mul_assoc]
    have h_diff : ‖f p - f q‖ = ‖F q - F p‖ := by
      rw [← Submodule.norm_coe, Submodule.coe_sub, ← sub_sub_sub_cancel_left (F p) (F q) (F γ₀)]
    rw [h_point, h_diff]
    exact (norm_le_pi_norm ((F q - F p) v) a).trans (norm_le_pi_norm (F q - F p) v)
  have h_norm (γ : S.G E) (hγ : γ ∈ A) : ‖F γ‖ ≤ ρ :=
    (pi_norm_le_iff_of_nonneg hρ.le).2 fun v ↦ (pi_norm_le_iff_of_nonneg hρ.le).2 (h_box γ hγ v)
  have h_ball (p : A) (_ : p ∈ u) : ‖f p‖ ≤ ρ + ρ :=
    norm_sub_le_of_le (h_norm γ₀ hγ₀) (h_norm p p.property)
  have h_one : 1 ≤ S.b ^ (60 * 𝔰.n) * ρ ^ 2 := by
    have hb_one : 1 ≤ S.b := S.one_le_b
    rw [hρ_eq, frameBoxRadius]
    bound
  have h_ratio : 1 + 2 * (ρ + ρ) / (S.N * ρ)⁻¹ ≤ S.b ^ (6 * 𝔰.n ^ 2) * R ^ 2 :=
    calc 1 + 2 * (ρ + ρ) / (S.N * ρ)⁻¹ = 1 + 4 * (S.N * ρ ^ 2) := by
          rw [div_inv_eq_mul]
          ring
      _ ≤ 5 * (S.b ^ (60 * 𝔰.n) * ρ ^ 2) := by
          grw [IsAdmissible.N_le]
          linarith
      _ ≤ S.b * (S.b ^ (60 * 𝔰.n) * ρ ^ 2) := by
          gcongr
          linarith
      _ = S.b ^ (74 * 𝔰.n + 60 * 𝔰.n + 1) * R ^ 2 := by
          rw [hρ_eq, frameBoxRadius]
          ring
      _ ≤ S.b ^ (6 * 𝔰.n ^ 2) * R ^ 2 := by
          gcongr
          · exact S.one_le_b
          · have h_large : 23 ≤ 𝔰.n := by linarith [S.ten_pow_five_le_varrho]
            nlinarith
  rw [image_eq_range, ← h_image, h_inj.encard_image]
  grw [encard_le_of_separated (inv_pos.2 hNρ) (add_pos hρ hρ).le h_sep h_ball, h_ratio]

/-- **Packing of weights.** Let `E` be a CM field with a primitive 5040-th root of unity and `S`
admissible filling data over `E` (`IsAdmissible`). Let `k p` be classes and `γ p` rational elements
with `p ↦ (k p, γ p)` injective, `w p` weights, `y` a point at the infinite places, `R ≥ 1`,
`b = S.b` and `n = 𝔰.n`. Suppose that for `p` in the support of `w` the element `γ p` is a term
over `(c, s, k p)` (`termsOver`), the point `x_p = (γ p)⁻¹ y` has at every place infimum of
`‖s x_p‖ + 1` over the Bessel subgroup (`besselLength`) at most `b ^ (6 n + 2) R`, and `w p` is at
most `x` times `S.classCutoff (k p)` at `x_p`, a cutoff for the rational unipotent elements fixing
the frame `f = (e₁, …, e_ϱ, z)` times the indicator of the reduced points. If the frame vectors
`x_p⁻¹ f_a` of any two of these points differ by an element of the real subspace `V`, then the
weights add up to at most `(b ^ (6 n ^ 2) R ^ 2) ^ dim V * x`. -/
lemma tsum_le_of_le_classCutoff_mul {c : S.Classes} {s : S.ResidueGL} {α : Type*}
    {y : NumberField.InfinitePlace E → 𝔰.G₁} {x : ℝ≥0∞} {R : ℝ}
    {k : α → S.Classes} {γ : α → S.G E} {w : α → ℝ≥0∞} (hR : 1 ≤ R)
    (h_inj : ∀ {p q : α}, k p = k q → γ p = γ q → p = q)
    (h_over : ∀ p ∈ w.support, γ p ∈ S.termsOver c s (k p))
    (h_size : ∀ p ∈ w.support, ∀ v : NumberField.InfinitePlace E,
      besselLength (((S.ratToInf (γ p))⁻¹ * y) v) ≤ S.b ^ (6 * 𝔰.n + 2) * R)
    (h_le : ∀ p ∈ w.support, w p ≤ S.classCutoff (k p) ((S.ratToInf (γ p))⁻¹ * y) * x)
    {V : Submodule ℝ
      (NumberField.InfinitePlace E → Fin (𝔰.ϱ + 1) → EuclideanSpace ℂ 𝔰.BesselIndex)}
    (hV : ∀ p ∈ w.support, ∀ q ∈ w.support,
      (fun v : NumberField.InfinitePlace E ↦ frameVector (((S.ratToInf (γ p))⁻¹ * y) v)) -
        (fun v : NumberField.InfinitePlace E ↦ frameVector (((S.ratToInf (γ q))⁻¹ * y) v)) ∈ V) :
    ∑' p : α, w p ≤ ENNReal.ofReal ((S.b ^ (6 * 𝔰.n ^ 2) * R ^ 2) ^ finrank ℝ V) * x := by
  -- Colour the terms by their frames. Terms with the same frame differ by an element of
  -- `S.classUnipotent₀`, so their weights are at most `x` times terms of a partition of unity and
  -- add up to at most `x`. The number of frames is bounded by `encard_image_frameImage_le`.
  have h_box (p : α) (hp : p ∈ w.support) (v : NumberField.InfinitePlace E) :
      ((S.ratToInf (γ p))⁻¹ * y) v ∈ frameBox (S.frameBoxRadius * R) := by
    have h_pos : 0 < S.classCutoff (k p) ((S.ratToInf (γ p))⁻¹ * y) * x :=
      (pos_iff_ne_zero.2 hp).trans_le (h_le p hp)
    exact mem_frameBox_of_classCutoff_ne_zero (left_ne_zero_of_mul h_pos.ne') (by positivity)
      (h_size p hp v)
  rw [← tsum_subtype_support]
  generalize w.support = A at *
  let frame (p : A) : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) E :=
    frameImage (γ p : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)
  refine tsum_le_of_encard_range_le
    (R := fun p q : α ↦ k p = k q ∧ (γ p)⁻¹ * γ q ∈ S.classUnipotent₀ (k p)) frame ?_
    (fun p q ↦ termsOver.eq_and_mem_classUnipotent₀ (h_over p p.property) (h_over q q.property))
    fun B hBA p hp h_rel ↦ ?_
  · -- The frames are those of the terms `γ p` with `p` in the support.
    have h_range : range frame =
        (fun g : S.G E ↦ frameImage (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)) '' (γ '' A) := by
      rw [image_image, image_eq_range]
    rw [h_range]
    exact encard_image_frameImage_le hR
      (forall_mem_image.2 fun p hp ↦ ⟨s, k p, h_over p hp⟩) (forall_mem_image.2 h_size)
      (forall_mem_image.2 h_box)
      (forall_mem_image.2 fun p hp ↦ forall_mem_image.2 fun q hq ↦ hV p hp q hq)
  · -- The terms `B` with the same frame: `q ↦ (γ q)⁻¹ * γ p` injects `B` into the unipotent group,
    -- over which the cutoffs sum to one.
    have h_class (q : B) : k q = k p := (h_rel q q.property p hp).1
    have h_mem (q : B) : (γ q)⁻¹ * γ p ∈ S.classUnipotent (k p) := by
      obtain ⟨h_unipotent, -⟩ : (γ q)⁻¹ * γ p ∈ S.classUnipotent₀ (k q) := (h_rel q q.2 p hp).2
      rwa [← h_class q]
    let ι (q : B) : S.classUnipotent (k p) := ⟨(γ q)⁻¹ * γ p, h_mem q⟩
    have hι : ι.Injective := fun q q' h_eq ↦
      Subtype.ext (h_inj ((h_class q).trans (h_class q').symm) (by simpa [ι] using h_eq))
    let β (u : S.classUnipotent (k p)) : ℝ≥0∞ :=
      S.classCutoff (k p) (S.ratToInf u * (S.ratToInf (γ p)⁻¹ * y))
    calc
      ∑' q : B, w q ≤ ∑' q : B, β (ι q) * x := by
        gcongr with q
        simpa [β, ι, h_class q] using h_le q (hBA q.property)
      _ ≤ (∑' u : S.classUnipotent (k p), β u) * x := by
        grw [← tsum_comp_le_tsum_of_injective hι, ENNReal.tsum_mul_right]
      _ = x := by rw [tsum_classCutoff_eq_one, one_mul]

/-- Let `E` be a CM field with a primitive 5040-th root of unity, `S` admissible filling data over
`E` for the shape `𝔰` (`IsAdmissible`), and `c` a class in `S.Classes`. Suppose a point `y`
satisfies `InCut` at every infinite place `v`: `besselLength (y v)`, the infimum of ‖s (y v)‖ + 1
over `s` in the Bessel subgroup, is at most `S.b ^ (6 n + 2)`, where `n = 𝔰.n`. Then some `u` in
`S.classUnipotent c`, the congruence group of rational unipotent elements attached to `c`, has
`S.ratToInf u * y` in `boxedPoints`. The boxed points are those satisfying the same bound that are
reduced: the entries above the diagonal of their triangular matrices of Gram–Schmidt coefficients,
read in the rational frame, lie in a chosen residue domain. -/
lemma exists_classUnipotent_mul_mem_boxedPoints (c : S.Classes)
    {y : NumberField.InfinitePlace E → 𝔰.G₁}
    (h_cut : ∀ v : NumberField.InfinitePlace E, InCut (y v) S.b) :
    ∃ u ∈ S.classUnipotent c, S.ratToInf u * y ∈ S.boxedPoints := by
  -- The cutoffs of the translates add up to `1`, so one of them is not zero.
  obtain ⟨u, hu⟩ : ∃ u : S.classUnipotent c, S.classCutoff c (S.ratToInf u * y) ≠ 0 :=
    CompleteLattice.summable.tsum_ne_zero_iff.1 ((tsum_classCutoff_eq_one c y).trans_ne one_ne_zero)
  -- Left translation by the unipotent `u` keeps `besselLength`.
  obtain ⟨hu_unipotent, -⟩ : u.val ∈ S.classUnipotent c := u.property
  have h_cut_mul (v : NumberField.InfinitePlace E) : InCut ((S.ratToInf u * y) v) S.b :=
    (besselLength_besselS_mul (mem_partialUnitriangularGroup_of_mem_besselU
      (hu_unipotent.ratToInf_mem_agreeWithOneOn v))).trans_le (h_cut v)
  exact ⟨u, u.property, mem_boxedPoints_of_classCutoff_ne_zero hu h_cut_mul⟩

/-- The cutoff of a class is measurable. -/
@[fun_prop]
lemma measurable_classCutoff (c : S.Classes) : Measurable (S.classCutoff c) := by
  obtain ⟨β, hβ, hβ_meas, -⟩ := S.exists_classCutoff_eq_mul c
  rw [hβ]
  exact hβ_meas.mul (isBoxPartitionOfUnity_reducedIndicator c).measurable

end New.Filling

end BoxPartition
end
end

/-!
# The Bessel kernel and the integral of a class cutoff over the real unipotent group

This file proves that the kernel `New.Filling.besselKernel`, the tensor
`besselFn(y) ⊗ besselFn(γ⁻¹ y)^*` of Bessel functions at the infinite places, is continuous.
It bounds the amplitude `New.Filling.amplitude` by the integral of the norms
`New.Filling.amplitudeMajorant`. It then computes the integral of a class cutoff
`S.classCutoff c` over the real unipotent group as `S.unipotentCovolume`. The group is unfolded
one coordinate at a time (`New.Filling.rowCoords`). The integral is then a product of covolumes of
explicit lattices.

## Main definitions and results

* `New.Filling.enorm_amplitude_le`: the norm of the amplitude
  `∫ β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^* dy` is at most the integral of the norm of its integrand.
* `New.Filling.lintegral_classCutoff_eq_unipotentCovolume`: let `E` contain a primitive 5040th
  root of unity and let `S` be admissible. For every class `c` and archimedean point `y`, the
  integral of the cutoff `u ↦ S.classCutoff c (u y)` over the real unipotent group 𝖴_∞, for the
  product of the Haar measures `New.Shape.besselHaar`, is the number `S.unipotentCovolume`.

Notions from other files:
* `New.Filling.besselFn`: for a tuple `i` of coordinates (`New.Filling.BesselCoord`), the product
  over the places `v` of the `i v`-th coordinate of `W side (y v)`.
* `New.Filling.M`, `New.Filling.classUnipotent`: the level M = p₀ p₁, the product of the two primes
  `S.levelPrime`; the rational points u of 𝖴 with h_c⁻¹ u h_c in the principal congruence
  subgroup K(M).
* `New.Shape.Form.besselU`, `New.Shape.Form.besselS`: the group 𝖴 of block upper unitriangular
  isometries, and the Bessel subgroup, which 𝖴 generates together with the unitary group of the
  standard form on κ.
* `New.Filling.IsAdmissible`: the standing hypotheses. The level `sourceLevel` is the preimage of
  K(M), `reduction` is onto, and size inequalities hold between b, M and ϖ, κ_v, N, the second
  moments, the number of Bessel coordinates, an index and the constant `scaledSiegelConst`.
* `New.Filling.unipotentCovolume`: an explicit positive number built from M, N, |κ|, ϱ, the
  discriminant of E and the scales of the frame at the infinite places.
-/

@[expose] public section

/-!
## Continuity of the Bessel kernel and the bound of an amplitude

First facts on the kernel `New.Filling.besselKernel`, the tensor `besselFn(y) ⊗ besselFn(γ⁻¹ y)^*`
of Bessel functions at the infinite places. The amplitude `New.Filling.amplitude`, its integral
against the cutoffs `New.Filling.classCutoff`, is bounded by the integral of the norms
`New.Filling.amplitudeMajorant` (`New.Filling.enorm_amplitude_le`).
-/

section AmplitudeBounds

open Fintype NumberField

namespace New.Filling

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E] {S : Filling E 𝔰} {γ : S.G E}
  {side : FullOrCut}

/-- Each coordinate of the product of the local Bessel functions is continuous on G_∞. -/
@[fun_prop]
lemma continuous_besselFn (i : S.BesselCoord) :
    Continuous fun y : InfinitePlace E → 𝔰.G₁ ↦ S.besselFn side y i := by
  fun_prop [besselFn]

/-- The kernel `y ↦ W(y) ⊗ W(γ⁻¹ y)^*` is continuous on G_∞. -/
@[fun_prop]
lemma continuous_besselKernel : Continuous (S.besselKernel side γ) := by fun_prop [besselKernel]

/-- The norm of `W(y) ⊗ W(γ⁻¹ y)^*` is the product of the norms of the local factors. The factor at
the infinite place `v` is the Bessel function `(S.besselSystem v).besselFn side`, full or cut
according to `side`, and `S.ratToInf γ` is the image in G_∞ of the rational element `γ`. -/
lemma enorm_besselKernel (y : InfinitePlace E → 𝔰.G₁) :
    ‖S.besselKernel side γ y‖ₑ =
      (∏ v : InfinitePlace E, ‖(S.besselSystem v).besselFn side (y v)‖ₑ) *
        ∏ v : InfinitePlace E, ‖(S.besselSystem v).besselFn side (((S.ratToInf γ)⁻¹ * y) v)‖ₑ := by
  -- Square both sides: the sum over pairs of tuples of indices of the squared coordinates factors
  -- as a product over the places, for each of the two tensor factors.
  simp only [eNorm_eq_nnNorm]
  norm_cast
  rw [← sq_eq_sq₀ zero_le zero_le]
  simp [EuclideanSpace.nnNorm_eq, besselKernel, besselFn, mul_pow, ← Finset.prod_pow, sum_prod_type,
    prod_sum, sum_mul_sum]

/-- The norm of the amplitude `∫ β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^* dy` is at most the integral of
the norm of its integrand. -/
lemma enorm_amplitude_le (c c' : S.Classes) :
    ‖S.amplitude side c c' γ‖ₑ ≤ S.amplitudeMajorant side c c' γ := by
  grw [amplitude, MeasureTheory.eNorm_integral_le_lintegral_eNorm, enorm_toReal_smul_le,
    amplitudeMajorant]

end New.Filling

end AmplitudeBounds

/-!
## Integral of a class cutoff over the real unipotent group

`New.Filling.lintegral_classCutoff_eq_unipotentCovolume` computes the covolume of the arithmetic
unipotent group `S.classUnipotent c` of a class `c` in the real unipotent group (a copy of
`New.Shape.Form.besselU` at each infinite place, with the Haar measure `New.Shape.besselHaar`): the
cutoff `S.classCutoff c`, whose translates under `S.classUnipotent c` sum to `1`, has integral
`S.unipotentCovolume`.

The group is unfolded one coordinate at a time by `New.Filling.existsUnique_mul_mem_box`. The basis
is e_a, the middle block, e*_a (`New.Shape.BesselIndex`); the coordinates of a unipotent element are
the free entries of each row e_a (positions `New.RealPlace.IsFreeEntry`) and the imaginary part of
its entry at e*_a. Each coordinate is additive once the earlier ones vanish; the integral is then a
product of covolumes of explicit lattices.
-/

section UnipotentCovolume

namespace New.Filling

open NumberField MeasureTheory Matrix Complex Finset RealPlace Sum ENNReal Function Fintype

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod in
/-- Additivity of an entry in the row of e_a, for x and u in the Bessel unipotent group of G₁. Let
the column j be e*_a or free for the row (`IsFreeEntry`: e_b or e*_b with b > a, or a column of the
middle block). If the free entries of u vanish in the rows e_b with b > a and in the row e_b with
j = e*_b, and the entries of u at (e_b, e*_b), b > a, are real, then the (e_a, j) entry of x·u is
the sum of those of u and x. -/
lemma besselU_mul_apply_eq_add {𝔰 : Shape} (x u : (𝔰.middleGram (1 : ℂ)).besselU) {a : Fin 𝔰.ϱ}
    {j : 𝔰.BesselIndex} (hj : j = eStar a ∨ IsFreeEntry (a, j))
    (h_im : ∀ b : Fin 𝔰.ϱ, a < b →
      ((u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl b) (eStar b)).im = 0)
    (h_zero : ∀ (b : Fin 𝔰.ϱ) (k : 𝔰.BesselIndex), a < b ∨ j = eStar b → IsFreeEntry (b, k) →
      (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl b) k = 0) :
    (↑(x * u) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) j =
      (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) j +
        (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) j := by
  set X : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := ↑x with hX
  set U' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := ↑u with hU'
  -- It suffices that ((X − 1)(U' − 1))(e_a, j) = 0, and this holds term by term.
  suffices h_prod : ((X - 1) * (U' - 1)) (inl a) j = 0 by
    have h_ne : inl a ≠ j := by grind [IsFreeEntry]
    simpa [hX, hU', Matrix.one_apply, h_ne, sub_eq_iff_eq_add', mul_sub, sub_mul] using h_prod
  -- Outside the columns e*_d, the rows of U' that matter below are those of 1.
  have h_row (k l : 𝔰.BesselIndex) (hk : ∀ b, k = inl b → a < b ∨ j = eStar b)
      (hl : ∀ d, l ≠ eStar d) : U' k l = if k = l then 1 else 0 := by
    have h_low (hkl : BesselIndex.level l ≤ BesselIndex.level k) :
        U' k l = if k = l then 1 else 0 := mem_besselU.1 u.property k l hkl
    rcases k with b | i | b <;> rcases l with b' | i' | b' <;>
      simp only [BesselIndex.level, elim_inl, elim_inr] at h_low <;>
      grind [IsFreeEntry]
  refine sum_eq_zero fun k _ ↦ mul_eq_zero.2 ?_
  by_cases hk : BesselIndex.level k ≤ BesselIndex.level (inl a : 𝔰.BesselIndex)
  · exact .inl (sub_eq_zero.2 (mem_besselU.1 x.property _ k hk))
  -- Here k has higher level than e_a, and we show that U'(k, j) is the entry of 1.
  refine .inr (sub_eq_zero.2 ?_)
  have hk_row (b : Fin 𝔰.ϱ) (hb : k = inl b) : a < b ∨ j = eStar b :=
    .inl (by simpa [hb, BesselIndex.level] using hk)
  by_cases! hj_star : ∀ d, j ≠ eStar d
  · exact h_row k j hk_row hj_star
  obtain ⟨c, rfl⟩ := hj_star
  -- In the column e*_c use U' · (J U'ᴴ J) = 1.
  let J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := (𝔰.middleGram (1 : ℂ)).splitGram
  have h_inv : U' * (J * U'ᴴ * J) = 1 := by
    rw [← U.coe_inv IsHermitianInvolution.mul_self u.val]
    exact u.val.val.mul_inv
  have h_unitary : ∑ d, U' k (inl d) * starRingEnd ℂ (U' (inl c) (eStar d)) + U' k (eStar c) =
      if k = eStar c then 1 else 0 := by
    simpa [Matrix.one_apply, J, Shape.Form.splitGram, h_row (inl c), Matrix.mul_apply] using
      congrFun₂ h_inv k (eStar c)
  have h_col (d : Fin 𝔰.ϱ) : U' k (inl d) = if k = inl d then 1 else 0 :=
    h_row k _ hk_row (by simp)
  rcases k with d | i | d
  · -- For c ≠ d one of the two entries is free, hence zero; for c = d the entry is real.
    have h_skew : starRingEnd ℂ (U' (inl c) (eStar d)) + U' (inl d) (eStar c) = 0 := by
      simpa [h_col] using h_unitary
    have had : a < d := by simpa [BesselIndex.level] using hk
    suffices U' (inl d) (eStar c) = 0 by simpa
    grind [conj_eq_iff_im, IsFreeEntry]
  · simpa [h_col] using h_unitary
  · simpa [h_col, Matrix.one_apply] using h_unitary

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. The basis matrix
`classBasis c` of the lattice of the class `c` differs from the identity only in its middle block
`M`, and the generalised index (`genIndex`, the inverse Haar modulus) of `det M` is `N ^ (-f)`.
Here `N = S.N` is the prime `π π̄` of `S` and `f` is the number of infinite places of `E`. -/
lemma exists_classBasis_eq_fromBlocks {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E]
    {𝔰 : Shape} {S : Filling E 𝔰} (c : S.Classes) :
    ∃ M : Matrix 𝔰.MiddleIndex 𝔰.MiddleIndex (𝔸f E),
      (classBasis c).val = fromBlocks 1 0 0 (fromBlocks M 0 0 1) ∧
      genIndex M.det = 1 / S.N ^ numInfPlaces E := by
  -- The witness `M` is read off from the product of the block matrices that define `classBasis c`.
  use ?_, by
    simp [Matrix.fromBlocks_multiply, classBasis, toBesselH, besselLatticeBasis]
    rfl
  -- det M is the determinant of the unitary representative of c over the conjugate of `S.piN`.
  -- Apply `genIndex` to the unitarity relation and to `piN_mul_star`, and take positive square
  -- roots.
  have h_unitary : genIndex c.out.val.val.det = 1 := by
    have h_sq : genIndex c.out.val.val.det ^ 2 = 1 := by
      simpa [← sq] using congrArg (fun A ↦ genIndex (det A))
          (show c.out.val.valᴴ * 1 * c.out.val.val = 1 from
        mem_unitaryGroupOf_iff.1 c.out.property)
    exact (pow_eq_one_iff_of_nonneg (genIndex_pos c.out.val.det).le two_ne_zero).1 h_sq
  have h_norm : genIndex (S.piN : 𝔸f E) = S.N ^ numInfPlaces E := by
    have h_sq : genIndex (S.piN * star S.piN.val : 𝔸f E) = genIndex (S.N : 𝔸f E) :=
      congrArg genIndex S.piN_mul_star
    simpa [genIndex_natCast, ← sq, (genIndex_pos S.piN).le] using h_sq
  simp [h_unitary, h_norm]

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. Let `γ` lie in
`S.classUnipotent c`, the rational unipotent elements that the representative of the class `c`
conjugates into the principal congruence subgroup of level `S.M`. Then the row of γ − 1 at e_a,
divided by `S.M`, has integral coordinates in the basis `classBasis c` of the lattice of `c`. -/
lemma classUnipotent_sub_one_div_M_row_integral {E : Type} [Field E] [CMType E]
    [HasPrimitiveRoot5040 E] {𝔰 : Shape} {S : Filling E 𝔰} {c : S.Classes}
    (γ : S.classUnipotent c) (a : Fin 𝔰.ϱ) (j : 𝔰.BesselIndex) :
    (finAdeleMatrix ((S.M : E)⁻¹ • ((γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) - 1)) (inl a) ᵥ*
      (classBasis c).val) j ∈ Ô E := by
  -- Conjugation by the basis turns γ into `S.translateByClassReps c c γ`, which lies in
  -- `S.principalLevel`.
  let k : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := S.translateByClassReps c c γ
  have h_conj : finAdeleMatrix ((S.M : E)⁻¹ • ((γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) - 1)) *
      (classBasis c).val = (classBasis c).val * S.ideleM⁻¹ • (k - 1) := by
    simp [k, coe_translateByClassReps, Matrix.map_sub, -Nat.cast_mul, sub_mul, mul_assoc, mul_sub]
    rfl
  have h_level : S.translateByClassReps c c γ ∈ S.principalLevel := γ.property.2
  have h_int : (S.ideleM⁻¹ • (k - 1)) (inl a) j ∈ Ô E :=
    (S.principalLevel_eq_unitaryLevel.le h_level).2 _ j
  obtain ⟨M, h_basis, -⟩ := exists_classBasis_eq_fromBlocks c
  rw [← mul_apply_eq_vecMul, h_conj]
  simpa [Matrix.one_apply, h_basis, Matrix.mul_apply] using h_int

attribute [local simp] BesselIndex.level frameScaleSq

attribute [local grind] IsFreeEntry

section FreeBlock

variable {R : Type*} [CommRing R] {𝔰 : Shape} {b : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R}
  {M : Matrix 𝔰.MiddleIndex 𝔰.MiddleIndex R}

open scoped Classical in
/-- If `b` differs from the identity only in its middle block, then its square block on the free
columns (`IsFreeEntry`) of the row e_a has the determinant of `b`. -/
lemma det_toSquareBlockProp_isFreeEntry (hb : b = fromBlocks 1 0 0 (fromBlocks M 0 0 1))
    (a : Fin 𝔰.ϱ) :
    (b.toSquareBlockProp fun j : 𝔰.BesselIndex ↦ IsFreeEntry (a, j)).det = b.det := by
  have h_rest : (b.toSquareBlockProp fun j ↦ ¬IsFreeEntry (a, j)) = 1 := by
    simp [Matrix.one_apply, toSquareBlockProp, ← ext_iff, hb]
  have h_triangular : ∀ i, ¬IsFreeEntry (a, i) → ∀ j, IsFreeEntry (a, j) → b i j = 0 := by
    simp [Matrix.one_apply, hb]
    omega
  simp [b.twoBlockTriangular_det (fun j ↦ IsFreeEntry (a, j)) h_triangular, h_rest]

open scoped Classical in
/-- If `b` differs from the identity only in its middle block, then the entries of `l ᵥ* b` in the
free columns (`IsFreeEntry`) of the row e_a depend only on the entries of `l` in these columns. -/
lemma transpose_toSquareBlockProp_mulVec (hb : b = fromBlocks 1 0 0 (fromBlocks M 0 0 1))
    (a : Fin 𝔰.ϱ) (l : 𝔰.BesselIndex → R) (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) :
    ((b.toSquareBlockProp fun j : 𝔰.BesselIndex ↦ IsFreeEntry (a, j))ᵀ *ᵥ l ∘ Subtype.val) j =
      (l ᵥ* b) j := by
  refine sum_of_injective _ Subtype.val_injective _ _ ?_ fun k ↦ mul_comm _ (l k)
  revert j
  simp [Matrix.one_apply, hb]
  lia

end FreeBlock

section Coordinates

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- The embedding of `S.classUnipotent c` into the real unipotent group 𝖴_∞, the product over the
infinite places of the Bessel unipotent group of G₁. -/
noncomputable def classUnipotentToInf (c : S.Classes) :
    S.classUnipotent c →* InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU :=
  .mk' (fun γ v ↦ ⟨S.ratToInf γ v, γ.property.1.ratToInf_mem_agreeWithOneOn v⟩) (by aesop)

lemma coe_classUnipotentToInf_apply {c : S.Classes} (γ : S.classUnipotent c) (v : InfinitePlace E) :
    (classUnipotentToInf c γ v : 𝔰.G₁) = S.ratToInf γ v := rfl

lemma classUnipotentToInf_injective (c : S.Classes) : Injective (classUnipotentToInf c) := by
  intro _
  simp [funext_iff, coe_classUnipotentToInf_apply, ← SetLike.coe_eq_coe, GeneralLinearGroup.ext_iff,
    (RingHom.injective _).eq_iff]

/-- The free entries (`IsFreeEntry`) of the row e_a of a point `u` of the real unipotent group
𝖴_∞, at all infinite places. -/
def freeRowCoords (u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) (a : Fin 𝔰.ϱ)
    (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) (v : InfinitePlace E) : ℂ :=
  (u v : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) j

/-- The imaginary parts of the entry at (e_a, e*_a) of a point `u` of the real unipotent group
𝖴_∞, at all infinite places. -/
def imRowCoords (u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) (a : Fin 𝔰.ϱ)
    (v : InfinitePlace E) : ℝ :=
  ((u v : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a)).im

/-- The coordinates of a point `u` of the real unipotent group 𝖴_∞, grouped by rows: for each row
e_a, its free entries (`freeRowCoords`) and the imaginary parts of its entry at e*_a
(`imRowCoords`), at all infinite places. -/
def rowCoords (u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) :
    (∀ a : Fin 𝔰.ϱ, {j : 𝔰.BesselIndex // IsFreeEntry (a, j)} → InfinitePlace E → ℂ) ×
      (Fin 𝔰.ϱ → InfinitePlace E → ℝ) :=
  (freeRowCoords u, imRowCoords u)

open scoped Classical in
/-- The map `rowCoords` sends a point of the real unipotent group 𝖴_∞ to the free entries of its
rows e_a and the imaginary parts (real numbers) of its entries at (e_a, e*_a), at all infinite
places of `E`. It carries the product over the infinite places of the Haar measure `besselHaar` to
Lebesgue measure on these coordinates. -/
lemma measurePreserving_rowCoords :
    MeasurePreserving (rowCoords (E := E) (𝔰 := 𝔰)) (.pi fun _ ↦ 𝔰.besselHaar)
      (volume.prod volume) := by
  -- Use `measurePreserving_freeEntries_besselHaar` at each place, then regroup the coordinates by
  -- rows instead of places.
  exact ((((measurePreserving_sigma
    (.symm (.subtypeProdEquivSigmaSubtype fun a j ↦ IsFreeEntry (𝔰 := 𝔰) (a, j)))).comp
      measurePreserving_flip).prod measurePreserving_flip).comp
        (measurePreserving_arrowProdEquivProdArrow ..)).comp
    (measurePreserving_pi _ _ fun _ : InfinitePlace E ↦ measurePreserving_freeEntries_besselHaar)

open scoped Pointwise in
/-- Unfolding. Let `E` contain a primitive 5040th root of unity and let `S` be admissible. The
cutoff `S.classCutoff c` is a measurable function G_∞ → [0, ∞], on tuples `y` of points of `G₁` at
the infinite places, whose left translates under the congruence group `S.classUnipotent c` of
rational unipotent elements add up to `1`. Let `B` be a measurable subset of the real unipotent
group 𝖴_∞ that meets each coset `u Γ` of the image `Γ` of `S.classUnipotent c` under
`classUnipotentToInf c` in exactly one point. Then the integral over 𝖴_∞ of
`u ↦ S.classCutoff c (u y)` is the measure of `B`, both for the product of the Haar measures
`𝔰.besselHaar`. -/
lemma lintegral_classCutoff_eq_measure [HasPrimitiveRoot5040 E] [S.IsAdmissible] (c : S.Classes)
    (y : InfinitePlace E → 𝔰.G₁)
    {B : Set (InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU)} (hB_meas : MeasurableSet B)
    (hB_unique : ∀ u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU,
      ∃! γ : (classUnipotentToInf c).range, u * γ ∈ B) :
    ∫⁻ u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU,
        S.classCutoff c (fun v : InfinitePlace E ↦ u v * y v) ∂(.pi fun _ ↦ 𝔰.besselHaar) =
      Measure.pi (fun _ ↦ 𝔰.besselHaar) B := by
  let Γ : Subgroup (InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) :=
    (classUnipotentToInf c).range
  -- The inverse of `B` is a fundamental domain for the left translations by `Γ`.
  have h_fund : IsFundamentalDomain Γ B⁻¹ (.pi fun _ ↦ 𝔰.besselHaar) :=
    .mk' hB_meas.inv.nullMeasurableSet fun u ↦
      ((Equiv.inv Γ).existsUnique_congr fun γ ↦ by simp [Subgroup.smul_def]).1 (hB_unique u⁻¹)
  have h_sum (u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) :
      ∑' γ : Γ, S.classCutoff c (fun v ↦ (γ • u) v * y v) = 1 := by
    rw [← ((classUnipotentToInf c).ofInjective (classUnipotentToInf_injective c)).tsum_eq,
      ← tsum_classCutoff_eq_one c fun v ↦ u v * y v]
    exact tsum_congr fun γ ↦ congrArg (S.classCutoff c) (funext fun v ↦ mul_assoc ..)
  have : Countable Γ := (classUnipotentToInf c).rangeRestrict_surjective.countable
  have : MeasurableConstSMul Γ (InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) :=
    ⟨fun γ ↦ measurable_const_mul γ.val⟩
  have : SMulInvariantMeasure Γ (InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU)
      (.pi fun _ ↦ 𝔰.besselHaar) :=
    ⟨fun γ s _ ↦ measure_preimage_mul _ γ.val s⟩
  -- The translates of the cutoff add up to 1, and the measure is inversion invariant.
  rw [h_fund.lintegral_eq_tsum'', ← lintegral_tsum (by fun_prop), lintegral_congr h_sum]
  simp [Set.univ_inter]

/-- Let `γ ∈ S.classUnipotent c`. If, at an infinite place `v`, right multiplication by `γ` adds the
(e_a, e*_a) entry of `γ` to that of every unipotent `x`, then the (e_a, e*_a) entry of `γ` divided
by the level `S.M` is skew: the complex conjugation `star` of the CM field `E` changes its sign. -/
lemma star_inv_mul_apply_eStar_eq_neg {c : S.Classes} (γ : S.classUnipotent c) (v : InfinitePlace E)
    (a : Fin 𝔰.ϱ)
    (h_add : ∀ x : (𝔰.middleGram (1 : ℂ)).besselU,
      (↑(x * classUnipotentToInf c γ v) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) =
        (classUnipotentToInf c γ v : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) +
          (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a)) :
    star ((S.M : E)⁻¹ * (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (inl a) (eStar a)) =
      -((S.M : E)⁻¹ * (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (inl a) (eStar a)) := by
  -- Take x = γ⁻¹ = J γᴴ J.
  let J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := (𝔰.middleGram (1 : ℂ)).splitGram
  let Y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := classUnipotentToInf c γ v
  have h_inv : (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) =
      Y (inl a) (eStar a) + (J * Yᴴ * J) (inl a) (eStar a) := by
    rw [← U.coe_inv IsHermitianInvolution.mul_self]
    simpa using h_add (classUnipotentToInf c γ v)⁻¹
  apply (Φ v).injective
  simpa [Matrix.mul_apply, J, Y, coe_classUnipotentToInf_apply, basisScale, Complex.ext_iff,
    self_eq_neg, ← two_mul, Nat.Prime.ne_zero, -ofReal_div] using h_inv

/-- For admissible `S` and `γ ∈ S.classUnipotent c`, the (e_a, e*_a) entry of `γ` is the level
`S.M` times an algebraic integer. -/
lemma isIntegral_inv_mul_apply_eStar [HasPrimitiveRoot5040 E] {c : S.Classes}
    (γ : S.classUnipotent c) (a : Fin 𝔰.ϱ) :
    IsIntegral ℤ
      ((S.M : E)⁻¹ * (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (inl a) (eStar a)) := by
  obtain ⟨M, h_basis, -⟩ := exists_classBasis_eq_fromBlocks c
  -- `using!` identifies the entry of `finAdeleMatrix` with the image under `algebraMap`.
  exact algebraMap_mem_Ô.1
    (by simpa [vecMul_fromBlocks, h_basis] using! classUnipotent_sub_one_div_M_row_integral γ a
          (eStar a))

open scoped Classical in
/-- The volume of the fundamental domain for the free entries (`IsFreeEntry`) of the row e_a, of
which there are 2(ϱ − 1 − a) + k + 1, is `(∏ v, S.M ^ 2 / S.frameScaleSq v a) / volÔ E` to that
power. Here `S.basisScale v j` is the scale of the basis vector `j` at the place `v`,
`S.frameScaleSq v a` is the square of the scale of e_a, `S.M` is the level, and `volÔ E` is
2^r₂/√|disc E|, with r₂ the number of complex places. -/
lemma prod_norm_basisScale_sq_div_eq (S : Filling E 𝔰) (a : Fin 𝔰.ϱ) :
    (∏ v : InfinitePlace E, ‖∏ j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)},
        (S.M : ℂ) / S.basisScale v (inl a) * S.basisScale v j‖ ^ 2) /
        (1 / (S.N : ℝ) ^ numInfPlaces E) /
        volÔ E ^ Fintype.card {j : 𝔰.BesselIndex // IsFreeEntry (a, j)} =
      ((∏ v : InfinitePlace E, (S.M : ℝ) ^ 2 / S.frameScaleSq v a) / volÔ E) ^
        (a.rev + (𝔰.k + 1) + a.rev : ℕ) := by
  -- `↓` splits the product and the count over the three blocks before they are simplified.
  simp [div_pow, prod_pow, tsub_add_eq_tsub_tsub_swap, Finset.prod_mul_distrib,
    Fintype.card_subtype, card_filter, basisScale, ↓prod_sum_type,
    ← prod_subtype _ mem_filter_univ, ↓sum_sum_type, prod_filter, filter_lt_eq_Ioi, mul_pow,
    pow_right_comm _ _ 2, prod_ite]
  field [prod_eq_zero_iff, Nat.Prime.ne_zero]

/-- The number `S.unipotentCovolume` is the product, over the rows e_a, of the covolumes of the
lattice of free entries and of the lattice of imaginary parts at e*_a. -/
lemma unipotentCovolume_eq_prod (S : Filling E 𝔰) :
    S.unipotentCovolume =
      (∏ a : Fin 𝔰.ϱ, ((∏ v : InfinitePlace E, (S.M : ℝ) ^ 2 / S.frameScaleSq v a) / volÔ E) ^
          (a.rev + (𝔰.k + 1) + a.rev : ℕ)) *
        ∏ a : Fin 𝔰.ϱ, ((∏ v : InfinitePlace E, |S.M / S.frameScaleSq v a|) *
          √√|NumberField.discr E|) := by
  have h_exponent (k : ℕ) (a : Fin 𝔰.ϱ) :
      k + 2 * (𝔰.ϱ - a) = a.rev + (k + 1) + a.rev + 1 := by grind
  rw [unipotentCovolume, ← sum_range_reflect, sum_range, frameScaleProd, prod_comm,
    Fin.prod_univ_castSucc]
  simp [div_pow, pow_mul', prod_pow, tsub_add_eq_tsub_tsub_swap, Finset.prod_mul_distrib,
    Finset.sum_add_distrib, mul_pow, abs_div, pow_right_comm _ _ 2,
    pow_succ _ (_ + _), prod_pow_eq_pow_sum, h_exponent]
  field [prod_eq_zero_iff, Nat.Prime.ne_zero]

lemma inl_ne_coe_isFreeEntry (a : Fin 𝔰.ϱ) (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) :
    inl a ≠ j.val := by grind

lemma coe_isFreeEntry_ne_eStar (a : Fin 𝔰.ϱ) (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) :
    j.val ≠ eStar a := by grind

omit [CMType E] in
lemma rowCoords_one : rowCoords (1 : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) = 0 := by
  simp [rowCoords, freeRowCoords, imRowCoords, Prod.ext_iff, funext_iff, inl_ne_coe_isFreeEntry]

omit [CMType E] in
lemma rowCoords_injective : Injective (rowCoords (E := E) (𝔰 := 𝔰)) := by
  intro u u' h_eq
  obtain ⟨h_free, h_im⟩ := Prod.ext_iff.1 h_eq
  exact funext fun v ↦ injective_freeEntries_besselU (Prod.ext
    (funext fun ⟨(a, j), hj⟩ ↦ congrFun₂ (congrFun h_free a) ⟨j, hj⟩ v)
    (funext fun a ↦ congrFun₂ h_im a v))

omit [CMType E] in
/-- If the free entries (`freeRowCoords`) and the imaginary parts of the (e_d, e*_d) entry
(`imRowCoords`) of `u` vanish in every row e_d with d > a, then the free entries of `x * u` in the
row e_a are the sum of those of `u` and of `x`. -/
lemma rowCoords_mul_fst (x : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU)
    {u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU} {a : Fin 𝔰.ϱ}
    (h_free : ∀ d : Fin 𝔰.ϱ, a < d → freeRowCoords u d = 0)
    (h_im : ∀ d : Fin 𝔰.ϱ, a < d → imRowCoords u d = 0) :
    freeRowCoords (x * u) a = freeRowCoords u a + freeRowCoords x a := by
  funext j v
  refine besselU_mul_apply_eq_add (x v) (u v) (.inr j.property) (fun d hd ↦ congrFun (h_im d hd) v)
    fun d k hd hk ↦ congrFun₂ (h_free d ?_) ⟨k, hk⟩ v
  -- If the free column `j` is e*_d, then d > a.
  grind

omit [CMType E] in
/-- If the free entries of `u` vanish in the rows e_d with d ≥ a and the imaginary parts at
(e_d, e*_d) vanish for d > a, then at each place right multiplication by `u` adds the (e_a, e*_a)
entry of `u` to that of `x`. -/
lemma mul_apply_eStar_of_rowCoords {u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU}
    {a : Fin 𝔰.ϱ} (h_free : ∀ d : Fin 𝔰.ϱ, a ≤ d → freeRowCoords u d = 0)
    (h_im : ∀ d : Fin 𝔰.ϱ, a < d → imRowCoords u d = 0) (v : InfinitePlace E)
    (x : (𝔰.middleGram (1 : ℂ)).besselU) :
    (↑(x * u v) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) =
      (u v : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) +
        (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) := by
  refine besselU_mul_apply_eq_add x (u v) (.inl rfl) (fun d hd ↦ congrFun (h_im d hd) v)
    fun d k hd hk ↦ congrFun₂ (h_free d ?_) ⟨k, hk⟩ v
  simpa [le_iff_lt_or_eq] using hd

section Lattices

/-! In this section `c` is a class and e_a is a row; `S` is admissible unless this is omitted. -/

open scoped Classical

variable [HasPrimitiveRoot5040 E]

/-- The transpose of the square block of the lattice basis `classBasis c` on the free columns
(`IsFreeEntry`) of the row e_a, as an invertible matrix. -/
noncomputable def freeBlock (c : S.Classes) (a : Fin 𝔰.ϱ) :
    GL {j : 𝔰.BesselIndex // IsFreeEntry (a, j)} (𝔸f E) :=
  .mk'' ((classBasis c).val.toSquareBlockProp fun j ↦ IsFreeEntry (a, j))ᵀ <| by
    obtain ⟨M, h_basis, -⟩ := exists_classBasis_eq_fromBlocks c
    simp [det_toSquareBlockProp_isFreeEntry h_basis]

lemma freeBlock_mulVec (c : S.Classes) (a : Fin 𝔰.ϱ) (l : 𝔰.BesselIndex → 𝔸f E)
    (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) :
    ((freeBlock c a).val *ᵥ l ∘ Subtype.val) j = (l ᵥ* (classBasis c).val) j := by
  obtain ⟨M, h_basis, -⟩ := exists_classBasis_eq_fromBlocks c
  exact transpose_toSquareBlockProp_mulVec h_basis a l j

lemma genIndex_det_freeBlock (c : S.Classes) (a : Fin 𝔰.ϱ) :
    genIndex (freeBlock c a).val.det = 1 / S.N ^ numInfPlaces E := by
  obtain ⟨M, h_basis, h_index⟩ := exists_classBasis_eq_fromBlocks c
  rw [← h_index, freeBlock, GeneralLinearGroup.val_mk'', det_transpose,
    det_toSquareBlockProp_isFreeEntry h_basis, h_basis]
  simp

omit [HasPrimitiveRoot5040 E] in
variable (S) in
/-- For each `a`, the scales `S.M / S.basisScale v (inl a) * S.basisScale v j` are nonzero for all
infinite places `v` and all `j` with `IsFreeEntry (a, j)`. Here `inl a` indexes the basis vector
e_a. So this family of scales is a unit. -/
lemma isUnit_basisScale_ratio (a : Fin 𝔰.ϱ) :
    IsUnit fun (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) (v : InfinitePlace E) ↦
      (S.M : ℂ) / S.basisScale v (inl a) * S.basisScale v j := by
  simp [Nat.Prime.ne_zero, Pi.isUnit_iff]

/-- The lattice of free entries of the row e_a for the class `c`: the vectors with entries
`S.M / S.basisScale v e_a * S.basisScale v j * Φ v (x j)`, for the rational vectors `x` on the free
columns `j` such that `freeBlock c a *ᵥ x` is integral. Here `S.basisScale v j` is the scale of the
basis vector `j` at the infinite place `v`, and `Φ v` is the chosen complex embedding at `v`. -/
noncomputable def freeLattice (c : S.Classes) (a : Fin 𝔰.ϱ) :
    AddSubmonoid ({j : 𝔰.BesselIndex // IsFreeEntry (a, j)} → InfinitePlace E → ℂ) :=
  (Variety.classLattice (freeBlock c a)⁻¹ ⊥
    (ContinuousLinearEquiv.smulLeft (isUnit_basisScale_ratio S a).unit)).toAddSubmonoid

/-- Let `S` be a filling of shape `𝔰` over the CM field `E` containing a primitive 5040th root of
unity, with `S` admissible. For `c` in `S.Classes`, the lattice `freeLattice c a` of free entries of
the row e_a has a measurable strict fundamental domain. Its volume is `((∏ v, S.M ^
2 / S.frameScaleSq v a) / volÔ E) ^ (a.rev + (𝔰.k + 1) + a.rev)`, the exponent being the number of
free columns. -/
lemma exists_fundamental_domain_freeLattice (c : S.Classes) (a : Fin 𝔰.ϱ) :
    ∃ F : Set ({j : 𝔰.BesselIndex // IsFreeEntry (a, j)} → InfinitePlace E → ℂ),
      MeasurableSet F ∧
      volume.real F = ((∏ v : InfinitePlace E, (S.M : ℝ) ^ 2 / S.frameScaleSq v a) / volÔ E) ^
        (a.rev + (𝔰.k + 1) + a.rev : ℕ) ∧
      ∀ x : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)} → InfinitePlace E → ℂ,
        ∃! l : freeLattice c a, l.val + x ∈ F := by
  obtain ⟨F, hF_meas, hF_vol, hF_fund⟩ :=
    exists_fundamental_domain_classLattice _ (isUnit_basisScale_ratio S a) (freeBlock c a)
  exact ⟨F, hF_meas, by rw [hF_vol, genIndex_det_freeBlock, prod_norm_basisScale_sq_div_eq],
    hF_fund⟩

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. The free entries
(`IsFreeEntry`) of the row e_a of the real image of any `γ ∈ S.classUnipotent c` lie in
`freeLattice c a`, the lattice of rescaled rational vectors `x` on the free columns with
`freeBlock c a *ᵥ x` integral. -/
lemma rowCoords_fst_mem_freeLattice (c : S.Classes) (a : Fin 𝔰.ϱ) (γ : S.classUnipotent c) :
    freeRowCoords (classUnipotentToInf c γ) a ∈ freeLattice c a := by
  let row : 𝔰.BesselIndex → 𝔸f E :=
    finAdeleMatrix ((S.M : E)⁻¹ • ((γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) - 1)) (inl a)
  have h_int (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) :
      ((freeBlock c a).val *ᵥ row ∘ Subtype.val) j ∈ Ô E := by
    simpa only [freeBlock_mulVec] using classUnipotent_sub_one_div_M_row_integral γ a j
  refine ⟨_, torsionClass_eq_zero.2 h_int, ?_⟩
  have hM : (S.M : ℂ) ≠ 0 := by simp [Nat.Prime.ne_zero]
  simp [funext_iff, mul_assoc, freeRowCoords, coe_classUnipotentToInf_apply,
    inl_ne_coe_isFreeEntry, field, -Nat.cast_mul]

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. Fix a class `c` and
a row e_a; its free columns (`IsFreeEntry`) are e_b and e*_b with b > a and the middle block. Let
`l` lie in `freeLattice c a`: its entries are the rescaled complex embeddings of a rational vector
`x` on the free columns with `freeBlock c a *ᵥ x` integral, `freeBlock c a` being the transposed
block of the lattice basis of `c` on these columns. Then `l` is the vector of free entries in the
row e_a of the real image of some `γ ∈ S.classUnipotent c`, for which all coordinates `rowCoords`
vanish in the rows e_d with d > a. -/
lemma exists_rowCoords_fst_eq (c : S.Classes) (a : Fin 𝔰.ϱ)
    {l : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)} → InfinitePlace E → ℂ}
    (hl : l ∈ freeLattice c a) :
    ∃ γ : S.classUnipotent c,
      freeRowCoords (classUnipotentToInf c γ) a = l ∧
      (∀ d : Fin 𝔰.ϱ, a < d → freeRowCoords (classUnipotentToInf c γ) d = 0) ∧
      ∀ d : Fin 𝔰.ϱ, a < d → imRowCoords (classUnipotentToInf c γ) d = 0 := by
  obtain ⟨x, hx, hxl⟩ := hl
  obtain ⟨M, h_basis, -⟩ := exists_classBasis_eq_fromBlocks c
  rw [← extend_comp Subtype.val_injective x 0] at hx hxl
  -- `x`, extended by zero off the free positions, has integral coordinates in the lattice basis.
  have hx_int : algebraMap E (𝔸f E) ∘ extend Subtype.val x 0 ᵥ* (classBasis c).val ∈
      intVectors (Ô E) 𝔰.BesselIndex := by
    intro j
    by_cases hj : IsFreeEntry (a, j)
    · rw [← freeBlock_mulVec c a _ ⟨j, hj⟩]
      exact torsionClass_eq_zero.1 hx _
    · revert j
      simp +contextual [vecMul_fromBlocks, h_basis]
  -- In the rows e_d, γ differs from 1 only in the row e_a and the column e*_a.
  obtain ⟨γ, hγ⟩ :=
    exists_eichler_classUnipotent c a (fun _ hj ↦ extend_val_apply' (g := x) hj) hx_int 0
  refine ⟨γ, ?_, fun d hd ↦ ?_, fun d hd ↦ ?_⟩
  · simp [funext_iff, mul_assoc, ← hxl, freeRowCoords, coe_classUnipotentToInf_apply, basisScale,
      field, inl_ne_coe_isFreeEntry, coe_isFreeEntry_ne_eStar, hγ]
  · have h_col (j : {j : 𝔰.BesselIndex // IsFreeEntry (d, j)}) : j.val ≠ eStar a := by grind
    simp [funext_iff, freeRowCoords, coe_classUnipotentToInf_apply, inl_ne_coe_isFreeEntry, hγ,
      h_col, hd.ne']
  · simp [funext_iff, imRowCoords, coe_classUnipotentToInf_apply, hγ, hd.ne']

/-- Let `E` contain a primitive 5040th root of unity. Suppose that at the place `v`, right
multiplication by the image `classUnipotentToInf c γ v` of `γ ∈ S.classUnipotent c`
adds its (e_a, e*_a) entry to that of every `x` in `besselU`. Then the imaginary parts of this entry
of `classUnipotentToInf c γ` at all places form a vector `(S.M / S.frameScaleSq w a * Im Φ_w(s))_w`
for an integer `s` of `E` with `star s = -s` (`imSkewLattice`). -/
lemma rowCoords_snd_mem_imSkewLattice (c : S.Classes) (a : Fin 𝔰.ϱ) (γ : S.classUnipotent c)
    (v : InfinitePlace E)
    (h_add : ∀ x : (𝔰.middleGram (1 : ℂ)).besselU,
      (↑(x * classUnipotentToInf c γ v) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) =
        (classUnipotentToInf c γ v : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) +
          (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a)) :
    imRowCoords (classUnipotentToInf c γ) a ∈
      imSkewLattice fun w : InfinitePlace E ↦ S.M / S.frameScaleSq w a := by
  -- The entry of γ at (e_a, e*_a) is `S.M` times s, with s integral and skew.
  refine ⟨IsIntegralClosure.mk' (𝓞 E) _ (isIntegral_inv_mul_apply_eStar γ a), RingOfIntegers.ext ?_,
    ?_⟩
  · simpa using star_inv_mul_apply_eStar_eq_neg γ v a h_add
  · have hM : (S.M : ℝ) ≠ 0 := by simp [Nat.Prime.ne_zero]
    simp [pow_mul', funext_iff, imRowCoords, coe_classUnipotentToInf_apply, basisScale, field,
      -Nat.cast_mul, -ofReal_div]

/-- Let `E` contain a primitive 5040th root of unity. Fix a class `c` and a row e_a. Let `l` be a
vector `(S.M / S.frameScaleSq v a * Im Φ_v(s))_v` for an integer `s` of `E` with `star s = -s`
(`imSkewLattice`). Then `l` is the vector of imaginary parts at (e_a, e*_a) of the real image of
some `γ ∈ S.classUnipotent c` whose other coordinates `rowCoords` vanish. -/
lemma exists_rowCoords_snd_eq (c : S.Classes) (a : Fin 𝔰.ϱ) {l : InfinitePlace E → ℝ}
    (hl : l ∈ imSkewLattice fun v : InfinitePlace E ↦ S.M / S.frameScaleSq v a) :
    ∃ γ : S.classUnipotent c,
      imRowCoords (classUnipotentToInf c γ) a = l ∧
      freeRowCoords (classUnipotentToInf c γ) = 0 ∧
      ∀ d : Fin 𝔰.ϱ, d ≠ a → imRowCoords (classUnipotentToInf c γ) d = 0 := by
  obtain ⟨s, hs, hsl⟩ := hl
  obtain ⟨γ, hγ⟩ := exists_eichler_classUnipotent c a (l := 0) (by simp) (by simp) ⟨s, hs⟩
  refine ⟨γ, ?_, ?_, fun d hd ↦ ?_⟩
  · simp [pow_mul', funext_iff, mul_assoc, ← hsl, imRowCoords, coe_classUnipotentToInf_apply,
      basisScale, field, hγ, -ofReal_div]
  · funext d j v
    by_cases hd : d = a
    · subst hd
      simp [freeRowCoords, coe_classUnipotentToInf_apply, inl_ne_coe_isFreeEntry,
        coe_isFreeEntry_ne_eStar, hγ]
    · simp [freeRowCoords, coe_classUnipotentToInf_apply, inl_ne_coe_isFreeEntry, hγ, hd]
  · simp [funext_iff, imRowCoords, coe_classUnipotentToInf_apply, hγ, hd]

end Lattices

open scoped Classical in
/-- Let `S` be admissible and `c` a class, with finite adelic representative h_c. The group
`S.classUnipotent c` consists of the rational unipotent `γ` with h_c⁻¹ γ h_c in the principal
congruence subgroup of level `S.M`; let `Γ` be its image in the real unipotent group 𝖴_∞. In the
basis e₁, …, e_ϱ, middle block, e*₁, …, e*_ϱ, the map `rowCoords` sends a point of 𝖴_∞ to the free
entries of each row e_a and the imaginary parts of the entries at (e_a, e*_a), at all infinite
places. There are measurable sets `F a` and `F' a` such that each coset `u Γ` has exactly one point
with coordinates in the box over them. The product of the volumes of all `F a` and `F' a` is the
explicit number `S.unipotentCovolume`, which does not depend on `c`. -/
lemma exists_box_existsUnique_rowCoords_mem [HasPrimitiveRoot5040 E]
    (c : S.Classes) :
    ∃ (F : ∀ a : Fin 𝔰.ϱ, Set ({j : 𝔰.BesselIndex // IsFreeEntry (a, j)} → InfinitePlace E → ℂ))
      (F' : Fin 𝔰.ϱ → Set (InfinitePlace E → ℝ)),
      (∀ a : Fin 𝔰.ϱ, MeasurableSet (F a)) ∧
      (∀ a : Fin 𝔰.ϱ, MeasurableSet (F' a)) ∧
      (∏ a : Fin 𝔰.ϱ, volume.real (F a)) * ∏ a : Fin 𝔰.ϱ, volume.real (F' a) = S.unipotentCovolume ∧
      ∀ u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU,
        ∃! γ : (classUnipotentToInf c).range,
          rowCoords (u * γ.val) ∈ Set.univ.pi F ×ˢ Set.univ.pi F' := by
  -- The group translates the coordinates by explicit lattices, in a triangular way. So
  -- `existsUnique_mul_mem_box` applies to fundamental domains of these lattices.
  choose F hF_meas hF_vol hF_fund using exists_fundamental_domain_freeLattice c
  choose F' hF'_meas hF'_vol hF'_fund using fun a : Fin 𝔰.ϱ ↦
    exists_fundamental_domain_im_skew (fun v ↦ S.M / S.frameScaleSq v a)
      (by simp [Nat.Prime.ne_zero])
  refine ⟨F, F', hF_meas, hF'_meas, ?_, fun u ↦ ?_⟩
  · simp only [hF_vol, hF'_vol, unipotentCovolume_eq_prod]
  -- The coordinates as one family: `inl a` for the free entries of the row e_a, `inr a` for the
  -- imaginary parts. The type names the additive group in which each coordinate lies.
  let coord (u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) : ∀ i : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ,
      (Sum.elim (fun a ↦ .of ({j // IsFreeEntry (a, j)} → InfinitePlace E → ℂ))
        (fun _ ↦ .of (InfinitePlace E → ℝ)) i : AddGrpCat) :=
    Sum.rec (freeRowCoords u) (imRowCoords u)
  have h_coord_inj : coord.Injective := fun _ _ h ↦
    rowCoords_injective (Prod.ext (funext (congrFun h <| inl ·)) (funext (congrFun h <| inr ·)))
  have h_coord_one_inl (d : Fin 𝔰.ϱ) : coord 1 (inl d) = 0 :=
    congrFun (congrArg Prod.fst rowCoords_one) d
  have h_coord_one_inr (d : Fin 𝔰.ϱ) : coord 1 (inr d) = 0 :=
    congrFun (congrArg Prod.snd rowCoords_one) d
  -- The last rows come first; in one row the free entries come before the imaginary part.
  let deg : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ → ℕ := Sum.elim (fun a ↦ 2 * a.rev) fun a ↦ 2 * a.rev + 1
  -- What the vanishing of the coordinates of lower degree means, row by row.
  have h_low_inl {x : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU} {a : Fin 𝔰.ϱ}
      (h_low : ∀ i, deg i < deg (inl a) → coord x i = coord 1 i) :
      (∀ d, a < d → freeRowCoords x d = 0) ∧ ∀ d, a < d → imRowCoords x d = 0 :=
    ⟨fun d hd ↦ (h_low (inl d) (by grind)).trans (h_coord_one_inl d),
      fun d hd ↦ (h_low (inr d) (by grind)).trans (h_coord_one_inr d)⟩
  have h_low_inr {x : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU} {a : Fin 𝔰.ϱ}
      (h_low : ∀ i, deg i < deg (inr a) → coord x i = coord 1 i) :
      (∀ d, a ≤ d → freeRowCoords x d = 0) ∧ ∀ d, a < d → imRowCoords x d = 0 :=
    ⟨fun d hd ↦ (h_low (inl d) (by grind)).trans (h_coord_one_inl d),
      fun d hd ↦ (h_low (inr d) (by grind)).trans (h_coord_one_inr d)⟩
  refine (existsUnique_congr fun _ ↦ Sum.forall).1
    (existsUnique_mul_mem_box deg coord h_coord_inj (classUnipotentToInf c).range
      (Sum.rec (freeLattice c)
        fun a ↦ (imSkewLattice fun v ↦ S.M / S.frameScaleSq v a).toAddSubmonoid)
      (Sum.rec F F') (Sum.rec hF_fund hF'_fund) ?attained ?in_lattice ?translates u)
  case translates =>
    rintro γ (a | a) h_low x
    · obtain ⟨h_free, h_im⟩ := h_low_inl h_low
      exact rowCoords_mul_fst x h_free h_im
    · obtain ⟨h_free, h_im⟩ := h_low_inr h_low
      exact funext fun v ↦ congrArg im (mul_apply_eStar_of_rowCoords h_free h_im v (x v))
  case in_lattice =>
    rintro ⟨_, γ, rfl⟩ (a | a) h_low
    · exact rowCoords_fst_mem_freeLattice c a γ
    · obtain ⟨h_free, h_im⟩ := h_low_inr h_low
      exact rowCoords_snd_mem_imSkewLattice c a γ Classical.ofNonempty
        (mul_apply_eStar_of_rowCoords h_free h_im _)
  case attained =>
    rintro (a | a) l hl
    · obtain ⟨γ, hγ, h_free, h_im⟩ := exists_rowCoords_fst_eq c a hl
      refine ⟨⟨_, γ, rfl⟩, hγ, ?_⟩
      rintro (d | d) h_ne h_deg
      · exact (h_free d (by grind)).trans (h_coord_one_inl d).symm
      · exact (h_im d (by grind)).trans (h_coord_one_inr d).symm
    · obtain ⟨γ, hγ, h_free, h_im⟩ := exists_rowCoords_snd_eq c a hl
      refine ⟨⟨_, γ, rfl⟩, hγ, ?_⟩
      rintro (d | d) h_ne -
      · exact (congrFun h_free d).trans (h_coord_one_inl d).symm
      · exact (h_im d fun hd ↦ h_ne (congrArg inr hd)).trans (h_coord_one_inr d).symm

end Coordinates

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. For every class `c`
and archimedean point `y`, the integral of the cutoff `u ↦ S.classCutoff c (u y)` over the real
unipotent group 𝖴_∞, for the product of the Haar measures `New.Shape.besselHaar`, is the number
`S.unipotentCovolume`, which depends neither on `c` nor on `y`.

A case of the covolume computation for Heisenberg radicals, with a fixed product Haar measure in
place of Tate's self-dual measures. -/
lemma lintegral_classCutoff_eq_unipotentCovolume {E : Type} [Field E] [CMType E]
    [HasPrimitiveRoot5040 E] {𝔰 : Shape} (S : Filling E 𝔰) (c : S.Classes) [S.IsAdmissible]
    (y : InfinitePlace E → 𝔰.G₁) :
    ∫⁻ u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU,
        S.classCutoff c (fun v : InfinitePlace E ↦ u v * y v) ∂(.pi fun _ ↦ 𝔰.besselHaar) =
      .ofReal S.unipotentCovolume := by
  classical
  -- The integral is the measure of a box that meets each coset of `S.classUnipotent c` once.
  obtain ⟨F, F', hF_meas, hF'_meas, h_vol, h_unique⟩ := exists_box_existsUnique_rowCoords_mem c
  have h_box : MeasurableSet (Set.univ.pi F ×ˢ Set.univ.pi F') :=
    (MeasurableSet.univ_pi hF_meas).prod (.univ_pi hF'_meas)
  have h_real : ((∏ a, volume (F a)) * ∏ a, volume (F' a)).toReal = S.unipotentCovolume := by
    simp [← h_vol, measureReal_def]
  rw [lintegral_classCutoff_eq_measure c y (measurePreserving_rowCoords.measurable h_box) h_unique,
    measurePreserving_rowCoords.measure_preimage h_box.nullMeasurableSet, Measure.prod_prod,
    volume_pi_pi, volume_pi_pi, ← h_real, ofReal_toReal]
  -- An infinite measure would have real value 0, but `S.unipotentCovolume` is positive.
  exact fun h_top ↦ S.unipotentCovolume_pos.ne (by simpa [h_top] using h_real)

end New.Filling

end UnipotentCovolume
end
end

/-!
# Sums of amplitudes over blocks

This file proves convergence, change of weight and the behaviour under the Bessel subgroup of the
block sums `S.amplitudeSum side T c s c'`. The block is the sum, over the rational `γ ∈ T` that lie
over `(c, s, c')` (`New.Filling.termsOver`), of the amplitudes
`∫ β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^* dy`. Here `β_c = S.classCutoff c` is a cutoff for the group
`S.classUnipotent c`, the argument `side : FullOrCut` selects the full or the cut Bessel function
`W`, and `ν = New.Filling.unipotentCovolume`. The listed results assume that `S` is admissible
(`New.Filling.IsAdmissible`).

## Main definitions and results

* `New.Filling.exists_tsum_classCutoff_mul_prod_enorm_le`,
  `New.Filling.tsum_amplitudeMajorant_lt_top`,
  `New.Filling.tsum_lintegral_enorm_besselKernel_sub_cut_le`: the sums are bounded and converge
  absolutely, and cutting `W` changes them little.
* `New.Filling.hasSum_amplitudeSum_of_cutoff`: for stable `T`, any measurable weight with orbit sums
  `1` may replace the product of the cutoffs `S.classCutoff c` and `S.classCutoff c'`.
* `New.Filling.amplitudeSum_mul_mul_inv`, `New.Filling.amplitudeSum_besselU_mul`: moving a block by
  the Bessel subgroup; the unipotent part acts through the character `New.Filling.unipotentChar`.
* `New.Filling.amplitudeSum_eq_zero_of_not_agrees`: the block of a stable set vanishes unless `s`
  agrees.
* `New.Filling.amplitudeSum_besselS_one_eq_ite`: for the full Bessel function only, at `s = 1` the
  Bessel subgroup contributes `S.unipotentCovolume` times the identity if `c = c'`, and `0`
  otherwise.

Notions from other files:
* `New.Filling.latticeStabilizer`, `New.Filling.reduction`, `New.Filling.ResidueGL`: the group K of
  integral elements of the finite adelic unitary group, and its reduction modulo the chosen places
  above p₀ and p₁, with values in the product `ResidueGL` of the general linear groups over the
  residue fields. The kernel is K(M) = `New.Filling.principalLevel`.
* `New.Filling.termsOver`: a rational `γ` is a term over `(c, s, c')` if h_c⁻¹ γ h_c' lies in K and
  has reduction `s`; here h_c = `S.classRep c` represents the class `c`.
* `New.Shape.Form.besselU`, `New.Shape.Form.besselS`, `New.Filling.IsStable`: the group 𝖴 of block
  upper unitriangular isometries, and the Bessel subgroup, which 𝖴 generates together with the
  unitary group of the standard form on κ; a set `T` of rational elements is stable if
  multiplication on either side by rational points of 𝖴 does not affect membership in `T`.
* `New.Filling.IsAdmissible`: the standing hypotheses. The level `sourceLevel` is the preimage of
  K(M), `reduction` is onto, and size inequalities hold between b, M and ϖ, κ_v, N, the second
  moments, the number of Bessel coordinates, an index and the constant `scaledSiegelConst`.
* `New.Filling.classUnipotent`, `New.Filling.unipotentCovolume`: the rational points u of 𝖴 with
  h_c⁻¹ u h_c in the principal congruence subgroup K(M); an explicit positive number built from M,
  N, |κ|, ϱ, the discriminant of E and the scales of the frame at the infinite places.

## Relation to the literature

The results on block sums belong to two steps: the bound for the second moment of the Poincaré
series (`New.Spanning.Unfolding.Moments`, which lists related work) and the bound for degenerate
terms and pairs with different links (`New.Spanning.RemainingTerms.Sum`).
-/

@[expose] public section

section AmplitudeSums

open NumberField MeasureTheory Measure Complex ENNReal Finset Fintype

namespace New.Filling

section GeneralBlocks

variable {E : Type} [Field E] [CMType E]
  {𝔰 : Shape} {S : Filling E 𝔰} {side : FullOrCut}

/-! ### Preliminaries on cutoffs, the kernel, sums by layers and majorants -/

/-- The rational points of the Bessel subgroup `besselS` form a stable set: multiplying on either
side by rational points of `besselU` does not affect membership in `besselS`. -/
lemma isStable_besselS : S.IsStable (S.ratMiddle E).besselS := by
  simp +contextual [IsStable, mul_mem_cancel_right, mul_mem_cancel_left]

/-- The quotient measure of a unimodular Haar measure `ν` on a subgroup of `G₁` is σ-finite, as its
density, a chosen cutoff for `ν`, is almost everywhere finite. -/
instance sigmaFinite_orbitMeasure
    {A : Subgroup 𝔰.G₁} (ν : Measure A) [h : RealPlace.IsUnimodularHaar ν] :
    SigmaFinite (orbitMeasure ν (@volume 𝔰.G₁ _)) :=
  have h_cutoff : IsCutoff ν (chosenCutoff ν) := Classical.epsilon_spec h.out
  .withDensity_of_ne_top (h_cutoff.ae_cutoff_lt_top.mono fun _ hy ↦ hy.ne)

/-- Unfolding at several places: if `ν` is a unimodular Haar measure on a subgroup of `G₁`, then
`(x, u) ↦ (u v * x v)_v` carries the product of the quotient measures and of the copies of `ν` to
the Haar measure on `P → G₁`, for a finite type `P`. -/
lemma measurePreserving_pi_orbitMeasure {A : Subgroup 𝔰.G₁} (ν : Measure A)
    [RealPlace.IsUnimodularHaar ν] {P : Type*} [Fintype P] :
    MeasurePreserving (fun p : (P → 𝔰.G₁) × (P → A) ↦ (fun v : P ↦ (p.2 v).val) * p.1)
      ((Measure.pi fun _ : P ↦ orbitMeasure ν (volume : Measure 𝔰.G₁)).prod
        (Measure.pi fun _ : P ↦ ν))
      (volume : Measure (P → 𝔰.G₁)) :=
  (measurePreserving_pi _ _ fun _ : P ↦
      measurePreserving_orbitMeasure (ν := ν) (μ := (volume : Measure 𝔰.G₁))).comp
    (measurePreserving_arrowProdEquivProdArrow ..).symm

/-- Let `g j`, for `j` in a countable index set `J`, be measurable functions with values in a
finite-dimensional space `EuclideanSpace ℂ I`, and let the sum over `j` of the integrals of `‖g j‖`
be finite. Then the `i`-th coordinate of `∑' j, ∫ g j` equals the integral of `∑' j, (g j x) i`. -/
lemma tsum_integral_apply {X J I : Type*} [MeasurableSpace X] {μ : Measure X} [Countable J]
    [Fintype I] {g : J → X → EuclideanSpace ℂ I} (hg_meas : ∀ j : J, Measurable (g j))
    (hg_fin : ∑' j : J, ∫⁻ x : X, ‖g j x‖ₑ ∂μ < ∞) (i : I) :
    (∑' j : J, ∫ x : X, g j x ∂μ) i = ∫ x : X, ∑' j : J, g j x i ∂μ := by
  -- Take the `i`-th coordinate through the sum and the integral, then exchange the two.
  have h_integrable (j) : Integrable (g j) μ := ⟨by fun_prop, (le_tsum _ j).trans_lt hg_fin⟩
  have h_coord_fin : ∑' j, ∫⁻ x, ‖g j x i‖ₑ ∂μ < ∞ := by grw [PiLp.eNorm_apply_le, hg_fin]
  have h_summable : Summable fun j ↦ ∫ x, g j x ∂μ :=
    .of_eNorm (ne_of_lt (by grw [eNorm_integral_le_lintegral_eNorm, hg_fin]))
  calc
    _ = ∑' j, (∫ x, g j x ∂μ) i := (EuclideanSpace.proj i).map_tsum h_summable
    _ = ∑' j, ∫ x, g j x i ∂μ := tsum_congr fun j ↦ eval_integral_piLp (h_integrable j).eval_piLp i
    _ = ∫ x, ∑' j, g j x i ∂μ := (integral_tsum (by fun_prop) h_coord_fin.ne).symm

/-- The group `S.ResidueGL`, a finite product of general linear groups over finite residue fields,
is finite. -/
noncomputable instance : Fintype S.ResidueGL := .ofFinite _

/-- The Bessel function `S.besselFn side` is invariant under left translation by the image at the
infinite places of the group `S.classUnipotent c` of a class `c`. -/
lemma besselFn_mul_of_mem_classUnipotent {c : S.Classes} (u : S.classUnipotent c)
    (y : InfinitePlace E → 𝔰.G₁) :
    S.besselFn side (S.ratToInf u * y) = S.besselFn side y := by
  -- `besselFn` changes by the inverse of `unipotentChar`. The conjugate of `u` by the
  -- representative of `c` lies in `S.principalLevel`, so the character has at `u` its value at `1`.
  obtain ⟨hu_besselU, hu_level⟩ := u.property
  have h_char : S.unipotentChar (S.ratToFin u) = 1 := by
    simp_all [unipotentChar_eq_of_mem_principalLevel (one_mem _) _ c.out]
  simp [besselFn_ratToInf_mul hu_besselU, h_char]

/-- Let `besselKernel γ y` be the tensor `besselFn(y) ⊗ besselFn(γ⁻¹ y)^*` of Bessel functions. Let
`u`, `u'` lie in the unipotent subgroup `besselU` of `(S.ratMiddle E).G`, the group `S.G E` of
rational isometries of the form with middle Gram matrix `S.ratMiddle E`. Then the kernel at
`(u γ u'⁻¹, u y)` is `ψ(u)⁻¹ ψ(u')` times the kernel at `(γ, y)`. Here `ψ` is `unipotentChar`
applied to the finite-adelic images `ratToFin u` and `ratToFin u'`. -/
lemma besselKernel_besselU_mul {u u' : (S.ratMiddle E).G} (hu : u ∈ besselU) (hu' : u' ∈ besselU)
    (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁) :
    S.besselKernel side (u * γ * u'⁻¹) (S.ratToInf u * y) =
      ((S.unipotentChar (S.ratToFin u))⁻¹ * S.unipotentChar (S.ratToFin u')) •
        S.besselKernel side γ y := by
  -- Apply `besselFn_ratToInf_mul` in both factors; conjugation inverts the second character, of
  -- modulus `1`.
  ext p
  have h_arg : (S.ratToInf (u * γ * u'⁻¹))⁻¹ * (S.ratToInf u * y) =
      S.ratToInf u' * ((S.ratToInf γ)⁻¹ * y) := by
    simp [mul_assoc]
  have h_conj : starRingEnd ℂ (S.unipotentChar (S.ratToFin u')) =
      (S.unipotentChar (S.ratToFin u'))⁻¹ := by simp [unipotentChar, ← inv_eq_conj]
  simp only [besselKernel, PiLp.smul_apply, h_arg, besselFn_ratToInf_mul hu,
    besselFn_ratToInf_mul hu']
  simp [h_conj]
  ring

/-- Unfolding: let each `w v` be measurable and left invariant under the unipotent group `besselU`
(`FixesLeft`). Then the integral of the cutoff `S.classCutoff c y` of the class `c` times
`∏ v, w v (y v)` is the covolume `S.unipotentCovolume` times the product of the integrals of the
`w v` for the quotient measure `besselQuotMeasure` on `𝖴 \ G₁`. -/
lemma lintegral_classCutoff_mul_prod [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {w : InfinitePlace E → 𝔰.G₁ → ℝ≥0∞} (hw_meas : ∀ v : InfinitePlace E, Measurable (w v))
    (hw_inv : ∀ v : InfinitePlace E, besselU.FixesLeft (w v)) (c : S.Classes) :
    ∫⁻ y : InfinitePlace E → 𝔰.G₁, S.classCutoff c y * ∏ v : InfinitePlace E, w v (y v) =
      .ofReal S.unipotentCovolume *
        ∏ v : InfinitePlace E, ∫⁻ y : 𝔰.G₁, w v y ∂besselQuotMeasure := by
  -- Unfold `y = u * x` with `u` in the product of the groups `besselU`: the factors `w v` do not
  -- see `u`, and the integral of `S.classCutoff c` over `u` is `S.unipotentCovolume`.
  calc
    _ = ∫⁻ x, (∫⁻ u, S.classCutoff c (fun v ↦ ((u v).val : 𝔰.G₁) * x v)
          ∂(Measure.pi fun _ : InfinitePlace E ↦ 𝔰.besselHaar)) *
        ∏ v, w v (x v) ∂(Measure.pi fun _ : InfinitePlace E ↦ besselQuotMeasure) := by
      simp (disch := measurability) [lintegral_prod, Pi.mul_def, hw_inv, lintegral_mul_const,
        ← (measurePreserving_pi_orbitMeasure 𝔰.besselHaar).lintegral_comp]
    _ = .ofReal S.unipotentCovolume *
        ∫⁻ x, ∏ v, w v (x v) ∂(.pi fun _ : InfinitePlace E ↦ besselQuotMeasure) := by
      simp only [lintegral_classCutoff_eq_unipotentCovolume]
      exact lintegral_const_mul' _ _ ofReal_ne_top
    _ = _ := by simp (disch := measurability) [TauCeti.lintegral_fintype_prod_eq_prod]

/-- Summation by layers. Let `u ≥ 1` and `K ≥ 0`. If the points with `u p ≤ R` have total weight at
most `(K R ^ e) ^ d` for all `R ≥ 1`, then the weighted sum of `u p ^ (-i)` is at most `2 K ^ d` as
soon as `2 e d < i`. -/
lemma tsum_mul_inv_pow_le_of_layers {α : Type*} {w : α → ℝ≥0∞} {u : α → ℝ} {K : ℝ} {e d i : ℕ}
    (hu : ∀ p : α, 1 ≤ u p) (hK : 0 ≤ K)
    (h_count : ∀ R ≥ (1 : ℝ), ∑' p : α, {p : α | u p ≤ R}.indicator w p ≤ .ofReal ((K * R ^ e) ^ d))
    (hi : 2 * (e * d) < i) :
    ∑' p : α, w p * .ofReal ((u p)⁻¹ ^ i) ≤ .ofReal (2 * K ^ d) := by
  -- Apply the layer cake bound to the measure with mass `w p` at the point `p`.
  let : MeasurableSpace α := ⊤
  let μ : Measure α := Measure.count.withDensity w
  have hi_real : 2 * ((e : ℝ) * d) < i := mod_cast hi
  have h_ed : 0 ≤ (e : ℝ) * d := by positivity
  have h_vol (R : ℝ) (hR : R ≥ 1) : μ {p | u p ≤ R} ≤ .ofReal ((K * R ^ e) ^ d) * 1 := by
    rw [withDensity_apply _ MeasurableSpace.measurableSet_top,
      ← lintegral_indicator MeasurableSpace.measurableSet_top, lintegral_count, mul_one]
    exact h_count R hR
  calc
    _ = ∫⁻ p, .ofReal (u p ^ (-i : ℝ)) ∂μ := by
      rw [lintegral_withDensity_eq_lintegral_mul _ measurable_from_top measurable_from_top,
        lintegral_count]
      simp only [Pi.mul_apply, Real.rpow_neg (zero_le_one.trans (hu _)), Real.rpow_natCast, inv_pow]
    _ ≤ .ofReal (K ^ d * 2) * 1 :=
      lintegral_rpow_neg_le_of_measure_sublevel_le measurable_from_top hu hK h_vol (by linarith)
        (by linarith)
    _ = .ofReal (2 * K ^ d) := by rw [mul_one, mul_comm]

variable (S) in
/-- The product over the infinite places `v` of the scaled lengths of `y v`, each of which is
`max 1 (besselLength (y v) / b ^ (6 n))`. Here `besselLength x` is the infimum of `‖s x‖ + 1` over
`s` in the Bessel subgroup `besselS`, `b = S.b` and `n = ϱ + 1`. -/
noncomputable def scaledBesselLengthProd (y : InfinitePlace E → 𝔰.G₁) : ℝ :=
  ∏ v : InfinitePlace E, scaledBesselLength (y v) S.b

/-- The product of the scaled lengths over the infinite places is at least one. -/
lemma one_le_scaledBesselLengthProd (y : InfinitePlace E → 𝔰.G₁) : 1 ≤ S.scaledBesselLengthProd y :=
  Finset.one_le_prod₀ fun v _ ↦ one_le_scaledBesselLength (y v) S.b

/-- The scaled length at one infinite place is at most the product of all of them. -/
lemma scaledBesselLength_le_scaledBesselLengthProd (y : InfinitePlace E → 𝔰.G₁)
    (v : InfinitePlace E) :
    scaledBesselLength (y v) S.b ≤ S.scaledBesselLengthProd y := by
  rw [scaledBesselLengthProd, ← mul_prod_erase _ _ (mem_univ v)]
  exact le_mul_of_one_le_right (zero_le_one.trans (one_le_scaledBesselLength ..))
    (Finset.one_le_prod₀ fun w _ ↦ one_le_scaledBesselLength (y w) S.b)

/-- Let `S` be admissible, `T` a set of rational elements, `c` a class and `s` an element of the
finite group `S.ResidueGL`. Write `γ⁻¹ y` for `(S.ratToInf γ)⁻¹ * y`. Over all classes `d` and all
`γ` in `T ∩ S.termsOver c s d`, the cutoff `S.classCutoff d` at `γ⁻¹ y` times
`S.scaledBesselLengthProd (γ⁻¹ y) ^ (-(r ^ 3 * f))` adds up to at most `2 b ^ (12 n ^ 3 r f)`. Here
`b = S.b` is the real size parameter of `S`, `f` is the number of infinite places, `n = ϱ + 1` and
`r` is the rank of `G₁`. -/
lemma tsum_classCutoff_mul_inv_pow_le [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) (y : InfinitePlace E → 𝔰.G₁) :
    ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)), S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
        .ofReal ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)) ≤
      .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E)) := by
  -- Sort the terms by the product `S.scaledBesselLengthProd` of the scaled lengths of `γ⁻¹ y` over
  -- the infinite places. Packing in the space of tuples of vectors, of real dimension `2 n r f`,
  -- bounds the total weight of the terms for which this product is at most `R`.
  have hb : 1 ≤ S.b := S.one_le_b
  let z (p : Σ d : S.Classes, ↥(T ∩ S.termsOver c s d)) : InfinitePlace E → 𝔰.G₁ :=
    (S.ratToInf p.2)⁻¹ * y
  let weight (p : Σ d : S.Classes, ↥(T ∩ S.termsOver c s d)) : ℝ≥0∞ :=
    S.classCutoff p.1 (z p)
  have h_dim : Module.finrank ℝ (⊤ : Submodule ℝ
      (InfinitePlace E → Fin (𝔰.ϱ + 1) → EuclideanSpace ℂ 𝔰.BesselIndex)) =
      2 * 𝔰.n * 𝔰.r * numInfPlaces E := by
    simp [finrank_top, Module.finrank_pi_fintype, finrank_real_of_complex]
    ring
  have h_count (R : ℝ) (hR : R ≥ 1) :
      ∑' p, {p | S.scaledBesselLengthProd (z p) ≤ R}.indicator weight p ≤
        .ofReal ((S.b ^ (6 * 𝔰.n ^ 2) * R ^ 2) ^ (2 * 𝔰.n * 𝔰.r * numInfPlaces E)) := by
    have h_size (p) (hp : p ∈ ({p | S.scaledBesselLengthProd (z p) ≤ R}.indicator weight).support)
        (v : InfinitePlace E) : besselLength (z p v) ≤ S.b ^ (6 * 𝔰.n + 2) * R := by
      have h_scaled : besselLength (z p v) / S.b ^ (6 * 𝔰.n) ≤ R :=
        (le_max_right ..).trans ((scaledBesselLength_le_scaledBesselLengthProd (z p) v).trans
          (Set.mem_of_indicator_ne_zero (s := {p | S.scaledBesselLengthProd (z p) ≤ R}) hp))
      grw [(div_le_iff₀' (by positivity)).1 h_scaled,
        pow_le_pow_right₀ hb (Nat.le_add_right (6 * 𝔰.n) 2)]
    rw [← h_dim, ← mul_one (ENNReal.ofReal _)]
    exact tsum_le_of_le_classCutoff_mul (y := y)
      (k := fun p : Σ d, ↥(T ∩ S.termsOver c s d) ↦ p.1) (γ := fun p ↦ p.2) hR Sigma.subtype_ext
      (fun p _ ↦ p.2.property.2) h_size
      (fun p _ ↦ (Set.indicator_le_self _ _ p).trans_eq (mul_one _).symm)
      fun _ _ _ _ ↦ Submodule.mem_top
  -- The exponent `r ^ 3 f` exceeds four times the dimension, as `8 n < r ^ 2`.
  have h_exp : 2 * (2 * (2 * 𝔰.n * 𝔰.r * numInfPlaces E)) < 𝔰.r ^ 3 * numInfPlaces E := by
    have hϱ := S.ten_pow_five_le_varrho
    have hr : 2 * 𝔰.ϱ + 1 ≤ 𝔰.r := by simp; lia
    have h_rank : 8 * 𝔰.n < 𝔰.r ^ 2 := by nlinarith
    nlinarith [show 0 < 𝔰.r * numInfPlaces E by positivity]
  calc
    _ = ∑' p, weight p *
        .ofReal ((S.scaledBesselLengthProd (z p))⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)) :=
      (tsum_sigma' _).symm
    _ ≤ .ofReal (2 * (S.b ^ (6 * 𝔰.n ^ 2)) ^ (2 * 𝔰.n * 𝔰.r * numInfPlaces E)) :=
      tsum_mul_inv_pow_le_of_layers (fun p ↦ one_le_scaledBesselLengthProd (z p)) (by positivity)
        h_count h_exp
    _ = _ := by rw [← pow_mul]; ring_nf

/-- Let `besselKernel γ y` be the tensor `besselFn(y) ⊗ besselFn(γ⁻¹ y)^*` of Bessel functions.
Where the kernel chosen by `side` differs from the cut kernel, the full and the cut Bessel function
differ at some place, at `y` or at `γ⁻¹ y`; so the product of the scaled lengths
(`scaledBesselLengthProd`) of the two points is at least the size parameter `S.b`. -/
lemma le_scaledBesselLengthProd_mul {γ : S.G E} {y : InfinitePlace E → 𝔰.G₁}
    (h_ne : S.besselKernel side γ y ≠ S.besselKernel .cut γ y) :
    S.b ≤ S.scaledBesselLengthProd y * S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y) := by
  by_contra h_near
  have h_eq (z : InfinitePlace E → 𝔰.G₁) (hz : ¬S.b ≤ S.scaledBesselLengthProd z)
    (v : InfinitePlace E) :
      (S.besselSystem v).besselFn .cut (z v) = (S.besselSystem v).besselFn .full (z v) := by
    by_contra h_cut
    have h_size : S.b ≤ scaledBesselLength (z v) S.b :=
      le_scaledBesselLength (by linarith [S.thousand_le_b])
        ((S.besselSystem v).isCutPair.lt_besselLength_of_ne _ h_cut)
    exact hz (h_size.trans (scaledBesselLength_le_scaledBesselLengthProd z v))
  have h_one_y : 1 ≤ S.scaledBesselLengthProd y := one_le_scaledBesselLengthProd y
  have h_one_z : 1 ≤ S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y) :=
    one_le_scaledBesselLengthProd _
  have h_left : ∀ v,
      (S.besselSystem v).besselFn .cut (y v) = (S.besselSystem v).besselFn .full (y v) :=
    h_eq y fun h ↦ h_near (h.trans (le_mul_of_one_le_right (by linarith) h_one_z))
  have h_right : ∀ v, (S.besselSystem v).besselFn .cut (((S.ratToInf γ)⁻¹ * y) v) =
      (S.besselSystem v).besselFn .full (((S.ratToInf γ)⁻¹ * y) v) :=
    h_eq _ fun h ↦ h_near (h.trans (le_mul_of_one_le_left (by linarith) h_one_y))
  -- For the full kernel this gives equality; for the cut kernel there is nothing to prove.
  cases side with
  | full => exact h_ne (by simp only [besselKernel, besselFn, h_left, h_right])
  | cut => exact h_ne rfl

section Majorant

variable {w : InfinitePlace E → 𝔰.G₁ → ℝ≥0∞} {a : InfinitePlace E → ℝ≥0∞}

/-- Let `hw` say that at each infinite place `v` the function `w v` is a decay majorant
(`IsDecayMajorant`, with constants `S.b` and `a v`) of the Bessel functions
`(S.besselSystem v).besselFn`. That is, `w v` bounds their norms times the scaled length
`max 1 (besselLength x / b ^ (6 n))` to the power `3 * r ^ 3 * f`. Here `b = S.b`, `n = ϱ + 1`, `r`
is the rank of `G₁` and `f = numInfPlaces E`. Then for every `y`, the product over `v` of the norms
`‖besselFn side (y v)‖`, times `scaledBesselLengthProd y` to the power
`r ^ 3 * f + 2 * (r ^ 3 * f)`, is at most the product over `v` of `w v (y v)`. -/
lemma pow_mul_pow_mul_prod_enorm_le
    (hw : ∀ v : InfinitePlace E,
      IsDecayMajorant S.b (numInfPlaces E) (S.besselSystem v).besselFn (w v) (a v))
    (y : InfinitePlace E → 𝔰.G₁) :
    ENNReal.ofReal (S.scaledBesselLengthProd y) ^ (𝔰.r ^ 3 * numInfPlaces E) *
      (ENNReal.ofReal (S.scaledBesselLengthProd y) ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)) *
        ∏ v : InfinitePlace E, ‖(S.besselSystem v).besselFn side (y v)‖ₑ) ≤
      ∏ v : InfinitePlace E, w v (y v) := by
  have h_nonneg (v : InfinitePlace E) : 0 ≤ scaledBesselLength (y v) S.b :=
    zero_le_one.trans (one_le_scaledBesselLength ..)
  calc
    _ = ∏ v, ENNReal.ofReal (scaledBesselLength (y v) S.b ^ (3 * 𝔰.r ^ 3 * numInfPlaces E)) *
        ‖(S.besselSystem v).besselFn side (y v)‖ₑ := by
      simp only [scaledBesselLengthProd, ofReal_prod_of_nonneg fun v _ ↦ h_nonneg v,
        ofReal_pow (h_nonneg _), prod_mul_distrib, prod_pow]
      ring
    _ ≤ _ := prod_le_prod fun v _ ↦ (hw v).pow_mul_enorm_le side (y v)

/-- At each infinite place `v` let the function `w v` be a decay majorant (`IsDecayMajorant`) of the
Bessel functions: it bounds their norm times the scaled length to the power `3 * r ^ 3 * f`, where
`r` is the rank of `G₁` and `f` the number of infinite places. Then the product over the places of
the norms, times the product `scaledBesselLengthProd` of the scaled lengths to the power
`2 * (r ^ 3 * f)`, is at most the product of the `w v`. -/
lemma pow_mul_prod_enorm_le_majorant
    (hw : ∀ v : InfinitePlace E,
      IsDecayMajorant S.b (numInfPlaces E) (S.besselSystem v).besselFn (w v) (a v))
    (y : InfinitePlace E → 𝔰.G₁) :
    ENNReal.ofReal (S.scaledBesselLengthProd y) ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)) *
      ∏ v : InfinitePlace E, ‖(S.besselSystem v).besselFn side (y v)‖ₑ ≤
      ∏ v : InfinitePlace E, w v (y v) := by
  refine (le_mul_of_one_le_left' (one_le_pow₀ ?_)).trans (pow_mul_pow_mul_prod_enorm_le hw y)
  exact one_le_ofReal.2 (one_le_scaledBesselLengthProd y)

/-- At each infinite place `v` let the function `w v`, bounded by the constant `a v`, be a decay
majorant (`IsDecayMajorant`) of the Bessel functions: it bounds their norm times the scaled length
to the power `3 * r ^ 3 * f`, where `r` is the rank of `G₁` and `f` the number of infinite places.
Then the product of the norms, times the product `scaledBesselLengthProd` of the scaled lengths to
the power `2 * (r ^ 3 * f)`, is at most the product of the `a v` times `scaledBesselLengthProd` to
the power `-(r ^ 3 * f)`. -/
lemma pow_mul_prod_enorm_le_bound
    (hw : ∀ v : InfinitePlace E,
      IsDecayMajorant S.b (numInfPlaces E) (S.besselSystem v).besselFn (w v) (a v))
    (y : InfinitePlace E → 𝔰.G₁) :
    ENNReal.ofReal (S.scaledBesselLengthProd y) ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)) *
        ∏ v : InfinitePlace E, ‖(S.besselSystem v).besselFn side (y v)‖ₑ ≤
      (∏ v : InfinitePlace E, a v) *
        .ofReal ((S.scaledBesselLengthProd y)⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)) := by
  have h_pos : 0 < S.scaledBesselLengthProd y := one_pos.trans_le (one_le_scaledBesselLengthProd y)
  -- Move the power `-(r ^ 3 * f)` to the left side.
  rw [mul_comm (∏ v, a v), ofReal_pow (inv_pos.2 h_pos).le, ofReal_inv_of_pos h_pos,
    ← ENNReal.inv_pow, ← mul_le_iff_le_inv (pow_ne_zero _ (ofReal_pos.2 h_pos).ne')
      (pow_ne_top ofReal_ne_top)]
  exact (pow_mul_pow_mul_prod_enorm_le hw y).trans (prod_le_prod fun v _ ↦ (hw v).le_bound (y v))

/-- At each infinite place `v` there are a Bessel function W and its cut W♭, of bounded support
modulo the Bessel subgroup. Let the function `w v`, bounded by the constant `a v`, be a decay
majorant (`IsDecayMajorant`): it bounds the norms of W and W♭ times the scaled length
`max 1 (besselLength / b ^ (6 n))` to the power `3 * r ^ 3 * f`. Then the kernel
`W(y) ⊗ W(γ⁻¹ y)^*`, built from W or W♭ as `side` says, and the kernel built from W♭ differ by at
most `2 * b ^ (-(2 * (r ^ 3 * f)))` times the product of the `w v` at `y`, the product of the `a v`
and the product of the scaled lengths of `γ⁻¹ y` (`scaledBesselLengthProd`) to the power
`-(r ^ 3 * f)`. Here `b = S.b`, `n = ϱ + 1`, `r` is the rank of `G₁` and `f` the number of infinite
places. -/
lemma enorm_besselKernel_sub_cut_le
    (hw : ∀ v : InfinitePlace E,
      IsDecayMajorant S.b (numInfPlaces E) (S.besselSystem v).besselFn (w v) (a v))
    (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁) :
    ‖S.besselKernel side γ y - S.besselKernel .cut γ y‖ₑ ≤
      (ENNReal.ofReal (S.b ^ (2 * (𝔰.r ^ 3 * numInfPlaces E))))⁻¹ *
        (2 * ((∏ v : InfinitePlace E, w v (y v)) * ((∏ v : InfinitePlace E, a v) *
          .ofReal ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^
            (𝔰.r ^ 3 * numInfPlaces E))))) := by
  rcases eq_or_ne (S.besselKernel side γ y) (S.besselKernel .cut γ y) with h_eq | h_ne
  · simp [h_eq]
  have hb : 0 < S.b := one_pos.trans_le S.one_le_b
  set z : InfinitePlace E → 𝔰.G₁ := (S.ratToInf γ)⁻¹ * y
  let gain : ℝ≥0∞ := .ofReal (S.b ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)))
  -- The cut acts at one of the two points, so the spare powers of the scaled lengths pay for the
  -- gain.
  have h_gain : gain ≤ ENNReal.ofReal (S.scaledBesselLengthProd y) ^
    (2 * (𝔰.r ^ 3 * numInfPlaces E)) *
      ENNReal.ofReal (S.scaledBesselLengthProd z) ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)) := by
    have h_far : S.b ≤ S.scaledBesselLengthProd y * S.scaledBesselLengthProd z :=
      le_scaledBesselLengthProd_mul h_ne
    rw [← mul_pow, ← ofReal_mul (zero_le_one.trans (one_le_scaledBesselLengthProd y)),
      ← ofReal_pow (hb.le.trans h_far)]
    exact ofReal_le_ofReal (pow_le_pow_left₀ hb.le h_far _)
  have h_kernel (τ : FullOrCut) : gain * ‖S.besselKernel τ γ y‖ₑ ≤ (∏ v, w v (y v)) *
      ((∏ v, a v) * .ofReal ((S.scaledBesselLengthProd z)⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E))) := by
    grw [h_gain, enorm_besselKernel, mul_mul_mul_comm, pow_mul_prod_enorm_le_majorant hw,
      pow_mul_prod_enorm_le_bound hw]
  rw [← mul_le_iff_le_inv (by positivity) ofReal_ne_top]
  grw [eNorm_sub_le, mul_add, h_kernel, h_kernel, two_mul]

end Majorant

variable [S.IsAdmissible]

/-- For 12 n³ + 500 ≤ k < r and f ≥ 1, the exponent 12 n³ r f + 1 + 400 r² f + 2 k f of the
losses in the tail bound plus the saving k³ f is at most the gain 2 r³ f. -/
lemma cut_exponent_le {n r k f : ℕ} (hk : 12 * n ^ 3 + 500 ≤ k) (hr : k + 1 ≤ r) (hf : 1 ≤ f) :
    12 * n ^ 3 * r * f + 1 + 400 * r ^ 2 * f + 2 * k * f + k ^ 3 * f ≤ 2 * (r ^ 3 * f) := by
  have h_count : 12 * n ^ 3 * r ≤ r ^ 2 := by grw [sq, show 12 * n ^ 3 ≤ r by lia]
  have h_dim : 2 * k + 1 ≤ r ^ 2 := by nlinarith
  have h_small : 402 * r ^ 2 ≤ r ^ 3 := by grw [pow_succ' r 2, show 402 ≤ r by lia]
  have h_cube : k ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left (by lia) 3
  calc
    _ ≤ (12 * n ^ 3 * r + 400 * r ^ 2 + (2 * k + 1) + k ^ 3) * f := by linarith
    _ ≤ 2 * r ^ 3 * f := Nat.mul_le_mul_right f (by lia)
    _ = _ := mul_assoc ..

/-- Let `E` contain a primitive 5040th root of unity, let `S` be admissible and let `T` be a set of
rational elements. Sum, over all classes `d` and all `γ ∈ T` that are terms over `(c, s, d)`
(`termsOver`), the cutoff of `d` at `γ⁻¹ y` times `A` times the product of the scaled lengths of
`γ⁻¹ y` (`scaledBesselLengthProd`) to the power `-(r ^ 3 * f)`. The sum is at most
`A * 2 b ^ (12 n ^ 3 r f)`. Here `b = S.b` is the size parameter of `S`, `f` is the number of
infinite places, `n = ϱ + 1` and `r` is the rank of the hermitian space of `G₁`. -/
lemma tsum_classCutoff_mul_const_mul_inv_pow_le [HasPrimitiveRoot5040 E]
    (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) (A : ℝ≥0∞) (y : InfinitePlace E → 𝔰.G₁) :
    ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)), S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
        (A * .ofReal ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^
          (𝔰.r ^ 3 * numInfPlaces E))) ≤
      A * .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E)) := by
  simp only [mul_left_comm _ A, ENNReal.tsum_mul_left]
  exact mul_le_mul_right (tsum_classCutoff_mul_inv_pow_le T c s y) _

/-- Let `S` be admissible and `T` a set of rational elements. At each infinite place `v` let `w v`
be a decay majorant of the Bessel functions (`IsDecayMajorant`); what is used is that `w v` is
measurable and left invariant under the unipotent group `besselU`, and that the constant `a v` times
the integral of `w v` over `𝖴 \ G₁` is at most `b ^ (400 r ^ 2)` times the dimension of the value
space. Let `d` run over all classes and `γ` over the terms of `T` over `(c, s, d)`. Then the sum of
the integrals of `β_c(y) β_d(γ⁻¹ y)` times the product of the `w v` at `y`, the product of the `a v`
and `scaledBesselLengthProd (γ⁻¹ y)` to the power `-(r ^ 3 * f)` is at most `ν * 2 b ^ (12 n ^ 3 r
f) * b ^ (400 r ^ 2 f) * card S.BesselCoord`. Here `β_c = S.classCutoff c`,
`ν = S.unipotentCovolume`, `b` is the size parameter of `S`, `f` is the number of infinite places,
`n = ϱ + 1` and `r` is the rank of `G₁`. -/
lemma tsum_lintegral_classCutoff_mul_majorant_le [HasPrimitiveRoot5040 E]
    (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL)
    {w : InfinitePlace E → 𝔰.G₁ → ℝ≥0∞} {a : InfinitePlace E → ℝ≥0∞}
    (hw : ∀ v : InfinitePlace E,
      IsDecayMajorant S.b (numInfPlaces E) (S.besselSystem v).besselFn (w v) (a v)) :
    ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)), ∫⁻ y : InfinitePlace E → 𝔰.G₁,
        S.classCutoff c y * S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
          ((∏ v : InfinitePlace E, w v (y v)) * ((∏ v : InfinitePlace E, a v) * .ofReal
            ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)))) ≤
      .ofReal S.unipotentCovolume * .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E)) *
        (.ofReal (S.b ^ (400 * 𝔰.r ^ 2)) ^ numInfPlaces E * card S.BesselCoord) := by
  -- Multiply the sum over the terms by `β_c * ∏ v, w v`, integrate, and unfold over `besselU`.
  let countBound : ℝ≥0∞ := .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E))
  have hw_meas (v : InfinitePlace E) : Measurable (w v) := (hw v).measurable
  have hw_inv (v : InfinitePlace E) : besselU.FixesLeft (w v) :=
    fun u hu ↦ (hw v).fixesLeft u (mem_partialUnitriangularGroup_of_mem_besselU hu)
  have h_size : Measurable S.scaledBesselLengthProd := by
    fun_prop [scaledBesselLengthProd, scaledBesselLength]
  calc
    _ = ∫⁻ y, S.classCutoff c y * (∏ v, w v (y v)) * ∑' (d : S.Classes)
        (γ : ↥(T ∩ S.termsOver c s d)), S.classCutoff d ((S.ratToInf γ)⁻¹ * y) * ((∏ v, a v) *
          .ofReal ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^
            (𝔰.r ^ 3 * numInfPlaces E))) := by
      simp (disch := fun_prop) only [← ENNReal.tsum_mul_left, lintegral_tsum,
        mul_mul_mul_comm _ _ (classCutoff ..)]
    _ ≤ ∫⁻ y, S.classCutoff c y * (∏ v, w v (y v)) * ((∏ v, a v) * countBound) := by
      grw [tsum_classCutoff_mul_const_mul_inv_pow_le]
    _ = .ofReal S.unipotentCovolume * countBound * ∏ v, a v * ∫⁻ y, w v y ∂besselQuotMeasure := by
      rw [lintegral_mul_const _ (by fun_prop), lintegral_classCutoff_mul_prod hw_meas hw_inv,
        mul_comm _ countBound, mul_mul_mul_comm, mul_comm (univ.prod _), ← prod_mul_distrib]
    _ ≤ _ := by
      grw [prod_le_prod fun v _ ↦ (hw v).bound_mul_lintegral_le]
      simp [countBound, prod_mul_distrib, Fintype.card_pi]

/-- For admissible `S`, twice the product of `ν`, `2 b ^ (12 n ^ 3 r f)`, `b ^ (400 r ^ 2 f)` and
the number `card S.BesselCoord` of Bessel coordinates, divided by `b ^ (2 r ^ 3 f)`, is at most
`ν b ^ (-k³ f) / 2`. Here `b` is the size parameter of `S`, `f` the number of infinite places,
`ν = S.unipotentCovolume`, `k = 𝔰.k`, `n = ϱ + 1` and `r` is the rank of `G₁`. -/
lemma inv_pow_mul_unipotentCovolume_mul_card_le :
    (ENNReal.ofReal (S.b ^ (2 * (𝔰.r ^ 3 * numInfPlaces E))))⁻¹ * 2 *
      (.ofReal S.unipotentCovolume * .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E)) *
        (.ofReal (S.b ^ (400 * 𝔰.r ^ 2)) ^ numInfPlaces E * card S.BesselCoord)) ≤
      .ofReal (S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) := by
  have hν : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb : 1 ≤ S.b := S.one_le_b
  have hk : 12 * 𝔰.n ^ 3 + 500 ≤ 𝔰.k := by
    have h_large : 1000 * (2 * 𝔰.ϱ + 2) ^ 3 ≤ 𝔰.k := S.pow_le_k.trans' (by gcongr; simp)
    rw [show 2 * 𝔰.ϱ + 2 = 2 * 𝔰.n by ring, mul_pow] at h_large
    linarith [Nat.one_le_pow 3 𝔰.n 𝔰.ϱ.succ_pos]
  have h_rank : 𝔰.k + 1 ≤ 𝔰.r := by simp +arith
  have h_pow : S.b * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E) *
      (S.b ^ (400 * 𝔰.r ^ 2)) ^ numInfPlaces E * S.b ^ (2 * 𝔰.k * numInfPlaces E) *
        S.b ^ (𝔰.k ^ 3 * numInfPlaces E) ≤ S.b ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)) := by
    simp only [← pow_mul, ← pow_add, ← pow_succ']
    exact pow_le_pow_right₀ hb (cut_exponent_le hk h_rank Fintype.card_pos)
  rw [le_ofReal_iff_toReal_le (by finiteness) (by positivity)]
  -- Clear the denominators and cancel `unipotentCovolume`; the constant `8` is at most `b`, and the
  -- number of coordinates is at most `b ^ (2 k f)`.
  simp (disch := positivity) only [toReal_mul, toReal_inv, toReal_pow, toReal_ofReal,
    toReal_ofNat, toReal_natCast, fieldLe]
  change (2 : ℝ) ^ 3 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E) *
      (S.b ^ (400 * 𝔰.r ^ 2)) ^ numInfPlaces E * (card S.BesselCoord : ℝ) *
        S.b ^ (𝔰.k ^ 3 * numInfPlaces E) ≤ S.b ^ (2 * (𝔰.r ^ 3 * numInfPlaces E))
  have h_card : (card S.BesselCoord : ℝ) ≤ S.b ^ (2 * 𝔰.k * numInfPlaces E) :=
    IsAdmissible.card_besselCoord_le
  grw [h_card, show (2 : ℝ) ^ 3 ≤ S.b by linarith [S.thousand_le_b]]
  exact h_pow

/-! ### Convergence and the tail bound -/

/-! At each place the Bessel functions lie below an invariant majorant `w v`, bounded by a constant
`a v`, with the power `3 i` of the scaled length to spare, `i = r ^ 3 f`. At `γ⁻¹ y` the power `i`
makes the sum over `γ` converge; at `y` we unfold `classCutoff c` and integrate `w`. The power `2 i`
that is left at both points gains `b ^ (-2 i)` where the cut acts, and this beats all the losses. -/

omit [S.IsAdmissible] in
/-- A power of the product of the scaled lengths is at least `1`, so it may be inserted as a
factor. -/
lemma le_scaledBesselLengthProd_pow_mul (y : InfinitePlace E → 𝔰.G₁) (i : ℕ) (x : ℝ≥0∞) :
    x ≤ ENNReal.ofReal (S.scaledBesselLengthProd y) ^ i * x :=
  le_mul_of_one_le_left' (one_le_pow₀ (one_le_ofReal.2 (one_le_scaledBesselLengthProd y)))

variable [HasPrimitiveRoot5040 E]

/-- Let the CM field `E` contain a primitive 5040th root of unity, and let the data `S` satisfy the
standing hypotheses `IsAdmissible`. Let `d` run over all classes and `γ` over the elements of `T`
that are terms over `(c, s, d)`. Then the sum of `β_d(γ⁻¹ y) ∏_v ‖W_v((γ⁻¹ y)_v)‖` is at most a
finite constant `C` that does not depend on the point `y` of G_∞, the product of one copy of `G₁`
for each infinite place `v`. -/
theorem exists_tsum_classCutoff_mul_prod_enorm_le {E : Type} [Field E] [CMType E]
    [HasPrimitiveRoot5040 E] {𝔰 : Shape} {S : Filling E 𝔰} {side : FullOrCut} [S.IsAdmissible]
    (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) :
    ∃ C : NNReal, ∀ y : InfinitePlace E → 𝔰.G₁,
      ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)),
          S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
            ∏ v : InfinitePlace E,
              ‖(S.besselSystem v).besselFn side (((S.ratToInf γ)⁻¹ * y) v)‖ₑ ≤
        C := by
  -- The Bessel functions decay in the scaled lengths, and this decay makes the sum converge.
  have h_majorant (v : InfinitePlace E) : ∃ (w : 𝔰.G₁ → ℝ≥0∞) (a : ℝ≥0∞),
      IsDecayMajorant S.b (numInfPlaces E) (S.besselSystem v).besselFn w a :=
    (S.besselSystem v).isCutPair.exists_majorant
  choose w a hw using h_majorant
  have h_decay (z : InfinitePlace E → 𝔰.G₁) : ∏ v, ‖(S.besselSystem v).besselFn side (z v)‖ₑ ≤
      (∏ v, a v) * .ofReal ((S.scaledBesselLengthProd z)⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)) :=
    (le_scaledBesselLengthProd_pow_mul z _ _).trans (pow_mul_prod_enorm_le_bound hw z)
  let bound : ℝ≥0∞ :=
    (∏ v, a v) * .ofReal (2 * S.b ^ (12 * 𝔰.n ^ 3 * 𝔰.r * numInfPlaces E))
  have h_bound_fin : bound ≠ ∞ :=
    mul_ne_top (prod_ne_top fun v _ ↦ (hw v).bound_ne_top) ofReal_ne_top
  refine ⟨bound.toNNReal, fun y ↦ ?_⟩
  calc
    _ ≤ ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)),
          S.classCutoff d ((S.ratToInf γ)⁻¹ * y) * ((∏ v, a v) * .ofReal
            ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^
              (𝔰.r ^ 3 * numInfPlaces E))) := by
      grw [h_decay]
    _ ≤ bound := tsum_classCutoff_mul_const_mul_inv_pow_le T c s (∏ v, a v) y
    _ = bound.toNNReal := (coe_toNNReal h_bound_fin).symm

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `S` be admissible, and let `γ` run over the elements of `T` that are terms over `(c, s, d)`,
for all classes `d`. The sum of the integrals `∫ β_c(y) β_d(γ⁻¹ y) ‖W(y) ⊗ W(γ⁻¹ y)^*‖ dy`
(`amplitudeMajorant`) is finite. -/
theorem tsum_amplitudeMajorant_lt_top (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) :
    ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)), S.amplitudeMajorant side c d γ < ∞ := by
  choose w a hw using fun v : InfinitePlace E ↦ (S.besselSystem v).isCutPair.exists_majorant
  refine lt_of_le_of_lt (le_trans ?_ (tsum_lintegral_classCutoff_mul_majorant_le T c s hw))
    (by finiteness)
  simp_rw [amplitudeMajorant, enorm_besselKernel]
  refine tsum_le_tsum fun d ↦ tsum_le_tsum fun γ ↦ lintegral_mono fun y ↦ ?_
  exact mul_le_mul' le_rfl (mul_le_mul'
    ((le_scaledBesselLengthProd_pow_mul y _ _).trans (pow_mul_prod_enorm_le_majorant hw y))
    ((le_scaledBesselLengthProd_pow_mul _ _ _).trans (pow_mul_prod_enorm_le_bound hw _)))

/-- Let `S` be admissible, let `d` run over all classes and `γ` over the elements of `T` that are
terms over `(c, s, d)`. The kernel `besselKernel side γ y` is `W(y) ⊗ W(γ⁻¹ y)^*`. The sum of the
integrals of `β_c(y) β_d(γ⁻¹ y)` times the norm of the difference between this kernel and the one
built from the cut function is at most `ν b ^ (-k³ f) / 2`. Here `ν = S.unipotentCovolume`,
`β_d = S.classCutoff d`, `k + 1` is the size of the middle block of the basis (`k = 𝔰.k`), `f` is
the number of infinite places and `b` is the size parameter of `S`. -/
theorem tsum_lintegral_enorm_besselKernel_sub_cut_le (T : Set (S.G E)) (c : S.Classes)
    (s : S.ResidueGL) :
    ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)),
      ∫⁻ y : InfinitePlace E → 𝔰.G₁, S.classCutoff c y * S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
        ‖S.besselKernel side γ y - S.besselKernel .cut γ y‖ₑ ≤
      .ofReal (S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) := by
  choose w a hw using fun v : InfinitePlace E ↦ (S.besselSystem v).isCutPair.exists_majorant
  let gain : ℝ≥0∞ := .ofReal (S.b ^ (2 * (𝔰.r ^ 3 * numInfPlaces E)))
  have hb : 1 ≤ S.b := S.one_le_b
  have h_gain_fin : gain⁻¹ ≠ ∞ := inv_ne_top.2 (by positivity)
  let majorant (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁) : ℝ≥0∞ :=
    (∏ v, w v (y v)) * ((∏ v, a v) * .ofReal
      ((S.scaledBesselLengthProd ((S.ratToInf γ)⁻¹ * y))⁻¹ ^ (𝔰.r ^ 3 * numInfPlaces E)))
  calc
    _ ≤ ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)), ∫⁻ y, S.classCutoff c y *
          S.classCutoff d ((S.ratToInf γ)⁻¹ * y) * (gain⁻¹ * (2 * majorant γ y)) := by
      grw [enorm_besselKernel_sub_cut_le hw]
    _ = gain⁻¹ * 2 * ∑' (d : S.Classes) (γ : ↥(T ∩ S.termsOver c s d)),
          ∫⁻ y, S.classCutoff c y * S.classCutoff d ((S.ratToInf γ)⁻¹ * y) * majorant γ y := by
      simp (disch := finiteness) only [← mul_assoc gain⁻¹, mul_left_comm _ (gain⁻¹ * _),
        lintegral_const_mul', ENNReal.tsum_mul_left]
    _ ≤ _ := (mul_le_mul_right (tsum_lintegral_classCutoff_mul_majorant_le T c s hw) _).trans
      inv_pow_mul_unipotentCovolume_mul_card_le

/-- For admissible `S`, the amplitudes of the elements of `T` over `(c, s, c')` are summable. -/
lemma summable_amplitude (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) :
    Summable fun γ : ↥(T ∩ S.termsOver c s c') ↦ S.amplitude side c c' γ := by
  refine .of_eNorm (ne_of_lt ?_)
  grw [enorm_amplitude_le]
  exact (le_tsum _ c').trans_lt (tsum_amplitudeMajorant_lt_top T c s)

variable {T : Set (S.G E)}

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible] in
/-- If `σ` is a term over `(c, t, c₁)` and `σ'` one over `(c', t', c₁')`, then `γ` is a term over
`(c₁, s, c₁')` if and only if `σ γ σ'⁻¹` is one over `(c, t s t'⁻¹, c')`. -/
lemma mem_termsOver_iff_mul_mul_inv_mem {c c₁ c' c₁' : S.Classes} {t t' s : S.ResidueGL}
    {σ σ' γ : S.G E} (hσ_over : σ ∈ S.termsOver c t c₁) (hσ'_over : σ' ∈ S.termsOver c' t' c₁') :
    γ ∈ S.termsOver c₁ s c₁' ↔ σ * γ * σ'⁻¹ ∈ S.termsOver c (t * s * t'⁻¹) c' :=
  ⟨fun hγ ↦ termsOver.mul (termsOver.mul hσ_over hγ) (termsOver.inv hσ'_over),
    fun hγ ↦ by simpa using termsOver.mul (termsOver.inv hσ_over) (termsOver.mul hγ hσ'_over)⟩

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. Let `σ` be a
rational isometry of the form with middle Gram matrix `S.ratMiddle E`. Assume that `σ` lies in the
Bessel subgroup `besselS`, generated by the unipotent group `besselU` and U(X₀), and is a term over
`(c, t, c₁)` (`termsOver`). Then `y ↦ S.classCutoff c (σ y)` has orbit sums `1` under
`S.classUnipotent c₁`, the rational points `u` of `besselU` with h_c₁⁻¹ u h_c₁ in the principal
congruence subgroup of level `S.M`. -/
lemma tsum_classCutoff_ratToInf_mul_eq_one {c c₁ : S.Classes} {t : S.ResidueGL}
    {σ : (S.ratMiddle E).G} (hσ : σ ∈ (S.ratMiddle E).besselS) (hσ_over : σ ∈ S.termsOver c t c₁)
    (y : InfinitePlace E → 𝔰.G₁) :
    ∑' u : S.classUnipotent c₁, S.classCutoff c (S.ratToInf σ * (S.ratToInf u * y)) = 1 := by
  -- Conjugation by `σ` carries `S.classUnipotent c₁` onto `S.classUnipotent c`.
  have conj_mem (γ : (S.ratMiddle E).G) :
      γ ∈ S.classUnipotent c₁ ↔ MulAut.conj σ γ ∈ S.classUnipotent c := by
    refine ((besselS_le_normalizer_besselU hσ γ).and
      (mem_termsOver_iff_mul_mul_inv_mem (s := 1) hσ_over hσ_over)).trans ?_
    simp only [MulAut.conj_apply, mul_one, mul_inv_cancel, mul_assoc]
    rfl
  simpa [mul_assoc] using (((MulAut.conj σ).subtypeEquiv conj_mem).tsum_eq _).trans
    (tsum_classCutoff_eq_one c (S.ratToInf σ * y))

/-- For admissible `S`, every class `c` and archimedean point `x`, the integral of `u ↦ β_c(u x)`,
`β_c = S.classCutoff c`, read as a complex function, over the product of the groups `besselU` is
`S.unipotentCovolume`. -/
lemma integral_classCutoff_eq_unipotentCovolume (c : S.Classes) (x : InfinitePlace E → 𝔰.G₁) :
    ∫ u : InfinitePlace E → besselU (T := 𝔰.middleGram (1 : ℂ)),
      ((S.classCutoff c fun v : InfinitePlace E ↦ u v * x v).toReal : ℂ)
        ∂(.pi fun _ : InfinitePlace E ↦ 𝔰.besselHaar) = S.unipotentCovolume := by
  rw [integral_complex_ofReal, integral_toReal (Measurable.aemeasurable (by fun_prop))
      (ae_lt_top (by fun_prop) (by simp [lintegral_classCutoff_eq_unipotentCovolume])),
    lintegral_classCutoff_eq_unipotentCovolume, toReal_ofReal S.unipotentCovolume_pos.le]

/-! ### Change of weight and moving blocks -/

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible] in
/-- Let `S` be a filling of shape `𝔰` over the CM field `E`. For stable `T`, the set of terms of `T`
over `(c, s, c')` is stable under `γ ↦ u γ u'⁻¹` for `u` in `S.classUnipotent c` and `u'` in
`S.classUnipotent c'`. -/
lemma mul_mul_inv_mem_inter_termsOver (hT : S.IsStable T) {c : S.Classes} {s : S.ResidueGL}
    {c' : S.Classes} (u : S.classUnipotent c) (u' : S.classUnipotent c') {γ : S.G E}
    (hγ_mem : γ ∈ T ∩ S.termsOver c s c') : u.val * γ * u'.val⁻¹ ∈ T ∩ S.termsOver c s c' := by
  obtain ⟨hu, hu_over⟩ := u.property
  obtain ⟨hu', hu'_over⟩ := (u'⁻¹).property
  exact ⟨by simpa using (hT u.val⁻¹ (inv_mem hu) u'.val⁻¹ hu' γ).2 hγ_mem.1,
    by simpa using termsOver.mul (termsOver.mul hu_over hγ_mem.2) hu'_over⟩

/-- Let the group `H`, with an s-finite inversion invariant measure `η`, act measurably on `Z` and
preserve the s-finite measure `μ`. A cutoff (`IsCutoff η β`) is a measurable `β : Z → [0, ∞]` with
`∫ β (u • p) dη(u) = 1` for every `p`. Two cutoffs `β`, `β'` give every invariant measurable `F` the
same integral: `∫ β F dμ = ∫ β' F dμ`. -/
lemma lintegral_mul_eq_of_isCutoff {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z] [Group H]
    [MulAction H Z] [MeasurableInv H] [MeasurableSMul₂ H Z] {η : Measure H} [SFinite η]
    [IsInvInvariant η] {μ : Measure Z} [SFinite μ] [SMulInvariantMeasure H Z μ] {β β' F : Z → ℝ≥0∞}
    (hβ : IsCutoff η β) (hβ' : IsCutoff η β') (hF : Measurable F)
    (h_inv : ∀ (u : H) (p : Z), F (u • p) = F p) :
    ∫⁻ p : Z, β p * F p ∂μ = ∫⁻ p : Z, β' p * F p ∂μ := by
  -- Under both weighted measures `F` has the law it has on the quotient.
  simpa [lintegral_withDensity_eq_lintegral_mul μ hβ.1 hF,
    lintegral_withDensity_eq_lintegral_mul μ hβ'.1 hF] using
    ((identDistrib_orbitMeasure (μ := μ) hβ hF h_inv).symm.trans
      (identDistrib_orbitMeasure hβ' hF h_inv)).lintegral_eq

/-- Let `S` be admissible and `T` stable. Let `X` be the set of `γ ∈ T` with h_c⁻¹ γ h_c' integral
of reduction `s` (`termsOver`). Let `φ γ y ∈ [0, ∞]` be measurable in `y` with sum `1` on each orbit
`(u γ u'⁻¹, u y)`, `γ ∈ X`, of `classUnipotent c × classUnipotent c'`; the first factor is the group
of rational `u` in `besselU` with h_c⁻¹ u h_c in the principal congruence subgroup of level `S.M`.
Then (a) the integrals `∫ φ γ y • besselKernel side γ y dy`, `γ ∈ X`, sum to the block; (b) each
integrand is integrable; (c) `∑_γ ∫ φ ‖kernel - cut kernel‖` is at most `ν b ^ (-k³ f) / 2`. Here
`ν = S.unipotentCovolume`, `b` is the size parameter of `S`, `k + 1` is the size of the middle block
of the basis (`k = 𝔰.k`) and `f` is the number of infinite places. -/
lemma hasSum_amplitudeSum_of_cutoff (hT : S.IsStable T) (c : S.Classes) (s : S.ResidueGL)
    (c' : S.Classes) (φ : S.G E → (InfinitePlace E → 𝔰.G₁) → ℝ≥0∞)
    (h_sum : ∀ γ ∈ T ∩ S.termsOver c s c', ∀ y : InfinitePlace E → 𝔰.G₁,
      ∑' u : S.classUnipotent c × S.classUnipotent c', φ (u.1 * γ * u.2⁻¹) (S.ratToInf u.1 * y) = 1)
    (hφ_meas : ∀ γ : S.G E, Measurable (φ γ)) :
    -- (a)
    HasSum (fun γ : ↥(T ∩ S.termsOver c s c') ↦
        ∫ y : InfinitePlace E → 𝔰.G₁, (φ γ y).toReal • S.besselKernel side γ y)
      (S.amplitudeSum side T c s c') ∧
    -- (b)
    (∀ γ : ↥(T ∩ S.termsOver c s c'),
      Integrable fun y : InfinitePlace E → 𝔰.G₁ ↦ (φ γ y).toReal • S.besselKernel side γ y) ∧
    -- (c)
    ∑' γ : ↥(T ∩ S.termsOver c s c'), ∫⁻ y : InfinitePlace E → 𝔰.G₁,
      φ γ y * ‖S.besselKernel side γ y - S.besselKernel .cut γ y‖ₑ ≤
      .ofReal (S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) := by
  -- `Δ = S.classUnipotent c × S.classUnipotent c'` acts on pairs `(γ, y)` by `(u γ u'⁻¹, u y)`,
  -- keeping the measure `ρ` and the kernel. Both `β₀ = β_c β_c'` and `φ` are cutoffs for this
  -- action, so they give an invariant function the same integral; the convergence and the tail
  -- bound for `β₀` pass to `φ`.
  let X : Set (S.G E) := T ∩ S.termsOver c s c'
  let Δ : Type := S.classUnipotent c × S.classUnipotent c'
  let Y : Type := InfinitePlace E → 𝔰.G₁
  let : MeasurableSpace (S.G E) := ⊤
  let : MulAction Δ X :=
    { smul u γ := ⟨u.1 * γ * u.2⁻¹, mul_mul_inv_mem_inter_termsOver hT u.1 u.2 γ.property⟩
      one_smul := by simp [HSMul.hSMul, Δ]
      mul_smul := by simp [HSMul.hSMul, Δ, mul_assoc] }
  -- The first component of `u` acts on `y` by left translation.
  let action : MulAction Δ Y := .compHom _ ((S.ratToInf.domRestrict _).comp (.fst _ _))
  let : SMul Δ Y := action.toSMul
  let ρ : Measure (X × Y) := Measure.count.prod volume
  have preserving (u : Δ) : MeasurePreserving (u • ·) ρ ρ :=
    (measurePreserving_count (MulAction.toPerm u)).prod (measurePreserving_mul_left ..)
  have : MeasurableSMul₂ Δ (X × Y) :=
    ⟨measurable_from_prod_countable_right fun u ↦ (preserving u).measurable⟩
  have : SMulInvariantMeasure Δ (X × Y) ρ :=
    ((smulInvariantMeasure_tfae Δ ρ).out 7 1).1 preserving
  let kernel (τ : FullOrCut) (p : X × Y) : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) :=
    S.besselKernel τ p.1 p.2
  have kernel_smul (τ : FullOrCut) (u : Δ) (p : X × Y) : kernel τ (u • p) = kernel τ p := by
    simp +zetaDelta [besselKernel, HSMul.hSMul, besselFn_mul_of_mem_classUnipotent, mul_assoc,
      SMul.smul]
  have kernel_meas (τ : FullOrCut) : Measurable (kernel τ) := by fun_prop [besselKernel]
  let β₀ (p : X × Y) : ℝ≥0∞ := S.classCutoff c p.2 * S.classCutoff c' ((S.ratToInf p.1)⁻¹ * p.2)
  have β₀_cutoff : IsCutoff (count : Measure Δ) β₀ := by
    refine ⟨by fun_prop, fun p ↦ ?_⟩
    simp +zetaDelta [HSMul.hSMul, tsum_classCutoff_eq_one, mul_assoc, lintegral_count,
      tsum_prod', ENNReal.tsum_mul_left, SMul.smul]
  have φ_cutoff : IsCutoff (count : Measure Δ) fun p : X × Y ↦ φ p.1 p.2 :=
    ⟨measurable_from_prod_countable_right fun γ ↦ hφ_meas γ,
      fun p ↦ (lintegral_count _).trans (h_sum p.1 p.1.property p.2)⟩
  -- The integral of an invariant `F` against any cutoff is at most the sum of integrals for `β₀`.
  have lintegral_le {β F : X × Y → ℝ≥0∞} (hβ : IsCutoff (count : Measure Δ) β)
      (hF : Measurable F) (h_inv : ∀ (u : Δ) (p : X × Y), F (u • p) = F p) :
      ∫⁻ p, β p * F p ∂ρ ≤ ∑' γ : X, ∫⁻ y, β₀ (γ, y) * F (γ, y) :=
    (lintegral_mul_eq_of_isCutoff hβ β₀_cutoff hF h_inv).le.trans
      ((lintegral_prod_le _).trans_eq (lintegral_count _))
  have integrable {β : X × Y → ℝ≥0∞} (hβ : IsCutoff (count : Measure Δ) β) :
      Integrable (fun p ↦ (β p).toReal • kernel side p) ρ :=
    integrable_toReal_smul hβ.1 (kernel_meas side).aestronglyMeasurable
      ((lintegral_le hβ (kernel_meas side).eNorm (by simp [kernel_smul])).trans_lt
        ((le_tsum _ c').trans_lt (tsum_amplitudeMajorant_lt_top T c s)))
  -- Fubini: for every cutoff the integrals over `y` sum to that of the kernel over the quotient.
  have hasSum {β : X × Y → ℝ≥0∞} (hβ : IsCutoff (count : Measure Δ) β) :
      HasSum (fun γ : X ↦ ∫ y, (β (γ, y)).toReal • S.besselKernel side γ y)
        (∫ p, kernel side p ∂orbitMeasure (count : Measure Δ) ρ) := by
    rw [hβ.integral_orbitMeasure (kernel_smul side) (kernel_meas side),
      integral_prod _ (integrable hβ)]
    exact (hasSum_integral_measure (integrable hβ).integral_prod_left).congr_fun
      (by simp [kernel, Y])
  have block_eq :
      S.amplitudeSum side T c s c' = ∫ p, kernel side p ∂orbitMeasure (count : Measure Δ) ρ :=
    (hasSum β₀_cutoff).tsum_eq
  refine ⟨by simpa only [block_eq] using hasSum φ_cutoff,
    ae_count_iff.1 (integrable φ_cutoff).prod_right_ae, ?_⟩
  have diff_meas : Measurable fun p ↦ ‖kernel side p - kernel .cut p‖ₑ := by fun_prop
  calc
    _ = ∫⁻ p, φ p.1 p.2 * ‖kernel side p - kernel .cut p‖ₑ ∂ρ :=
      ((lintegral_prod _ (φ_cutoff.1.mul diff_meas).aemeasurable).trans (lintegral_count _)).symm
    _ ≤ ∑' γ : X, ∫⁻ y, β₀ (γ, y) * ‖kernel side (γ, y) - kernel .cut (γ, y)‖ₑ :=
      lintegral_le φ_cutoff diff_meas (by simp [kernel_smul])
    _ ≤ _ := (le_tsum _ c').trans (tsum_lintegral_enorm_besselKernel_sub_cut_le T c s)

/-- Moving a block. Let `S` be admissible and `T` stable. Let `σ` over `(c, t, c₁)` and `σ'` over
`(c', t', c₁')` be rational elements (`(S.ratMiddle E).G` is the group `S.G E`) of the Bessel
subgroup `besselS`. Suppose that `γ ∈ T ↔ σ γ σ'⁻¹ ∈ T`. If a continuous linear map `L` takes the
kernel at `(γ, y)` to the kernel at `(σ γ σ'⁻¹, σ y)`, then `L` takes the block over `(c₁, s, c₁')`
to that over `(c, t s t'⁻¹, c')`. -/
lemma amplitudeSum_mul_mul_inv (hT : S.IsStable T) {c : S.Classes} {t : S.ResidueGL}
    {c₁ : S.Classes} {σ : (S.ratMiddle E).G} {c' : S.Classes} {t' : S.ResidueGL} {c₁' : S.Classes}
    {σ' : (S.ratMiddle E).G} (hσ : σ ∈ besselS) (hσ_over : σ ∈ S.termsOver c t c₁)
    (hσ' : σ' ∈ besselS) (hσ'_over : σ' ∈ S.termsOver c' t' c₁')
    (hT_iff : ∀ γ : S.G E, γ ∈ T ↔ σ * γ * σ'⁻¹ ∈ T)
    (L : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) →L[ℂ]
      EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord))
    (hL : ∀ (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁),
      S.besselKernel side (σ * γ * σ'⁻¹) (S.ratToInf σ * y) = L (S.besselKernel side γ y))
    (s : S.ResidueGL) :
    S.amplitudeSum side T c (t * s * t'⁻¹) c' = L (S.amplitudeSum side T c₁ s c₁') := by
  -- The weight `β_c(σ y) β_c'(σ' γ⁻¹ y)` has orbit sums `1`, so
  -- `hasSum_amplitudeSum_of_cutoff` computes the right side with it; then substitute
  -- `γ ↦ σ γ σ'⁻¹` and `y ↦ σ y`.
  let φ (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁) : ℝ≥0∞ :=
    S.classCutoff c (S.ratToInf σ * y) * S.classCutoff c' (S.ratToInf σ' * ((S.ratToInf γ)⁻¹ * y))
  -- The orbit sums of `φ` are products of those of the two translated cutoffs, hence `1`.
  have φ_sum (γ : S.G E) (y : InfinitePlace E → 𝔰.G₁) :
      ∑' u : S.classUnipotent c₁ × S.classUnipotent c₁',
        φ (u.1 * γ * u.2⁻¹) (S.ratToInf u.1 * y) = 1 := by
    simp [φ, tsum_classCutoff_ratToInf_mul_eq_one hσ hσ_over,
      tsum_classCutoff_ratToInf_mul_eq_one hσ' hσ'_over,
      mul_assoc, tsum_prod', ENNReal.tsum_mul_left]
  have φ_meas (γ : S.G E) : Measurable (φ γ) := by fun_prop
  obtain ⟨hasSum, integrable, -⟩ :=
    hasSum_amplitudeSum_of_cutoff (side := side) hT c₁ s c₁' φ (fun γ _ ↦ φ_sum γ) φ_meas
  let move : ↥(T ∩ S.termsOver c₁ s c₁') ≃ ↥(T ∩ S.termsOver c (t * s * t'⁻¹) c') :=
    ((Equiv.mulLeft σ).trans (.mulRight σ'⁻¹)).subtypeEquiv fun γ ↦
      (hT_iff γ).and (mem_termsOver_iff_mul_mul_inv_mem hσ_over hσ'_over)
  refine (move.hasSum_iff.1 ((hasSum.mapL L).congr_fun fun γ ↦ ?_)).tsum_eq
  change S.amplitude side c c' (σ * γ * σ'⁻¹) = L (∫ y, (φ γ y).toReal • S.besselKernel side γ y)
  rw [← L.integral_comp_comm (integrable γ), amplitude,
    ← integral_mul_left_eq_self _ (S.ratToInf σ)]
  simp [φ, ← hL, mul_assoc]

/-- Let `S` be admissible and `T` stable (`IsStable`), and let `side` choose the full or the cut
Bessel function. Let `u`, `u'` in `besselU` be integral finite adelic elements
(`latticeStabilizer`), with reductions `ū`, `ū'` modulo the chosen places (`S.reduction`). Then the
block at `ū s ū'⁻¹` is `ψ(u)⁻¹ ψ(u')` times the block at `s`. Here `ψ = S.unipotentChar` is the
additive character `S.selfDualChar` at the sum of the entries just above the diagonal on the frame
(`simpleRootSum`), divided by the level `S.M`. -/
lemma amplitudeSum_besselU_mul (hT : S.IsStable T) {u u' : S.latticeStabilizer}
    (hu : u.1 ∈ besselU) (hu' : u'.1 ∈ besselU) (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) :
    S.amplitudeSum side T c (S.reduction u * s * (S.reduction u')⁻¹) c' =
      ((S.unipotentChar u)⁻¹ * S.unipotentChar u') • S.amplitudeSum side T c s c' := by
  -- Approximate `u`, `u'` modulo `S.principalLevel` by rational `x`, `x'` in `besselU` with the
  -- same character; they lie over `(c, ū, c)` and `(c', ū', c')`. Move the block by them.
  have approx (d : S.Classes) {v : S.latticeStabilizer} (hv : v.val ∈ besselU) :
      ∃ x : S.G E, x ∈ besselU ∧ x ∈ S.termsOver d (S.reduction v) d ∧
        S.unipotentChar (S.ratToFin x) = S.unipotentChar v := by
    obtain ⟨x, hx, ⟨k, hk⟩, hψ⟩ := exists_rat_approx_unipotentChar_eq d hv
    exact ⟨x, hx, ⟨v * k, by simp_all⟩, hψ⟩
  obtain ⟨x, hx, hx_over, hψ⟩ := approx c hu
  obtain ⟨x', hx', hx'_over, hψ'⟩ := approx c' hu'
  -- The kernel changes by the scalar `ψ(x)⁻¹ ψ(x')`, and so does the block.
  simpa [hψ, hψ'] using amplitudeSum_mul_mul_inv hT
    (mem_partialUnitriangularGroup_of_mem_besselU hx) hx_over
    (mem_partialUnitriangularGroup_of_mem_besselU hx') hx'_over
    (fun γ ↦ (hT x⁻¹ (inv_mem hx) _ (inv_mem hx') γ).symm) (.lsmul ℂ ℂ _)
    (besselKernel_besselU_mul hx hx') s

/-- Let `S` be admissible. If `T` is stable (`S.IsStable T`) and `s` does not agree, that is
`unipotentChar u ≠ unipotentChar u'` for some integral unipotent `u`, `u'` whose reductions satisfy
`ū s = s ū'`, then the amplitude sum `S.amplitudeSum side T c s c'` of the elements of `T` over
`(c, s, c')` vanishes. -/
lemma amplitudeSum_eq_zero_of_not_agrees (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes)
    (hT : S.IsStable T) (hs : ¬S.Agrees s) :
    S.amplitudeSum side T c s c' = 0 := by
  -- For `ū s = s ū'`, `amplitudeSum_besselU_mul` multiplies the block at `s` by `ψ(u)⁻¹ ψ(u')`
  -- without changing it; a nonzero block forces this scalar to be `1`.
  by_contra h_ne
  refine hs fun u u' hu hu' huu' ↦ eq_of_inv_mul_eq_one (smul_left_injective ℂ h_ne ?_)
  simp [← amplitudeSum_besselU_mul hT hu hu', huu']

end GeneralBlocks

/-! ### The identity block -/

open scoped Classical in
/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. Let `c`, `c'` be
classes, and let `i`, `j` be tuples of one coordinate index of the Bessel function at each infinite
place (`BesselCoord`). Sum, over the rational points `γ` of the Bessel subgroup `besselS` with h_c⁻¹
γ h_c' integral of reduction `1` (`termsOver`), the integrals
`∫ β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^* dy`, with `W` the full Bessel function and
`β_c = S.classCutoff c`. The `(i, j)` entry of this sum (`amplitudeSum`) is `S.unipotentCovolume`,
the covolume of `S.classUnipotent c` in the real unipotent group, if `c = c'` and `i = j`, and `0`
otherwise. -/
lemma amplitudeSum_besselS_one_eq_ite {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [S.IsAdmissible] [HasPrimitiveRoot5040 E] (c c' : S.Classes) (i j : S.BesselCoord) :
    S.amplitudeSum .full (S.ratMiddle E).besselS c 1 c' (i, j) =
      (if c = c' ∧ i = j then S.unipotentCovolume else 0 : ℝ) := by
  -- Only `γ ∈ S.classUnipotent c` with `c = c'` contribute
  -- (`eq_and_mem_classUnipotent_of_besselS`). By `hasSum_amplitudeSum_of_cutoff` the whole
  -- weight `classCutoff c` may be put on the one term `γ = 1`; unfolding over `besselU` at every
  -- place then leaves `unipotentCovolume` times the product of the local inner products on
  -- `𝖴 \ G₁`.
  obtain hne | rfl := ne_or_eq c c'
  · have : IsEmpty ↥(↑(S.ratMiddle E).besselS ∩ S.termsOver c 1 c') :=
      ⟨fun ⟨_, hγ, hγ_over⟩ ↦ hne (eq_and_mem_classUnipotent_of_besselS hγ hγ_over).1⟩
    simp [amplitudeSum, tsum_empty, hne]
  let φ (γ : S.G E) : (InfinitePlace E → 𝔰.G₁) → ℝ≥0∞ := if 1 = γ then S.classCutoff c else 0
  have φ_sum : ∀ γ ∈ ↑(S.ratMiddle E).besselS ∩ S.termsOver c 1 c,
      ∀ y : InfinitePlace E → 𝔰.G₁, ∑' u : S.classUnipotent c × S.classUnipotent c,
        φ (u.1 * γ * u.2⁻¹) (S.ratToInf u.1 * y) = 1 := by
    rintro γ ⟨hγ, hγ_over⟩ y
    lift γ to S.classUnipotent c using (eq_and_mem_classUnipotent_of_besselS hγ hγ_over).2
    simp only [φ]
    norm_cast
    rw [tsum_prod']
    simp only [ite_apply, eq_mul_inv_iff_mul_eq, one_mul, Pi.zero_apply]
    exact (tsum_congr fun a ↦ by
      convert tsum_ite_eq (a * γ) (fun _ ↦ S.classCutoff c (S.ratToInf ↑a * y))).trans
      (tsum_classCutoff_eq_one c y)
  have φ_meas (γ : S.G E) : Measurable (φ γ) := by measurability
  obtain ⟨hasSum, integrable, -⟩ :=
    hasSum_amplitudeSum_of_cutoff (side := .full) isStable_besselS c 1 c φ φ_sum φ_meas
  let F (v : InfinitePlace E) (y : 𝔰.G₁) : ℂ :=
    (S.besselSystem v).besselFn .full y (i v) * starRingEnd ℂ
      ((S.besselSystem v).besselFn .full y (j v))
  have ker_one (y : InfinitePlace E → 𝔰.G₁) :
      S.besselKernel .full 1 y (i, j) = ∏ v, F v (y v) := by
    simp [besselKernel, besselFn, F, prod_mul_distrib]
  -- The character by which `besselU` acts has modulus `1`, so it cancels in `F`.
  have F_mul (v : InfinitePlace E) (u : 𝔰.G₁) (hu : u ∈ besselU) (y : 𝔰.G₁) :
      F v (u * y) = F v y := by
    simp [F, ((S.besselSystem v).isCutPair.isBesselFunction _).map_unipotent_mul u hu, mul_conj',
      mul_mul_mul_comm _ _ (starRingEnd _ _)]
  have one_term : 1 ∈ ↑(S.ratMiddle E).besselS ∩ S.termsOver c 1 c :=
    ⟨besselS.one_mem, (S.classUnipotent c).one_mem.2⟩
  have others (γ : ↥(↑(S.ratMiddle E).besselS ∩ S.termsOver c 1 c)) (hγ : γ ≠ ⟨1, one_term⟩) :
      ∫ y, (φ γ.val y).toReal • S.besselKernel .full γ y = 0 := by
    simp [φ, show 1 ≠ γ.val from fun h ↦ hγ (Subtype.ext h.symm)]
  have h_int_prod : Integrable fun y : InfinitePlace E → 𝔰.G₁ ↦
      (S.classCutoff c y).toReal * ∏ v, F v (y v) := by
    simpa [φ, ker_one] using (integrable ⟨1, one_term⟩).eval_piLp (i, j)
  calc
    _ = ∫ y, (S.classCutoff c y).toReal * ∏ v, F v (y v) := by
      rw [hasSum.unique (hasSum_single ⟨1, one_term⟩ others),
        eval_integral_piLp (integrable ⟨1, one_term⟩).eval_piLp]
      simp [φ, ker_one]
    _ = ∫ x, S.unipotentCovolume * ∏ v, F v (x v) ∂.pi fun _ ↦ besselQuotMeasure := by
      rw [← (measurePreserving_pi_orbitMeasure 𝔰.besselHaar).integral_integral_comp h_int_prod]
      simp [Pi.mul_def, F_mul, integral_mul_const, integral_const_mul,
        integral_classCutoff_eq_unipotentCovolume]
    _ = S.unipotentCovolume * ∏ v, if i v = j v then 1 else 0 := by
      rw [integral_const_mul, integral_fintype_prod_eq_prod]
      exact congrArg _ (prod_congr rfl fun v _ ↦ (S.besselSystem v).orthonormal (i v) (j v))
    _ = _ := by simp [Fintype.prod_boole, funext_iff, apply_ite ofReal]

end New.Filling

end AmplitudeSums
