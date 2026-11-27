module

import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import TauCeti.Analysis.Real.Sqrt
public import New.Spanning.RemainingTerms.Size
public import New.Spanning.Unfolding.Climbing
import Lib.Adelic.Unitary.CongruenceLevels
import New.Spanning.RemainingTerms.Sum
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.Module
import Lib.General.LinearAlgebra.BlockEmbeddings
import New.Spanning.MainTerm.EnergyEstimate
import New.Spanning.SecondMoment.PositiveType
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.NumberTheory.NumberField.Countable
public import New.Spanning.SecondMoment.FewTranslates
public import Lib.General.Groups.CharacterTheory
public import Lib.Shimura.ComplexTheta.AppellHumbertData
public import New.Spanning.Frames.FixedLines
import Lib.Shimura.Uniformisation.HolomorphicFamilies
import New.Spanning.Frames.FiniteDepth
import New.Spanning.Frames.FiniteShells
import New.Spanning.MainTerm.GlobalToLocal

section
section
/-!
# The expansion of the squares and the second moment near the Bessel subgroup

This file proves the expansion of the squares and the bound on the second moment near `R̄₀`, where
`R̄₀ = reducedImage besselS` is the reduction of the Bessel subgroup. These results concern the
operators `P_s = P* s P`, stated in terms of their blocks. The terms in the Bessel subgroup give the
operator `r_ψ(s)`, which is `New.Filling.besselTranslate`, and the terms off it give `P_s - r_ψ(s)`.
Along the way it treats the terms of cell rank `0` and the cosets `ζ R̄₀` by integral `ζ ∈ E` with
`ζ ζ̄ = 1`, called roots of unity (these are the roots of unity of `E`, by Kronecker's theorem), and
it computes the blocks of the Bessel subgroup.

## Main definitions and results

* `New.Filling.sqrt_secondMoment_compl_besselS_le`: the expansion of the squares.
* `New.Filling.secondMoment_compl_besselS_le`: `P_s` is close to `r_ψ(s)` near `R̄₀`.

Notions from other files:
* `termsOver c s c'`: the rational `γ` such that `h_c⁻¹ γ h_c'` (`translateByClassReps`) is integral
  with reduction `s`; such a `γ` lies over the block `(c, s, c')`.
* `amplitudeSum side T c s c'`: the sum of the amplitudes of the elements of `T` over that block.
* `secondMoment A Ω`: the sum of `‖A c s c'‖² / unipotentCovolume²` over all classes `c`, `c'` and
  `s ∈ Ω`.
* `reducedImage A`: the image in the finite group `ResidueGL` of the integral elements of `A`.
-/

@[expose] public section

namespace New

open Matrix Complex Module InnerProductSpace EuclideanSpace Finset Fintype

attribute [local instance low] Fintype.ofFinite

section Scalars

variable {R n : Type} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n] (J : Matrix n n R)

/-- A scalar `ζ` with `ζ ζ̄ = 1` as an isometry of the form `J`. -/
noncomputable def scalarIsometry (ζ : R) (hζ : ζ * star ζ = 1) : U J :=
  ⟨⟨ζ • 1, star ζ • 1, by simp [smul_smul, mul_comm, hζ], by simp [smul_smul, hζ]⟩,
    mem_unitaryGroupOf_iff.2 <| show (ζ • 1)ᴴ * J * (ζ • 1) = J by simp [smul_smul, hζ]⟩

lemma scalarIsometry_one (h : (1 : R) * star 1 = 1) : scalarIsometry J 1 h = 1 := by
  ext : 2
  simp [scalarIsometry]

/-- For `ζ ζ̄ = 1` and an isometry `g` of `J`, the matrix of `ζ⁻¹ g` is `ζ̄` times that of `g`. -/
lemma val_scalarIsometry_inv_mul {ζ : R} (hζ : ζ * star ζ = 1) (g : U J) :
    (((scalarIsometry J ζ hζ)⁻¹ * g : U J) : GL n R).val = star ζ • (g : GL n R).val := by
  simp [scalarIsometry]

end Scalars

/-- Let `ϱ > 0`, so that the first frame vector `e₁` is orthogonal to the frame. If `g` maps `e₁` to
a multiple of itself, then the leading minors of positive size of `frameGram g`, the matrix of the
products of the frame with its image under `g`, vanish. -/
lemma leadingMinor_frameGram_eq_zero {R : Type} [CommRing R] {𝔰 : Shape} (T : 𝔰.Form R)
    (hϱ : 0 < 𝔰.ϱ) {g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R}
    (hg : ∀ j : 𝔰.BesselIndex, j ≠ 𝔰.besselFrame 0 → g j (𝔰.besselFrame 0) = 0)
    {l : Fin (𝔰.ϱ + 2)} (hl : 0 < l.val) : leadingMinor (T.frameGram g) l = 0 := by
  have h_orth (b : Fin (𝔰.ϱ + 1)) : T.splitGram (𝔰.besselFrame b) (𝔰.besselFrame 0) = 0 := by
    rw [show 𝔰.besselFrame 0 = .inl ⟨0, hϱ⟩ from besselFrame_castSucc ⟨0, hϱ⟩]
    cases b using Fin.lastCases <;> simp [splitGram]
  have h_col (b : Fin (𝔰.ϱ + 1)) : T.frameGram g b 0 = 0 := by
    rw [Shape.Form.frameGram, submatrix_apply, Matrix.mul_apply,
      Fintype.sum_eq_single (𝔰.besselFrame 0)
      fun j hj ↦ by rw [hg j hj, mul_zero], h_orth, zero_mul]
  exact det_eq_zero_of_column_eq_zero ⟨0, hl⟩ fun a ↦ h_col (Fin.castLE l.is_le a)

/-- A real function `β` of positive type on a group, that is, with `β (a⁻¹ b) = ⟪u a, u b⟫` for
vectors `u a` of an inner product space, is largest at `1`. -/
lemma le_apply_one_of_inner_eq {G V : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {β : G → ℝ} {u : G → V}
    (h_posType : ∀ a b : G, ⟪u a, u b⟫_ℂ = β (a⁻¹ * b)) (s : G) : β s ≤ β 1 := by
  have h_norm (a : G) : ‖u a‖ ^ 2 = β 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), h_posType, inv_mul_cancel, RCLike.re_to_complex, ofReal_re]
  calc β s = RCLike.re ⟪u 1, u s⟫_ℂ := by simp [h_posType]
    _ ≤ ‖u 1‖ * ‖u s‖ := re_inner_le_norm (u 1) (u s)
    _ ≤ β 1 := by linarith [two_mul_le_add_sq ‖u 1‖ ‖u s‖, h_norm 1, h_norm s]

open scoped Classical in
/-- The sum of `β` over the elements of a subgroup `H` with the property `p`, read in the whole
group. -/
lemma sum_subgroup_filter {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (p : G → Prop)
    (β : G → ℝ) : ∑ s : H with p s.val, β s.val = ∑ s : G with s ∈ H ∧ p s, β s := by
  rw [← filter_filter, sum_filter, sum_filter p, sum_subtype (p := (· ∈ H)) _ (by simp)]

/-- If row `j` of `M` vanishes before the index `b`, and `v` vanishes after `b` and is `1` at `b`,
then the entry `j` of `M v` is `M j b`. -/
lemma mulVec_apply_eq_of_eq_zero_of_lt {R m n : Type*} [Semiring R] [Fintype n] [LinearOrder n]
    {M : Matrix m n R} {v : n → R} {j : m} {b : n} (hM : ∀ a : n, a < b → M j a = 0)
    (hv : ∀ a : n, b < a → v a = 0) (hb : v b = 1) : (M *ᵥ v) j = M j b := by
  rw [mulVec_apply_eq_sum, Fintype.sum_eq_single b, hb, mul_one]
  intro a ha
  obtain h | h := ha.lt_or_gt <;> simp [hM, hv, h]

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- Suppose that for every index `a` the frame and its image under `γ` have a common vector that is
a combination of their vectors up to `a`, with coefficient `1` at `a` in both
(`PairOccursAt`). Then `γ` lies in the Bessel subgroup. -/
lemma mem_besselS_of_pairOccursAt {γ : S.G E}
    (h_pairs : ∀ a : Fin (𝔰.ϱ + 1), PairOccursAt γ 1 1 a) : γ ∈ besselS := by
  -- By induction on `b`, the vector `γ e_b` is `e_b` plus earlier frame vectors.
  have h_col (j : 𝔰.BesselIndex) (b : Fin (𝔰.ϱ + 1)) (hb : b.val ≤ BesselIndex.level j) :
      frameImage (γ : GL 𝔰.BesselIndex E).val j b = frameImage 1 j b := by
    induction b using WellFoundedLT.induction with | ind b ih
    obtain ⟨x, y, hxy, hx, hy, h_zero⟩ := h_pairs b
    -- In row `j` of the relation at index `b` only the two terms at `b` remain.
    have h_one (a : Fin (𝔰.ϱ + 1)) (ha : a < b) :
        frameImage (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) j a = 0 :=
      one_apply_ne fun hj : j = _ ↦ ha.not_ge (by rwa [hj, level_besselFrame] at hb)
    have h_γ (a : Fin (𝔰.ϱ + 1)) (ha : a < b) : frameImage (γ : GL _ E).val j a = 0 := by
      rw [ih a ha (le_trans ha.le hb), h_one a ha]
    rw [← mulVec_apply_eq_of_eq_zero_of_lt h_γ (fun a ha ↦ (h_zero a ha).2) hy,
      ← mulVec_apply_eq_of_eq_zero_of_lt h_one (fun a ha ↦ (h_zero a ha).1) hx, hxy]
  exact Filling.mem_besselS_iff_frameImage.2 h_col

/-- If the first frame vector satisfies `ζ e₁ = γ e₁` in the form of `PairOccursAt` at the
index `0`, then `ζ` is the diagonal entry of `γ` at `e₁`. -/
lemma PairOccursAt.apply_besselFrame_zero {γ : S.G E} {ζ : E}
    (h_pair : PairOccursAt γ ζ 1 0) :
    (γ : GL 𝔰.BesselIndex E).val (𝔰.besselFrame 0) (𝔰.besselFrame 0) = ζ := by
  obtain ⟨x, y, hxy, hx, hy, h_zero⟩ := h_pair
  simpa [mulVec_eq_sum, Fin.sum_univ_succ, hx, hy, h_zero, Matrix.one_apply] using
    congrFun hxy.symm (𝔰.besselFrame 0)

/-- Let `ζ ζ̄ = 1`. If the frame and its image under `γ` have common vectors with leading
coefficients `ζ` and `1` at every index, then `ζ⁻¹ γ` lies in the Bessel subgroup. -/
lemma scalarIsometry_inv_mul_mem_besselS {γ : S.G E} {ζ : E} (hζ : ζ * star ζ = 1)
    (h_pairs : ∀ a : Fin (𝔰.ϱ + 1), PairOccursAt γ ζ 1 a) :
    (scalarIsometry (S.ratMiddle E).splitGram ζ hζ)⁻¹ * γ ∈ (S.ratMiddle E).besselS := by
  refine mem_besselS_of_pairOccursAt fun a ↦ ?_
  obtain ⟨x, y, hxy, hx, hy, h_zero⟩ := h_pairs a
  refine ⟨star ζ • x, y, ?_, by simp [hx, mul_comm, hζ], hy, fun b hb ↦ by simp [h_zero b hb]⟩
  have h_smul : frameImage (star ζ • (γ : GL 𝔰.BesselIndex E).val) =
      star ζ • frameImage (γ : GL 𝔰.BesselIndex E).val := rfl
  rw [mulVec_smul, hxy, val_scalarIsometry_inv_mul, h_smul, smul_mulVec]

namespace Filling

/-! ### Terms of cell rank `0` and scalar cosets -/

/-- For `γ` in the Bessel subgroup and classes `c`, `c'` with representatives `h_c`, `h_c'`, the
finite adelic element `h_c⁻¹ γ h_c'` lies in the Bessel subgroup. -/
lemma translateByClassReps_mem_besselS {γ : S.G E} (hγ : γ ∈ besselS) (c c' : S.Classes) :
    S.translateByClassReps c c' γ ∈ besselS := by
  obtain ⟨u, hu, η, rfl⟩ := exists_besselU_mul_toBesselH hγ S.isUnit_natCast_N
  have h_rep (k : Gf E 𝔰.κ) : S.inclHFin k ∈ besselS :=
    mem_partialUnitriangularGroup_of_mem_floorGroup (inclHFin_mem_besselH k)
  -- The representatives `h_c`, `h_c'` are values of `inclHFin`.
  refine mul_mem (mul_mem (inv_mem (h_rep _)) ?_) (h_rep _)
  rw [map_mul, ratToFin_toBesselH]
  exact mul_mem (mem_partialUnitriangularGroup_of_mem_besselU (ratToFin_mem_besselU_iff.2 hu))
    (h_rep _)

/-- If `h_c⁻¹ γ h_c' = translateByClassReps c c' γ` is an element `k` of the stabilizer of the
lattice, then the diagonal entry of `γ` at the first frame vector `e₁` is integral, being the same
entry of `k`. -/
lemma apply_besselFrame_zero_mem_Ô {γ : S.G E} {c c' : S.Classes} {k : S.latticeStabilizer}
    (hk : (k : S.GFin) = S.translateByClassReps c c' γ) :
    ((γ : GL 𝔰.BesselIndex E).val (𝔰.besselFrame 0) (𝔰.besselFrame 0) : 𝔸f E) ∈ Ô E := by
  have h_first : 𝔰.besselFrame 0 = .inl ⟨0, pos_of_gt S.ten_pow_five_le_varrho⟩ :=
    besselFrame_castSucc ⟨0, _⟩
  have h_frame : frameImage ((k : S.GFin) : GL 𝔰.BesselIndex (𝔸f E)).val =
      S.classCoord c * finAdeleMatrix (frameImage (γ : GL 𝔰.BesselIndex E).val) := by
    rw [hk, frameImage_translateByClassReps]
  have h_entry : (k : S.GFin).val (𝔰.besselFrame 0) (𝔰.besselFrame 0) =
      ((γ : GL 𝔰.BesselIndex E).val (𝔰.besselFrame 0) (𝔰.besselFrame 0) : 𝔸f E) := by
    simpa [classCoord_eq_fromBlocks, Matrix.mul_apply, Matrix.one_apply, h_first]
      using congrFun₂ h_frame (𝔰.besselFrame 0) 0
  rw [← h_entry]
  exact k.property.isIntMatrix _ _

/-- If the matrix of an element `z` of the stabilizer of the lattice is the scalar `ζ`, an integral
adele, then its reduction at a chosen place `w` is the residue of `ζ` at `w`. -/
lemma val_reduction_of_eq_smul_one {z : S.latticeStabilizer} {ζ : Ô E}
    (hz : ((z : S.GFin) : GL 𝔰.BesselIndex (𝔸f E)).val = (ζ : 𝔸f E) • 1)
    (i : Fin 2) (w : S.chosenPlaces i) :
    (S.reduction z i w).val = New.reduceAt (w : FinPlace E) ζ • 1 := by
  ext a b
  change New.reduceAt (w : FinPlace E) ⟨((z : S.GFin) : GL 𝔰.BesselIndex (𝔸f E)).val a b, _⟩ = _
  by_cases hab : a = b <;> simp [hz, hab]

/-- The classes `c`, `c'` are double cosets of the unitary group of the middle space `X₀`, with
representatives `h_c`, `h_c'`; a rational `γ` lies over the block `(c, s, c')` (`termsOver`) if
`h_c⁻¹ γ h_c'` is integral with reduction `s`. Let such a `γ` have norm-one pairs occurring from
level `0`: for one `ζ` with `ζ ζ̄ = 1`, the frame and its image under `γ` have common vectors with
leading coefficients `ζ`, `1` at every index. Then there is an integral `ζ` with `ζ ζ̄ = 1` such
that `γ` lies in `ζ` times the Bessel subgroup and `s` in `ζ` times the reduction of the Bessel
subgroup (`InScalarCoset`). -/
lemma exists_scalar_mul_besselS {γ : S.G E} {c c' : S.Classes} {s : S.ResidueGL}
    (hγ : γ ∈ S.termsOver c s c') (h_pair : NormOnePairOccursFrom 0 γ) :
    ∃ (ζ : E) (hζ : ζ * star ζ = 1) (h_int : (ζ : 𝔸f E) ∈ Ô E),
      (∃ γ₀ ∈ besselS, γ = scalarIsometry (S.ratMiddle E).splitGram ζ hζ * γ₀) ∧
        S.InScalarCoset ⟨ζ, h_int⟩ s := by
  obtain ⟨k, rfl, hk⟩ :
    ∃ k : S.latticeStabilizer, S.reduction k = s ∧ (k : S.GFin) = S.translateByClassReps c c' γ :=
      hγ
  obtain ⟨ζ, hζ, h_flag⟩ : ∃ ζ : E, ζ * star ζ = 1 ∧
    ∀ a : Fin (𝔰.ϱ + 1), 0 ≤ a.val → PairOccursAt γ ζ 1 a := h_pair
  -- `ζ` is the coefficient of `γ e₁ = ζ e₁`, an entry of the integral matrix `k`.
  have h_int : (ζ : 𝔸f E) ∈ Ô E := by
    simpa only [(h_flag 0 bot_le).apply_besselFrame_zero] using apply_besselFrame_zero_mem_Ô hk
  let γ₀ : S.G E := (scalarIsometry (S.ratMiddle E).splitGram ζ hζ)⁻¹ * γ
  have hγ₀ : γ₀ ∈ besselS := scalarIsometry_inv_mul_mem_besselS hζ fun a ↦ h_flag a bot_le
  -- The scalar `ζ` as an element `z` of the stabilizer of the lattice; `k = z k₀`.
  have hζ_fin : (ζ : 𝔸f E) * star (ζ : 𝔸f E) = 1 := by
    simpa using congrArg (algebraMap E (𝔸f E)) hζ
  let z : S.latticeStabilizer := ⟨scalarIsometry _ (ζ : 𝔸f E) hζ_fin,
    mem_intGL.2 ⟨IsIntMatrix.smul h_int .one, IsIntMatrix.smul (star_mem_Ô h_int) .one⟩⟩
  let k₀ : S.latticeStabilizer := z⁻¹ * k
  have hk₀ : (k₀ : S.GFin) = S.translateByClassReps c c' γ₀ := by
    refine Subtype.ext (Units.ext ?_)
    have hk₀_val : ((k₀ : S.GFin) : GL 𝔰.BesselIndex (𝔸f E)).val =
        star (ζ : 𝔸f E) • ((k : S.GFin) : GL 𝔰.BesselIndex (𝔸f E)).val :=
      val_scalarIsometry_inv_mul _ hζ_fin (k : S.GFin)
    have hγ₀_val : (γ₀ : GL 𝔰.BesselIndex E).val = star ζ • (γ : GL 𝔰.BesselIndex E).val :=
      val_scalarIsometry_inv_mul _ hζ γ
    rw [hk₀_val, hk, coe_translateByClassReps, coe_translateByClassReps]
    simp [hγ₀_val, Matrix.map_smul' _ _ _ (map_mul (algebraMap E (𝔸f E)))]
  have hk₀_mem : (k₀ : S.GFin) ∈ besselS := by
    simpa [hk₀] using translateByClassReps_mem_besselS hγ₀ c c'
  refine ⟨ζ, hζ, h_int, ⟨γ₀, hγ₀, (mul_inv_cancel_left _ γ).symm⟩, S.reduction k₀,
    ⟨k₀, hk₀_mem, rfl⟩, fun i w ↦ ?_⟩
  calc (S.reduction k i w).val = (S.reduction z i w).val * (S.reduction k₀ i w).val := by
        rw [← Units.val_mul, ← Pi.mul_apply, ← Pi.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = New.reduceAt (w : FinPlace E) ⟨ζ, h_int⟩ • (S.reduction k₀ i w).val := by
      rw [val_reduction_of_eq_smul_one (z := z) (ζ := ⟨ζ, h_int⟩) rfl, smul_one_mul]

/-- An integral element of the Bessel subgroup fixes the first frame vector `e₁`. -/
lemma apply_besselFrame_zero_of_mem_besselS {k : S.latticeStabilizer} (hk : (k : S.GFin) ∈ besselS)
    (j : 𝔰.BesselIndex) : (k : S.GFin).val j (𝔰.besselFrame 0) =
      (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)) j (𝔰.besselFrame 0) :=
  mem_besselS_iff_frameImage.1 hk j 0 bot_le

/-- An element `t` of the reduction of the Bessel subgroup fixes the first frame vector modulo
every chosen place `w`: its column there is that of the identity matrix. -/
lemma apply_besselFrame_zero_of_mem_reducedImage {t : S.ResidueGL} (ht : t ∈ S.reducedImage besselS)
    (i : Fin 2) (w : S.chosenPlaces i) (j : 𝔰.BesselIndex) :
    (t i w).val j (𝔰.besselFrame 0) =
      (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (ResField (w : FinPlace E))) j
        (𝔰.besselFrame 0) := by
  obtain ⟨k, hk, rfl⟩ := ht
  simpa using reduction_apply_congr 1 i w (apply_besselFrame_zero_of_mem_besselS hk j)

/-- Let `s` coincide, at the chosen places above `p_i`, with an element `t` of the reduction of the
Bessel subgroup. Then modulo each such place `w`, and modulo its conjugate (`isConj = true`), the
span of the frame and its image under `s` share a nonzero vector (`MeetsAt`), namely the first
frame vector. -/
lemma meetsAt_of_eq_of_mem_reducedImage {s t : S.ResidueGL} (ht : t ∈ S.reducedImage besselS)
    {i : Fin 2} (hs : s i = t i) (w : S.chosenPlaces i) (isConj : Bool) :
    S.MeetsAt s (⟨i, w⟩, isConj) := by
  obtain ⟨k, hk, rfl⟩ : ∃ k : S.latticeStabilizer, (k : S.GFin) ∈ besselS ∧ S.reduction k = t := ht
  have h_action : S.actionAt s (⟨i, w⟩, isConj) = S.actionAt (S.reduction k) (⟨i, w⟩, isConj) := by
    simp only [actionAt, hs]
  refine ⟨Pi.single 0 1, Pi.single 0 1, by simp, funext fun j ↦ ?_⟩
  have h_col : (k : S.GFin).val j (𝔰.besselFrame 0) = if j = 𝔰.besselFrame 0 then 1 else 0 := by
    rw [apply_besselFrame_zero_of_mem_besselS hk j, Matrix.one_apply]
  rw [h_action, actionAt_reduction, mulVec_single_one, mulVec_single_one]
  obtain rfl | hj := eq_or_ne j (𝔰.besselFrame 0)
  · simp [h_col, ← Submonoid.one_def, Matrix.one_apply]
  · simp [hj, h_col, ← ZeroMemClass.zero_def]

/-- An element `s` of `ζ` times the reduction of the Bessel subgroup is not open (`IsOpenElement`):
at every chosen place the leading minor of size `1` of the products of the frame with its image
under `s` vanishes. -/
lemma InScalarCoset.not_isOpenElement {ζ : Ô E} {s : S.ResidueGL} (hs : S.InScalarCoset ζ s) :
    ¬S.IsOpenElement s := by
  rintro ⟨w, hw⟩
  obtain ⟨t, ht, h_eq⟩ : ∃ t ∈ S.reducedImage besselS, ∀ (i : Fin 2) (v : S.chosenPlaces i),
    (s i v).val = New.reduceAt (v : FinPlace E) ζ • (t i v).val := hs
  have hϱ : 0 < 𝔰.ϱ := pos_of_gt S.ten_pow_five_le_varrho
  have h_col (j : 𝔰.BesselIndex) (hj : j ≠ 𝔰.besselFrame 0) :
      (s 0 w).val j (𝔰.besselFrame 0) = 0 := by
    simp [h_eq, apply_besselFrame_zero_of_mem_reducedImage ht, hj]
  exact hw ⟨1, Nat.succ_lt_succ hϱ⟩ (leadingMinor_frameGram_eq_zero _ hϱ h_col one_pos)

lemma inScalarCoset_one {s : S.ResidueGL} (hs : s ∈ S.reducedImage besselS) : S.InScalarCoset 1 s :=
  ⟨s, hs, by simp⟩

/-- If `s` is not in the reduction of the Bessel subgroup, the terms in the Bessel subgroup
contribute `0` to every block `(c, s, c')`, as none of them lies over it. -/
lemma amplitudeSum_besselS_eq_zero {side : FullOrCut} {s : S.ResidueGL}
    (hs : s ∉ S.reducedImage besselS)
    (c c' : S.Classes) : S.amplitudeSum side (S.ratMiddle E).besselS c s c' = 0 := by
  have h_empty : IsEmpty ↥(((S.ratMiddle E).besselS : Set (S.G E)) ∩ S.termsOver c s c') := by
    refine ⟨?_⟩
    rintro ⟨γ, hγ, k, rfl, hk⟩
    have hk_mem : (k : S.GFin) ∈ besselS := by
      simpa [hk] using translateByClassReps_mem_besselS hγ c c'
    exact hs ⟨k, hk_mem, rfl⟩
  rw [amplitudeSum, tsum_empty]

/-- The complement of the Bessel subgroup is stable under multiplication by the unipotent group
`besselU` on both sides. -/
lemma isStable_compl_besselS :
    S.IsStable ((S.ratMiddle E).besselS : Set (S.G E))ᶜ :=
  fun u hu u' hu' γ ↦ (S.isStable_besselS u hu u' hu' γ).not

/-- An integral `ζ ∈ E`
with `ζ ζ̄ = 1` that is `1` modulo every place of
`chosenPlaces i`, the finite places of norm `p_i = levelPrime i` chosen in `S`, is `1`. -/
lemma eq_one_of_reduceAt_scalar_eq_one {ζ : E}
    (hζ : ζ * star ζ = 1) (h_int : (ζ : 𝔸f E) ∈ Ô E) (i : Fin 2)
    (h_residue : ∀ w : S.chosenPlaces i, New.reduceAt (w : FinPlace E) ⟨ζ, h_int⟩ = 1) : ζ = 1 := by
  -- View `ζ` as an isometry `z` of the standard lattice of rank one and apply freeness to it.
  let z : U (stdSpace E Unit).J := scalarIsometry (stdSpace E Unit).J ζ hζ
  let x : Gf E Unit := 1⁻¹ * stdEmbFin z * 1
  have h_mem : x ∈ stdLevel E Unit := mem_stdLevel.2 fun _ _ ↦ by
    simpa [x, z, scalarIsometry] using h_int
  have h_red (w : S.chosenPlaces i) : stdLevel.reduceAt (w : FinPlace E) ⟨x, h_mem⟩ = 1 := by
    ext
    simpa [stdLevel.reduceAt, x, z, scalarIsometry] using h_residue w
  have hz : z = 1 := S.eq_one_of_reduceAt_eq_one (by simp; linarith [S.thousand_mul_le_k]) i h_mem
    h_red
  simpa [z, scalarIsometry] using congrArg (fun g : U (stdSpace E Unit).J ↦ g.val () ()) hz

/-- The product `k f` of the rank `k` of `X₀` and the number `f` of infinite places of `E` is at
least `40`. -/
lemma forty_le_k_mul_numInfPlaces (S : Filling E 𝔰) : 40 ≤ 𝔰.k * Core.numInfPlaces E :=
  le_mul_of_le_of_one_le (by linarith [S.thousand_mul_le_k]) NeZero.one_le

/-- The set `Ω` is disjoint from the cosets `ζ R̄₀` of the reduction `R̄₀` of the Bessel subgroup,
for all integral `ζ ≠ 1` in `E` with `ζ ζ̄ = 1`. -/
def AvoidsScalarCosets (S : Filling E 𝔰) (Ω : Set S.ResidueGL) : Prop :=
  ∀ (ζ : E) (h_int : (ζ : 𝔸f E) ∈ Ô E), ζ * star ζ = 1 → ζ ≠ 1 →
    ∀ s ∈ Ω, ¬S.InScalarCoset ⟨ζ, h_int⟩ s

/-- Let `Ω` avoid the cosets of the reduction of the Bessel subgroup by the roots of unity `ζ ≠ 1`.
Then no `γ` off the Bessel subgroup that lies over a block `(c, s, c')` with `s ∈ Ω` has a norm-one
pair occurring from level `0`: such a `γ` is `ζ` times an element of the Bessel subgroup, and
`ζ = 1`. -/
lemma AvoidsScalarCosets.not_normOnePairOccursFrom_zero {Ω : Set S.ResidueGL}
    (hΩ : S.AvoidsScalarCosets Ω)
    (γ : S.G E) (h_off : γ ∈ ((S.ratMiddle E).besselS : Set (S.G E))ᶜ) (c c' : S.Classes)
    (s : S.ResidueGL) (hs : s ∈ Ω) (hγ : γ ∈ S.termsOver c s c') : ¬NormOnePairOccursFrom 0 γ := by
  intro h_pair
  obtain ⟨ζ, hζ, h_int, ⟨γ₀, hγ₀, rfl⟩, h_coset⟩ := exists_scalar_mul_besselS hγ h_pair
  obtain rfl : ζ = 1 := by_contra fun h_ne ↦ hΩ ζ h_int hζ h_ne s hs h_coset
  exact h_off (by simpa [scalarIsometry_one] using hγ₀)

/-- An element `γ` of the Bessel subgroup has a norm-one pair occurring from level `0`: at every
index, the frame and its image under `γ` have a common vector with both leading coefficients `1`. -/
lemma normOnePairOccursFrom_zero_of_mem_besselS {γ : S.G E} (hγ : γ ∈ besselS) :
    NormOnePairOccursFrom 0 γ := by
  refine ⟨1, by simp, fun a _ ↦ ?_⟩
  -- The vector `γ e_a` is `e_a` plus earlier frame vectors.
  let F : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) E := frameImage (γ : GL 𝔰.BesselIndex E).val
  have h_col (i : 𝔰.BesselIndex) (hi : a.val ≤ BesselIndex.level i) : F i a = frameImage 1 i a :=
    mem_besselS_iff_frameImage.1 hγ i a hi
  let x (b : Fin (𝔰.ϱ + 1)) : E := F (𝔰.besselFrame b) a
  have hx (b : Fin (𝔰.ϱ + 1)) (hb : a ≤ b) : x b = if b = a then 1 else 0 := by
    simpa [x, Matrix.one_apply, besselFrame_injective.eq_iff] using
      h_col (𝔰.besselFrame b) (by rwa [level_besselFrame])
  -- It has no part in `X₀` or along the dual vectors.
  have h_off (i : 𝔰.BesselIndex) (hi : 𝔰.ϱ ≤ BesselIndex.level i) (h_ne : i ≠ 𝔰.z) :
      F i a = 0 := by
    refine (h_col i (a.is_le.trans hi)).trans (one_apply_ne fun h : i = 𝔰.besselFrame a ↦ ?_)
    rw [h, level_besselFrame] at hi
    exact h_ne (by rw [h, Fin.last_le_iff.1 hi, besselFrame_top])
  have h_common : frameImage 1 *ᵥ x = F *ᵥ Pi.single a 1 := by
    rw [frameImage_one_mulVec, mulVec_single_one]
    -- The rows at `e₁, …, e_ϱ`, in `X₀`, at the last frame vector and at the dual vectors.
    ext (b | (j | j) | b)
    · simp [x, Fin.init]
    · exact (h_off (.inr (.inl (.inl j))) le_rfl (by simp)).symm
    · simp [x]
    · exact (h_off (.inr (.inr b)) (show 𝔰.ϱ ≤ 2 * 𝔰.ϱ - b.val by lia) (by simp)).symm
  exact ⟨x, Pi.single a 1, h_common, by simp [hx], by simp, fun b hb ↦ by simp [hx b hb.le, hb.ne']⟩

/-! ### The blocks of the Bessel subgroup -/

/-- Let `u` lie in the unipotent group `besselU`. At each infinite place `v`, let the image
`ratToInf η v` of `η` be `embedH (k v)`: the unitary matrix `k v` in `U(κ)` acts on `X₀` and the
other basis vectors are fixed. Then, for either `side` (full or cut), left translation by the image
of `u η` multiplies the values of `besselFn` by the tensor product (`kroneckerPi`) of the matrices
`rep (k v)` of the local Bessel systems `besselSystem v`, divided by `unipotentChar` of the finite
adelic image `ratToFin u`. -/
lemma besselFn_mul_of_eq_embedH {side : FullOrCut} {u η : S.G E} (hu : u ∈ besselU)
    {k : NumberField.InfinitePlace E → U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)}
    (hk : ∀ v : NumberField.InfinitePlace E, S.ratToInf η v = RealPlace.embedH (k v))
    (y : NumberField.InfinitePlace E → 𝔰.G₁) :
    S.besselFn side (S.ratToInf (u * η) * y) = ((S.unipotentChar (S.ratToFin u))⁻¹ •
      kroneckerPi fun v : NumberField.InfinitePlace E ↦ ((S.besselSystem v).rep (k v)).val) *ᵥ
        S.besselFn side y := by
  rw [map_mul, mul_assoc, besselFn_ratToInf_mul hu, smul_mulVec]
  have h_map (v : NumberField.InfinitePlace E) (h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) (z : 𝔰.G₁) :
      (S.besselSystem v).besselFn side (RealPlace.embedH h * z) =
        toEuclideanCLM (𝕜 := ℂ) ((S.besselSystem v).rep h).1 ((S.besselSystem v).besselFn side z) :=
    ((S.besselSystem v).isCutPair.isBesselFunction side).map_unitary_mul h z
  ext
  simp [besselFn, hk, h_map, kroneckerPi, mulVec, dotProduct, Fintype.prod_sum, prod_mul_distrib]

/-- For `side` either the full Bessel function or its cut, an element `γ` of the Bessel subgroup
`besselS` acts on the values of `besselFn side` by a unitary matrix. That is, there is a unitary `M`
indexed by `BesselCoord` with `besselFn side (ratToInf γ * y) = M *ᵥ besselFn side y` for all
`y`. -/
lemma exists_unitary_besselFn_mul {side : FullOrCut} {γ : S.G E} (hγ : γ ∈ besselS) :
    ∃ M ∈ unitaryGroup S.BesselCoord ℂ, ∀ y : NumberField.InfinitePlace E → 𝔰.G₁,
      S.besselFn side (S.ratToInf γ * y) = M *ᵥ S.besselFn side y := by
  obtain ⟨u, hu, η, hη, rfl⟩ := mem_besselS.1 hγ
  choose k hk using fun v ↦ exists_eq_toBesselH (hη.ratToInf_mem_agreeWithOneOn v) isUnit_one
  refine ⟨_, ?_, besselFn_mul_of_eq_embedH hu hk⟩
  -- A scalar of modulus one times a tensor product of unitary matrices is unitary.
  have h_star : star (kroneckerPi fun v ↦ ((S.besselSystem v).rep (k v)).val) =
      kroneckerPi fun v ↦ star ((S.besselSystem v).rep (k v)).val :=
    Matrix.ext fun _ _ ↦ by simp [kroneckerPi]
  have h_norm : ‖S.unipotentChar (S.ratToFin u)‖ = 1 := norm_selfDualChar
  rw [mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm, h_star, ← kroneckerPi_mul,
    Complex.star_def, mul_conj', norm_inv, h_norm]
  simp [kroneckerPi_one]

open scoped Classical in
/-- Let `E` contain a primitive `5040`-th root of unity and let the filling `S` be admissible
(`IsAdmissible`). The classes `c` index the double cosets of the unitary group of `X₀`, with
representatives `h_c`, and `termsOver c s c'` is the set of rational `γ` with `h_c⁻¹ γ h_c'`
integral of reduction `s`: these lie over the block `(c, s, c')`. Let `γ` in the Bessel subgroup
`besselS` lie over it and act on the values of the full Bessel function by the matrix `M`, whose
indices `BesselCoord` are the coordinates of those values. Then the sum of amplitudes
(`amplitudeSum`, for the full function) of the terms in the Bessel subgroup is
`unipotentCovolume • M` over this block and `0` over the blocks `(c, s, d)` with `d ≠ c'`; here
`unipotentCovolume` is the positive constant that stands for the covolume of the unipotent lattice
at a class. -/
lemma amplitudeSum_besselS_apply [HasPrimitiveRoot5040 E] [S.IsAdmissible] {γ : S.G E}
    {c c' : S.Classes} {s : S.ResidueGL} (hγ : γ ∈ besselS) (hγ_over : γ ∈ S.termsOver c s c')
    {M : Matrix S.BesselCoord S.BesselCoord ℂ}
    (hM : ∀ y : NumberField.InfinitePlace E → 𝔰.G₁,
      S.besselFn .full (S.ratToInf γ * y) = M *ᵥ S.besselFn .full y)
    (d : S.Classes) (i j : S.BesselCoord) :
    S.amplitudeSum .full (S.ratMiddle E).besselS c s d (i, j) =
      if c' = d then S.unipotentCovolume * M i j else 0 := by
  -- Translation by `γ` moves the block `(c', 1, d)` to `(c, s, d)` and acts by `M ⊗ 1`.
  let L := toEuclideanCLM (n := S.BesselCoord × S.BesselCoord) (𝕜 := ℂ) (kronecker M 1)
  have hL (x : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord)) (a b : S.BesselCoord) :
      L x (a, b) = ∑ k : S.BesselCoord, M a k * x (k, b) := by
    simp [L, mulVec, dotProduct, Matrix.one_apply, sum_prod_type]
  have h_kernel (δ : S.G E) (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      S.besselKernel .full (γ * δ * 1⁻¹) (S.ratToInf γ * y) = L (S.besselKernel .full δ y) := by
    ext ⟨a, b⟩
    simp [hL, besselKernel, mul_assoc, hM, mulVec, dotProduct, sum_mul]
  have h_move : S.amplitudeSum .full (S.ratMiddle E).besselS c s d =
      L (S.amplitudeSum .full (S.ratMiddle E).besselS c' 1 d) := by
    simpa using amplitudeSum_mul_mul_inv isStable_besselS hγ hγ_over (one_mem _)
      (S.classUnipotent d).one_mem.2 (by simp [hγ, mul_mem_cancel_left]) L h_kernel 1
  rw [h_move, hL]
  split_ifs with h <;> simp [h, amplitudeSum_besselS_one_eq_ite, apply_ite, mul_comm]

/-- Let `E` contain a primitive `5040`-th root of unity and let the filling `S` be admissible
(`IsAdmissible`). For classes `c`, `d` and `s` in `ResidueGL`, a term lies over the block
`(c, s, d)` (`termsOver`) if `h_c⁻¹ γ h_d` is integral with reduction `s`. The sum of amplitudes
(`amplitudeSum`, for the full Bessel function) of the terms in the Bessel subgroup `besselS` over
`(d, s⁻¹, c)` is the adjoint of that over `(c, s, d)`, as a matrix indexed by the coordinates of the
Bessel function. -/
lemma amplitudeSum_besselS_inv [HasPrimitiveRoot5040 E] [S.IsAdmissible] (c d : S.Classes)
    (s : S.ResidueGL) (i j : S.BesselCoord) :
    S.amplitudeSum .full (S.ratMiddle E).besselS d s⁻¹ c (j, i) =
      star (S.amplitudeSum .full (S.ratMiddle E).besselS c s d (i, j)) := by
  by_cases h : ∃ γ ∈ (S.ratMiddle E).besselS, γ ∈ S.termsOver c s d
  · -- If `γ` acts by the unitary matrix `M`, then `γ⁻¹` acts by its adjoint.
    obtain ⟨γ, hγ, hγ_over⟩ := h
    obtain ⟨M, hM_unitary, hM⟩ := exists_unitary_besselFn_mul (side := .full) hγ
    have hM_inv (y : NumberField.InfinitePlace E → 𝔰.G₁) :
        S.besselFn .full (S.ratToInf γ⁻¹ * y) = star M *ᵥ S.besselFn .full y := by
      rw [← mul_inv_cancel_left (S.ratToInf γ) y, hM]
      simp [mem_unitaryGroup_iff'.1 hM_unitary]
    simp [amplitudeSum_besselS_apply hγ hγ_over hM,
      amplitudeSum_besselS_apply (inv_mem hγ) (termsOver.inv hγ_over) hM_inv]
  · have h_empty : IsEmpty ↥(((S.ratMiddle E).besselS : Set (S.G E)) ∩ S.termsOver c s d) :=
      ⟨fun γ ↦ h ⟨γ, γ.property⟩⟩
    have h_empty_inv : IsEmpty ↥(((S.ratMiddle E).besselS : Set (S.G E)) ∩ S.termsOver d s⁻¹ c) :=
      ⟨fun ⟨γ, hγ, hγ_over⟩ ↦ h ⟨γ⁻¹, inv_mem hγ, by simpa using termsOver.inv hγ_over⟩⟩
    simp [amplitudeSum, tsum_empty]

/-- Let `E` contain a primitive `5040`-th root of unity and let the filling `S` be admissible
(`IsAdmissible`). Let `δ` in the Bessel subgroup lie over `(d, t, d')` and act on the values of the
full Bessel function by `N`, and let `T` be a set of terms that is stable with `T δ = T`. Then the
sum of amplitudes of `T`, for the full function, over `(c, s t⁻¹, d)` is `A Nᴴ`, where `A` is that
over `(c, s, d')`. -/
lemma amplitudeSum_mul_inv_apply [HasPrimitiveRoot5040 E] [S.IsAdmissible] {T : Set (S.G E)}
    (hT : S.IsStable T) {δ : S.G E} {d d' : S.Classes} {t : S.ResidueGL} (hδ : δ ∈ besselS)
    (hδ_over : δ ∈ S.termsOver d t d') (hT_mul_inv : ∀ γ : S.G E, γ ∈ T ↔ γ * δ⁻¹ ∈ T)
    {N : Matrix S.BesselCoord S.BesselCoord ℂ}
    (hN : ∀ y : NumberField.InfinitePlace E → 𝔰.G₁,
      S.besselFn .full (S.ratToInf δ * y) = N *ᵥ S.besselFn .full y)
    (c : S.Classes) (s : S.ResidueGL) (i j : S.BesselCoord) :
    S.amplitudeSum .full T c (s * t⁻¹) d (i, j) =
      ∑ k : S.BesselCoord, star (N j k) * S.amplitudeSum .full T c s d' (i, k) := by
  -- Translation by `δ⁻¹` on the right acts on the kernel by `1 ⊗ conj N`.
  let L := toEuclideanCLM (n := S.BesselCoord × S.BesselCoord) (𝕜 := ℂ) (kronecker 1 (N.map star))
  have hL (x : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord)) (a b : S.BesselCoord) :
      L x (a, b) = ∑ k : S.BesselCoord, star (N b k) * x (a, k) := by
    simp [L, mulVec, dotProduct, Matrix.one_apply, sum_prod_type]
  have h_kernel (γ : S.G E) (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      S.besselKernel .full (1 * γ * δ⁻¹) (S.ratToInf 1 * y) = L (S.besselKernel .full γ y) := by
    ext ⟨a, b⟩
    simpa [hL, besselKernel, mul_assoc, hN, mulVec, dotProduct, mul_sum] using
      Finset.sum_congr rfl fun _ _ ↦ mul_left_comm ..
  have h_move : S.amplitudeSum .full T c (s * t⁻¹) d = L (S.amplitudeSum .full T c s d') := by
    simpa using amplitudeSum_mul_mul_inv hT (one_mem _) (S.classUnipotent c).one_mem.2 hδ hδ_over
      (by simpa using hT_mul_inv) L h_kernel s
  rw [h_move, hL]

/-! ### The expansion of the squares and the second moment near `R̄₀` -/

/-- Let `E` contain a primitive `5040`-th root of unity and let the filling `S` be admissible
(`IsAdmissible`). Let `Ω` avoid the cosets `ζ R̄₀` of the roots of unity `ζ ≠ 1`, and let `s ∈ Ω`.
Then over each block at `s` the terms off the Bessel subgroup `besselS` have the same sum of
amplitudes as the terms of `Γ* = remainingTerms`. These are the `γ` with `termDisc γ ≠ 0`, and those
with agreeing characters that move the span of the isotropic frame vectors `e₁, …, e_ϱ`. -/
lemma AvoidsScalarCosets.amplitudeSum_compl_besselS_eq [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {side : FullOrCut} {Ω : Set S.ResidueGL} (hΩ : S.AvoidsScalarCosets Ω) {s : S.ResidueGL}
    (hs : s ∈ Ω) (c c' : S.Classes) :
    S.amplitudeSum side (S.ratMiddle E).besselSᶜ c s c' =
      S.amplitudeSum side S.remainingTerms c s c' := by
  -- The terms off `R₀` and `Γ*` whose characters do not agree (`CharsAgree` fails) form a stable
  -- set with sum `0`. One whose characters agree has a norm-one pair occurring from level `0`, so
  -- lies over no block at `s`.
  set offBessel : Set (S.G E) := ((S.ratMiddle E).besselS : Set (S.G E))ᶜ
  set agreeing : Set (S.G E) := {γ | S.CharsAgree γ}
  have h_sub : offBessel ∩ S.remainingTerms = S.remainingTerms :=
    Set.inter_eq_right.2 fun γ hγ h_mem ↦
      (normOnePairOccursFrom_zero_of_mem_besselS h_mem).notMem_remainingTerms hγ
  have h_stable : S.IsStable (offBessel ∩ S.remainingTermsᶜ ∩ agreeingᶜ) := fun u hu u' hu' γ ↦ by
    simp only [Set.mem_inter_iff, Set.mem_compl_iff S.remainingTerms, Set.mem_compl_iff agreeing]
    rw [isStable_compl_besselS u hu u' hu' γ, isStable_remainingTerms u hu u' hu' γ]
    simp only [offBessel, agreeing, Set.mem_ofPred_eq,
      charsAgree_mul_mul_iff_of_mem_besselU (inv_mem hu) hu']
  have h_disagree : S.amplitudeSum side (offBessel ∩ S.remainingTermsᶜ ∩ agreeingᶜ) c s c' = 0 :=
    amplitudeSum_eq_zero_of_not_charsAgree h_stable (fun γ hγ ↦ hγ.2) c s c'
  have h_empty : IsEmpty ↥(offBessel ∩ S.remainingTermsᶜ ∩ agreeing ∩ S.termsOver c s c') :=
    ⟨fun ⟨γ, ⟨⟨h_off, h_out⟩, h_agree⟩, h_over⟩ ↦
      hΩ.not_normOnePairOccursFrom_zero γ h_off c c' s hs h_over
      (CharsAgree.normOnePairOccursFrom_zero h_agree h_out)⟩
  have h_agree : S.amplitudeSum side (offBessel ∩ S.remainingTermsᶜ ∩ agreeing) c s c' = 0 :=
    tsum_empty
  rw [amplitudeSum_eq_inter_compl_add_inter offBessel S.remainingTerms, h_sub,
    amplitudeSum_eq_inter_compl_add_inter (offBessel ∩ S.remainingTermsᶜ) agreeing]
  simp [h_disagree, h_agree]

/-- Let `E` contain a primitive `5040`-th root of unity, let the filling `S` be admissible
(`IsAdmissible`), and let `Ω` avoid the cosets of the reduction of the Bessel subgroup by the roots
of unity `ζ ≠ 1`. For each block over `Ω` and each link, sum the amplitudes for the cut Bessel
function of the terms with that link and nonzero `termDisc`; let the squared norms of these sums
(`linkSecondMoment`) add up to at most `C unipotentCovolume²`, with `C ≥ 0` and the positive
constant `unipotentCovolume` that stands for the covolume of the unipotent lattice at a class. Then
the second moment over `Ω` of the terms off the Bessel subgroup, for the full Bessel function, has
square root at most `C^(1/2) + b⁻¹⁵ 𝒟_id^(1/2)`, where `b = S.b` and `𝒟_id = identitySecondMoment`
is the order of the reduction of the Bessel subgroup times the number `sourceDim` of pairs of a
class and a coordinate. -/
theorem sqrt_secondMoment_compl_besselS_le [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {Ω : Set S.ResidueGL} (hΩ : S.AvoidsScalarCosets Ω) {C : ℝ} (hC : 0 ≤ C)
    (h_links : linkSecondMoment {γ : S.G E | S.termDisc γ ≠ 0} Ω ≤ .ofReal
      (C * S.unipotentCovolume ^ 2)) :
    √(secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) Ω) ≤
      √C + (S.b ^ 15)⁻¹ * √S.identitySecondMoment := by
  classical
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have h_id_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  set remaining : Set (S.G E) := S.remainingTerms
  -- Over `Ω` the blocks of `P_s - r_ψ(s)` are those of `Γ*`.
  have h_blocks : secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) Ω =
      secondMoment (S.amplitudeSum .full remaining) Ω :=
    sum_congr rfl fun c _ ↦ sum_congr rfl fun c' _ ↦ sum_congr rfl fun s hs ↦ by
      rw [hΩ.amplitudeSum_compl_besselS_eq (mem_filter.1 hs).2]
  have h_sqrt : √((S.b ^ 40)⁻¹ * S.identitySecondMoment) = (S.b ^ 20)⁻¹ *
    √S.identitySecondMoment := by
    rw [Real.sqrt_mul' _ h_id_nonneg, Real.sqrt_inv, pow_mul _ 20 2, Real.sqrt_sq (by positivity)]
  -- The pairs of terms with the same link give `C`, the other pairs at most `b^(-kf) 𝒟_id`.
  have h_pairs : secondMoment (S.amplitudeSum .cut remaining) Ω ≤ C + (S.b ^ 40)⁻¹ *
    S.identitySecondMoment := by
    grw [secondMoment_remainingTerms_le hC h_links,
      ← pow_le_pow_right₀ S.one_le_b S.forty_le_k_mul_numInfPlaces, div_eq_inv_mul]
  have h_small : 2 * (S.b ^ 5)⁻¹ ≤ 1 := by
    grw [← hb]
    norm_num
  calc _ ≤ √(secondMoment (S.amplitudeSum .full remaining - S.amplitudeSum .cut remaining) Ω) +
        √(secondMoment (S.amplitudeSum .cut remaining) Ω) := by
        grw [h_blocks, ← sqrt_secondMoment_add_le, sub_add_cancel]
    -- Passing to the cut function costs `b⁻²⁰ 𝒟_id^(1/2)`.
    _ ≤ (S.b ^ 20)⁻¹ * √S.identitySecondMoment + (√C + (S.b ^ 20)⁻¹ * √S.identitySecondMoment) := by
      grw [secondMoment_sub_cut_le, h_pairs, Real.sqrt_add_le_add_sqrt, h_sqrt]
    _ = √C + 2 * (S.b ^ 5)⁻¹ * ((S.b ^ 15)⁻¹ * √S.identitySecondMoment) := by ring
    _ ≤ √C + (S.b ^ 15)⁻¹ * √S.identitySecondMoment := by grw [h_small, one_mul]

/-- Let `s` coincide at the chosen places above `p_i = levelPrime i` with an element `t` of
`reducedImage besselS`, the reduction of the Bessel subgroup. Then the product of the norms
`p_i` of these places and their conjugates is at most `meetNorm s`, the product of the norms of the
places at which `s` meets, as `s` meets at each of them. -/
lemma prod_levelPrime_le_meetNorm_of_eq
    {s t : S.ResidueGL} (ht : t ∈ S.reducedImage besselS) {i : Fin 2} (hs : s i = t i) :
    ∏ _ : S.chosenPlaces i × Bool, S.levelPrime i ≤ S.meetNorm s := by
  classical
  let φ (p : S.chosenPlaces i × Bool) : (Σ j, S.chosenPlaces j) × Bool := (⟨i, p.1⟩, p.2)
  have hφ : φ.Injective := fun p p' h ↦ by simpa [φ, Prod.ext_iff] using h
  have h_meet : ∀ p ∈ univ.image φ, S.MeetsAt s p :=
    forall_mem_image.2 fun p _ ↦ meetsAt_of_eq_of_mem_reducedImage ht hs p.1 p.2
  exact (prod_image hφ.injOn).symm.trans_le (prod_le_meetNorm h_meet)

/-- The set of the `s` that coincide with an element of `R̄₀`, the reduction of the Bessel subgroup,
at the chosen places above `p_i` avoids the cosets `ζ R̄₀` with `ζ ≠ 1`: such an `s` fixes the first
frame vector there, so `ζ` is `1` modulo these places. -/
lemma avoidsScalarCosets_setOf_exists_apply_eq
    (i : Fin 2) : S.AvoidsScalarCosets
      {s : S.ResidueGL | ∃ t ∈ S.reducedImage besselS, s i = t i} := by
  rintro ζ h_int hζ h_ne s ⟨t, ht, hs⟩ ⟨t', ht', h_coset⟩
  refine h_ne (S.eq_one_of_reduceAt_scalar_eq_one hζ h_int i fun w ↦ ?_)
  have h_entry : (s i w).val (𝔰.besselFrame 0) (𝔰.besselFrame 0) =
      New.reduceAt w.val ⟨ζ, h_int⟩ * (t' i w).val (𝔰.besselFrame 0) (𝔰.besselFrame 0) := by
    rw [h_coset i w, Matrix.smul_apply, smul_eq_mul]
  rw [hs, apply_besselFrame_zero_of_mem_reducedImage ht,
    apply_besselFrame_zero_of_mem_reducedImage ht', one_apply_eq, mul_one] at h_entry
  exact h_entry.symm

/-- Each level prime `levelPrime i` is at most `b` times the other, so `M / b ≤ p_i ^ 2`, with
`p_i = levelPrime i`, for the level `M = p₀ p₁`. -/
lemma M_div_b_le_levelPrime_sq (i : Fin 2) : S.M / S.b ≤ (S.levelPrime i : ℝ) ^ 2 := by
  have hb : 0 < S.b := one_pos.trans_le S.one_le_b
  have h_le (j : Fin 2) : (S.levelPrime j : ℝ) ≤ S.levelPrime i * S.b := by
    grw [S.levelPrime_le j, ← S.le_levelPrime i, ← pow_succ]
  rw [div_le_iff₀ hb, M, Nat.cast_mul, sq, mul_assoc]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · grw [h_le 1]
  · grw [mul_comm, h_le 0]

/-- The second moment near the Bessel subgroup. Let `E` contain a primitive `5040`-th root of unity
and let the filling `S` be admissible (`IsAdmissible`). Let `Ω` be the set of `s` that coincide with
an element of `R̄₀` at the chosen places above `p_i`. Then the second moment over `Ω` of the terms
off the Bessel subgroup, that is `∑ ‖P_s - r_ψ(s)‖²`, is at most `b⁻¹² 𝒟_id`. Here `P_s` and
`r_ψ(s)` are the operators whose blocks at `s` are the conjugates of the amplitude sums of all terms
and of the terms in the Bessel subgroup, divided by `unipotentCovolume`, `R̄₀` is the reduction of
the Bessel subgroup, `p_i = levelPrime i`, `b` is the parameter `S.b` of the filling and
`𝒟_id = identitySecondMoment = #R̄₀ D_X`, with `D_X = sourceDim` the number of pairs of a class and
a coordinate. -/
theorem secondMoment_compl_besselS_le [HasPrimitiveRoot5040 E] [hS : S.IsAdmissible] (i : Fin 2) :
    secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ)
      {s : S.ResidueGL | ∃ t ∈ S.reducedImage besselS, s i = t i} ≤ (S.b ^ 12)⁻¹ *
        S.identitySecondMoment := by
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have h_id_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_main_nonneg : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  set Ω : Set S.ResidueGL := {s | ∃ t ∈ S.reducedImage besselS, s i = t i}
  set meetBound : ℕ := ∏ _ : S.chosenPlaces i × Bool, S.levelPrime i with h_meetBound_def
  have h_meetBound_ne : meetBound ≠ 0 :=
    prod_ne_zero_iff.2 fun _ _ ↦ (S.levelPrime_prime_and_ne i).1.ne_zero
  -- Every `s ∈ Ω` meets at the `f` chosen places above `p_i` and at their conjugates.
  have h_meet : ∀ s ∈ Ω, meetBound ≤ S.meetNorm s := fun s ⟨t, ht, hs⟩ ↦
    prod_levelPrime_le_meetNorm_of_eq ht hs
  -- With `m = k f`, `meetBound ≥ (M / b)^f` and `𝒟_main ≤ (M / b⁶)^m 𝒟_id`, the sums over links
  -- give at most `(b³ / M)^m (M / b⁶)^m 𝒟_id = b^(-3m) 𝒟_id ≤ b⁻³⁰ 𝒟_id`.
  have h_links : (S.b ^ (2 * Core.numInfPlaces E) / meetBound) ^ 𝔰.k * S.mainSecondMoment ≤
      (S.b ^ 30)⁻¹ * S.identitySecondMoment := by
    have hM : (0 : ℝ) < S.M := Nat.cast_pos.2 (two_pos.trans_le two_le_M)
    have h_meetBound_ge : (S.M / S.b) ^ Core.numInfPlaces E ≤ meetBound := by
      grw [h_meetBound_def, prod_const, card_univ, Fintype.card_prod, S.card_chosenPlaces,
          Fintype.card_bool,
        Nat.cast_pow, pow_mul', M_div_b_le_levelPrime_sq]
    have h_exp : 30 ≤ 3 * (𝔰.k * Core.numInfPlaces E) := by
      linarith [S.forty_le_k_mul_numInfPlaces]
    calc _ ≤ (S.b ^ (2 * Core.numInfPlaces E) / (S.M / S.b) ^ Core.numInfPlaces E) ^ 𝔰.k *
          ((S.M / S.b ^ 6) ^ (𝔰.k * Core.numInfPlaces E) * S.identitySecondMoment) := by
          grw [hS.mainSecondMoment_le, ← h_meetBound_ge]
      _ = (S.b ^ (3 * (𝔰.k * Core.numInfPlaces E)))⁻¹ * S.identitySecondMoment := by
        simp only [div_pow]
        field
      _ ≤ (S.b ^ 30)⁻¹ * S.identitySecondMoment := by grw [pow_le_pow_right₀ S.one_le_b h_exp]
  have h_sqrt : √(secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) Ω) ≤
      2 * (S.b ^ 15)⁻¹ * √S.identitySecondMoment :=
    calc _ ≤ √((S.b ^ (2 * Core.numInfPlaces E) / meetBound) ^ 𝔰.k * S.mainSecondMoment) +
          (S.b ^ 15)⁻¹ * √S.identitySecondMoment :=
          sqrt_secondMoment_compl_besselS_le (avoidsScalarCosets_setOf_exists_apply_eq i)
            (by positivity)
            (linkSecondMoment_le_of_le_meetNorm h_meetBound_ne h_meet)
      _ ≤ √((S.b ^ 30)⁻¹ * S.identitySecondMoment) + (S.b ^ 15)⁻¹ * √S.identitySecondMoment := by
        grw [h_links]
      _ = 2 * (S.b ^ 15)⁻¹ * √S.identitySecondMoment := by
        rw [Real.sqrt_mul' _ h_id_nonneg, Real.sqrt_inv, pow_mul _ 15 2,
          Real.sqrt_sq (by positivity)]
        ring
  have h_small : (2 * (S.b ^ 15)⁻¹) ^ 2 ≤ (S.b ^ 12)⁻¹ := by
    have h_four : 4 ≤ S.b ^ 18 := le_trans (by linarith) (le_self_pow₀ S.one_le_b (by norm_num))
    field_simp
    linarith
  grw [(Real.sqrt_le_iff.1 h_sqrt).2, mul_pow, Real.sq_sqrt h_id_nonneg, h_small]

end Filling

end New
end
end

/-!
# The second moment over the whole group

This file proves the bound on the sum of the second moments of the operators `P_s = P* s P` over the
whole group, stated in terms of their blocks. It bounds the contribution of the cosets of `R̄₀` and
that of the elements that are not open.

The blocks of `P_s` are the complex conjugates of the sums `amplitudeSum` over all terms, divided by
`unipotentCovolume`, so `‖P_s‖²` (Hilbert–Schmidt norm) is the `secondMoment` of these sums at `s`.
In the same way the terms in the Bessel subgroup `R₀ = besselS` give `r_ψ(s)`, and those off it give
`P_s - r_ψ(s)`. The operator `r_ψ(s)` is `New.Filling.besselTranslate`; the passage from operators
to blocks is `New.Filling.HasAmplitudeBlocks`.

We write `R̄₀` for `reducedImage besselS`, `D_X` for `sourceDim`, `𝒟_id` for `identitySecondMoment`,
`𝒟_main` for `mainSecondMoment`, `b` for the parameter `S.b` of the filling, `p_i` for
`levelPrime i`, `M = p₀ p₁` for the level, `f` for the number of infinite places, `k = |κ|`,
`n = ϱ + 1` for the length of the frame, `e₁` for its vector of index `0` and `δ_l` for the leading
minors of `frameGram`. In `InScalarCoset ζ s` the scalar `ζ` is an integral adele, acting through
its residues.

## Main definitions and results

* `New.Filling.sum_secondMoment_le`: `∑ ‖P_s‖² ≤ (1 + 9 b⁻⁴) 𝒟_main`, if `s ↦ ‖P_s‖²` has positive
  type and `‖P_1‖² ≤ 2 D_X`.
* `New.Filling.secondMoment_univ_eq_secondMoment_compl_besselS`: if `Ω` is disjoint from the
  reduction `R̄₀` of the Bessel subgroup, then the terms in the Bessel subgroup give `0` over `Ω`,
  so all terms and the terms off the Bessel subgroup have the same second moment over `Ω`.

Notions from other files:
* `termsOver c s c'`: the rational `γ` such that `h_c⁻¹ γ h_c'` (`translateByClassReps`) is integral
  with reduction `s`; such a `γ` lies over the block `(c, s, c')`.
* `amplitudeSum side T c s c'`: the sum of the amplitudes of the elements of `T` over that block.
* `secondMoment A Ω`: the sum of `‖A c s c'‖² / unipotentCovolume²` over all classes `c`, `c'` and
  `s ∈ Ω`.
* `reducedImage A`: the image in the finite group `ResidueGL` of the integral elements of `A`.
-/

@[expose] public section

namespace New

open Matrix Complex Module InnerProductSpace EuclideanSpace Finset Fintype

attribute [local instance low] Fintype.ofFinite

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

namespace Filling

/-! ### The second moment over the whole group -/

/-- The second moment of a family of blocks at one element `σ`: `unipotentCovolume⁻²` times the sum
of the squared norms of the blocks over `σ`. -/
lemma secondMoment_singleton {V : Type} [NormedAddCommGroup V]
    (A : S.Classes → S.ResidueGL → S.Classes → V) (σ : S.ResidueGL) :
    secondMoment A {σ} = ∑ c : S.Classes, ∑ c' : S.Classes,
      ‖A c σ c'‖ ^ 2 / S.unipotentCovolume ^ 2 :=
  sum_congr rfl fun c _ ↦ sum_congr rfl fun c' _ ↦
    sum_eq_single_of_mem σ (by simp) (by simp +contextual)

/-- The second moment of a family of blocks over a set `Ω` is the sum of its second moments at the
elements of `Ω`. -/
lemma secondMoment_eq_sum_secondMoment_singleton {V : Type} [NormedAddCommGroup V]
    (A : S.Classes → S.ResidueGL → S.Classes → V) (Ω : Set S.ResidueGL) [DecidablePred (· ∈ Ω)] :
    secondMoment A Ω = ∑ s : S.ResidueGL with s ∈ Ω, secondMoment A {s} := by
  simp only [secondMoment_singleton]
  rw [secondMoment, sum_comm_cycle]
  congr!

/-- If `Ω` is disjoint from the reduction `R̄₀` of the Bessel subgroup, then the terms in the Bessel
subgroup give `0` over `Ω`, so all terms and the terms off the Bessel subgroup have the same second
moment over `Ω`. -/
lemma secondMoment_univ_eq_secondMoment_compl_besselS [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {Ω : Set S.ResidueGL} (hΩ : ∀ s ∈ Ω, s ∉ S.reducedImage besselS) :
    secondMoment (S.amplitudeSum .full Set.univ) Ω =
      secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) Ω := by
  classical
  rw [amplitudeSum_eq_inter_compl_add_inter Set.univ (S.ratMiddle E).besselS, Set.univ_inter,
    Set.univ_inter]
  refine sum_congr rfl fun c _ ↦ sum_congr rfl fun c' _ ↦ sum_congr rfl fun s hs ↦ ?_
  simp only [Pi.add_apply, amplitudeSum_besselS_eq_zero (hΩ s (mem_filter.1 hs).2), add_zero]

open scoped Classical in
/-- At most `M ^ f #R̄₀` elements lie in a coset of the reduction `R̄₀` of the Bessel subgroup by an
integral scalar (`InScalarCoset`), as only the residues of the scalar at the chosen places
matter. -/
lemma card_inScalarCoset_le : #{s : S.ResidueGL | ∃ ζ : Ô E, S.InScalarCoset ζ s} ≤
    S.M ^ Core.numInfPlaces E * Nat.card (S.reducedImage besselS) := by
  -- An element `s = ζ t` is determined by the residues of `ζ` and by `t`.
  have h_scalar (s : {s : S.ResidueGL // ∃ ζ : Ô E, S.InScalarCoset ζ s}) :
      ∃ (ζ : Ô E) (t : S.ResidueGL), t ∈ S.reducedImage besselS ∧ ∀ (i : Fin 2)
        (w : S.chosenPlaces i),
        (s.val i w).val = New.reduceAt w.val ζ • (t i w).val := s.property
  choose ζ t ht h_eq using h_scalar
  let φ (s : {s : S.ResidueGL // ∃ ζ : Ô E, S.InScalarCoset ζ s}) :
      (∀ (i : Fin 2) (w : S.chosenPlaces i), ResField w.val) × S.reducedImage besselS :=
    (fun _ w ↦ New.reduceAt w.val (ζ s), ⟨t s, ht s⟩)
  have hφ : φ.Injective := fun s s' h ↦ by
    obtain ⟨h_res, h_t⟩ := Prod.ext_iff.1 h
    refine Subtype.ext (funext₂ fun i w ↦ Units.ext ?_)
    rw [h_eq, h_eq,
      show New.reduceAt w.val (ζ s) = New.reduceAt w.val (ζ s') from congrFun₂ h_res i w,
      show t s = t s' from congrArg Subtype.val h_t]
  rw [← Fintype.card_subtype, card_eq_nat_card]
  refine (Nat.card_le_card_of_injective φ hφ).trans_eq ?_
  simp only [Nat.card_prod, Nat.card_pi, card_resField_eq_levelPrime, prod_const, card_univ,
    S.card_chosenPlaces, Fin.prod_univ_two, mul_pow]

/-- Let the filling `S` be admissible (`IsAdmissible`), which includes the bound
`b^(11kf) 𝒟_id ≤ 𝒟_main`. Then `b^(5kf) 𝒟_id ≤ b^(-6ka) 𝒟_main` for any set `places` of chosen
places above the level prime `p₀` (`chosenPlaces 0`), where `a = #places`. -/
lemma pow_mul_identitySecondMoment_le_mul_mainSecondMoment [hS : S.IsAdmissible]
    (places : Finset (S.chosenPlaces 0)) :
    S.b ^ (5 * (𝔰.k * Core.numInfPlaces E)) * S.identitySecondMoment ≤
      (S.b ^ (6 * 𝔰.k))⁻¹ ^ #places * S.mainSecondMoment := by
  have hb : 1 ≤ S.b := S.one_le_b
  have h_id_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_places : #places ≤ Core.numInfPlaces E :=
    places.card_le_univ.trans_eq (S.card_chosenPlaces 0)
  rw [inv_pow, le_inv_mul_iff₀ (by positivity)]
  calc _ ≤ (S.b ^ (6 * 𝔰.k)) ^ Core.numInfPlaces E *
        (S.b ^ (5 * (𝔰.k * Core.numInfPlaces E)) * S.identitySecondMoment) := by
        gcongr
        exact one_le_pow₀ hb
    _ = S.b ^ (11 * (𝔰.k * Core.numInfPlaces E)) * S.identitySecondMoment := by ring
    _ ≤ S.mainSecondMoment := hS.mul_identitySecondMoment_le

/-- For each chosen place `w` above `p₀`, let `vectors w` be a nonzero vector of the span of the
frame modulo `w`. If its Boolean is `true`, it is taken modulo the conjugate of `w` instead. Let `s`
fix all of them. So `meetNorm s`, the product of the norms of the places at which `s` meets, is at
least `levelPrime 0 ^ numInfPlaces E`. -/
lemma levelPrime_pow_le_meetNorm_of_mem_fixer
    {vectors : ∀ w : S.chosenPlaces 0, S.FrameVector w} {s : S.ResidueGL}
    (hs : s ∈ S.fixer univ vectors) : S.levelPrime 0 ^ Core.numInfPlaces E ≤ S.meetNorm s := by
  classical
  let φ (w : S.chosenPlaces 0) : (Σ j : Fin 2, S.chosenPlaces j) × Bool := (⟨0, w⟩, (vectors w).1)
  have hφ : φ.Injective := fun w w' h ↦ by simpa [φ] using congrArg Prod.fst h
  have h_meet : ∀ p ∈ univ.image φ, S.MeetsAt s p :=
    forall_mem_image.2 fun w hw ↦ meetsAt_of_mem_vectorFixer (mem_fixer.1 hs w hw)
  refine le_trans ?_ (prod_le_meetNorm h_meet)
  rw [prod_image hφ.injOn]
  simp [φ, S.card_chosenPlaces]

open scoped Classical in
/-- For `s` in `ResidueGL`, write `‖P_s‖²` for the `secondMoment` at `s` of the amplitude sums
of all terms. If `‖P_s‖² ≤ 2 D_X` for all `s`, with `D_X = sourceDim`, then the sum
of `‖P_s‖²` over the cosets of the reduction `R̄₀` of the Bessel subgroup by integral scalars
(`InScalarCoset`) is at most `2 M ^ f 𝒟_id`. -/
lemma sum_secondMoment_inScalarCoset_le
    (h_le : ∀ s : S.ResidueGL, secondMoment (S.amplitudeSum .full Set.univ) {s} ≤ 2 * S.sourceDim) :
    ∑ s : S.ResidueGL with ∃ ζ : Ô E, S.InScalarCoset ζ s,
        secondMoment (S.amplitudeSum .full Set.univ) {s} ≤
      2 * S.M ^ Core.numInfPlaces E * S.identitySecondMoment :=
  calc _ ≤ #{s : S.ResidueGL | ∃ ζ : Ô E, S.InScalarCoset ζ s} • (2 * S.sourceDim : ℝ) :=
        sum_le_card_nsmul _ _ _ fun s _ ↦ h_le s
    _ ≤ _ := by
      grw [nsmul_eq_mul, card_inScalarCoset_le, identitySecondMoment]
      exact le_of_eq (by push_cast; ring)

/-- Let the filling `S` be admissible (`IsAdmissible`). Then `8 M ^ f 𝒟_id ≤ b^(-6kf) 𝒟_main`, as
`b^(11kf) 𝒟_id ≤ 𝒟_main`, `8 M ^ f ≤ b (b²³) ^ f` and `23 f + 1 ≤ 5 k f`. -/
lemma eight_mul_M_pow_mul_identitySecondMoment_le [S.IsAdmissible] :
    8 * S.M ^ Core.numInfPlaces E * S.identitySecondMoment ≤
      (S.b ^ (6 * 𝔰.k))⁻¹ ^ #(univ : Finset (S.chosenPlaces 0)) * S.mainSecondMoment := by
  have h_id_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_exp : 23 * Core.numInfPlaces E + 1 ≤ 5 * (𝔰.k * Core.numInfPlaces E) := by
    nlinarith only [S.thousand_mul_le_k, NeZero.one_le (n := Core.numInfPlaces E)]
  have hb : 1000 ≤ S.b := S.thousand_le_b
  calc _ ≤ S.b * (S.b ^ 23) ^ Core.numInfPlaces E * S.identitySecondMoment := by
        grw [M_le_b_pow, show (8 : ℝ) ≤ S.b by linarith]
    _ ≤ S.b ^ (5 * (𝔰.k * Core.numInfPlaces E)) * S.identitySecondMoment := by
      grw [← pow_mul, ← pow_succ', pow_le_pow_right₀ S.one_le_b h_exp]
    _ ≤ _ := pow_mul_identitySecondMoment_le_mul_mainSecondMoment univ

/-- The bound `(b^(2f) / p₀^f)^k 𝒟_main` on sums over links is at most an eighth of
`b^(-6kf) 𝒟_main`, as `b¹⁰ ≤ p₀` (`le_levelPrime`). -/
lemma div_levelPrime_pow_mul_mainSecondMoment_le :
    (S.b ^ (2 * Core.numInfPlaces E) / (S.levelPrime 0 ^ Core.numInfPlaces E : ℕ)) ^ 𝔰.k *
        S.mainSecondMoment ≤
      (S.b ^ (6 * 𝔰.k))⁻¹ ^ #(univ : Finset (S.chosenPlaces 0)) * S.mainSecondMoment / 8 := by
  have hb : 1 ≤ S.b := S.one_le_b
  have h_main_nonneg : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  have h_eight : 8 ≤ S.b ^ (2 * (𝔰.k * Core.numInfPlaces E)) := by
    grw [← S.forty_le_k_mul_numInfPlaces, ← two_le_b]
    norm_num
  calc _ ≤ (S.b ^ (2 * Core.numInfPlaces E) / (S.b ^ 10) ^ Core.numInfPlaces E) ^ 𝔰.k *
        S.mainSecondMoment := by grw [Nat.cast_pow, ← le_levelPrime]
    _ = (S.b ^ (2 * (𝔰.k * Core.numInfPlaces E)))⁻¹ *
        ((S.b ^ (6 * 𝔰.k))⁻¹ ^ #(univ : Finset (S.chosenPlaces 0)) * S.mainSecondMoment) := by
      rw [card_univ, S.card_chosenPlaces, inv_pow, div_pow]
      field
    _ ≤ _ := by grw [← div_eq_inv_mul, h_eight]

/-- Let `E` contain a primitive `5040`-th root of unity and let the filling `S` be admissible
(`IsAdmissible`). Let `D_X = sourceDim` be the number of pairs of a class and a coordinate, and
suppose `‖P_s‖² ≤ 2 D_X` for all `s`. At each of the `f` chosen places `w` above `p₀`, `vectors w`
is a `FrameVector`: a nonzero vector in the span of the frame `e₁, …, e_ϱ, z`, taken modulo `w` or
modulo its conjugate. Then the sum over the group `fixer` of the `s` that fix all these vectors
satisfies `∑ ‖P_s‖² ≤ b^(-6kf) 𝒟_main`. -/
lemma secondMoment_fixer_univ_le [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (vectors : ∀ w : S.chosenPlaces 0, S.FrameVector w)
    (h_le : ∀ s : S.ResidueGL, secondMoment (S.amplitudeSum .full Set.univ) {s} ≤ 2 * S.sourceDim) :
    secondMoment (S.amplitudeSum .full Set.univ) (S.fixer univ vectors) ≤
      (S.b ^ (6 * 𝔰.k))⁻¹ ^ #(univ : Finset (S.chosenPlaces 0)) * S.mainSecondMoment := by
  -- The scalar cosets are small. Off them the expansion of the squares applies, and its sums over
  -- links are small because every `s` in the fixer meets at `f` places above `p₀`.
  classical
  have hb : 1 ≤ S.b := S.one_le_b
  have h_id_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_main_nonneg : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  set target : ℝ := (S.b ^ (6 * 𝔰.k))⁻¹ ^ #(univ : Finset (S.chosenPlaces 0)) * S.mainSecondMoment
  have h_id_le_target : 8 * S.M ^ Core.numInfPlaces E * S.identitySecondMoment ≤ target :=
    eight_mul_M_pow_mul_identitySecondMoment_le
  let β (s : S.ResidueGL) : ℝ := secondMoment (S.amplitudeSum .full Set.univ) {s}
  let Ω : Set S.ResidueGL := {s | s ∈ S.fixer univ vectors ∧ ¬∃ ζ : Ô E, S.InScalarCoset ζ s}
  -- The scalar cosets have at most `M ^ f #R̄₀` elements, each with `β s ≤ 2 D_X`.
  have h_cosets : ∑ s : S.ResidueGL with ∃ ζ : Ô E, S.InScalarCoset ζ s, β s ≤ target / 2 :=
    (sum_secondMoment_inScalarCoset_le h_le).trans (by linarith [show 0 ≤ target by positivity])
  -- On `Ω` the sums over links give at most `linkBound ≤ b^(-8kf) 𝒟_main`, as `b¹⁰ ≤ p₀`.
  let linkBound : ℝ := (S.b ^ (2 * Core.numInfPlaces E) /
    (S.levelPrime 0 ^ Core.numInfPlaces E : ℕ)) ^ 𝔰.k * S.mainSecondMoment
  have h_links : linkBound ≤ target / 8 := div_levelPrime_pow_mul_mainSecondMoment_le
  have h_id : (S.b ^ 15)⁻¹ ^ 2 * S.identitySecondMoment ≤ target / 8 := by
    have h_inv : (S.b ^ 15)⁻¹ ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hb))
    grw [h_inv, ← h_id_le_target, ← one_le_pow₀ (Nat.one_le_cast.2 (one_le_two.trans two_le_M))]
    linarith
  have h_rest : ∑ s : S.ResidueGL with s ∈ Ω, β s ≤ target / 2 := by
    have h_avoid : S.AvoidsScalarCosets Ω := fun ζ h_int _ _ s hs h ↦ hs.2 ⟨⟨ζ, h_int⟩, h⟩
    have h_off : ∀ s ∈ Ω, s ∉ S.reducedImage besselS :=
      fun s hs h ↦ hs.2 ⟨1, inScalarCoset_one h⟩
    calc _ = secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) Ω := by
          rw [← secondMoment_eq_sum_secondMoment_singleton,
            secondMoment_univ_eq_secondMoment_compl_besselS h_off]
      _ ≤ (√linkBound + (S.b ^ 15)⁻¹ * √S.identitySecondMoment) ^ 2 := by
        rw [← Real.sqrt_le_left (by positivity)]
        exact sqrt_secondMoment_compl_besselS_le h_avoid (by positivity)
          (linkSecondMoment_le_of_le_meetNorm
          (pow_ne_zero _ (S.levelPrime_prime_and_ne 0).1.ne_zero)
          fun s hs ↦ levelPrime_pow_le_meetNorm_of_mem_fixer hs.1)
      _ ≤ 2 * (linkBound + (S.b ^ 15)⁻¹ ^ 2 * S.identitySecondMoment) := by
        grw [add_sq_le, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt h_id_nonneg]
      _ ≤ target / 2 := by linarith [h_links, h_id]
  calc _ = ∑ s : S.ResidueGL with s ∈ S.fixer univ vectors ∧ ∃ ζ : Ô E, S.InScalarCoset ζ s, β s +
        ∑ s : S.ResidueGL with s ∈ Ω, β s := by
        rw [secondMoment_eq_sum_secondMoment_singleton,
          ← sum_filter_add_sum_filter_not _ fun s : S.ResidueGL ↦ ∃ ζ : Ô E, S.InScalarCoset ζ s,
          filter_filter, filter_filter]
        congr!
    _ ≤ ∑ s : S.ResidueGL with ∃ ζ : Ô E, S.InScalarCoset ζ s, β s + ∑ s : S.ResidueGL with s ∈ Ω,
      β s := by
      gcongr
      · exact fun s _ _ ↦ secondMoment_nonneg
      · exact And.right
    _ ≤ target := by linarith [h_cosets, h_rest]

/-- Let the filling `S` be admissible (`IsAdmissible`) and assume Weil data on `E`. Over the open
`s` that fix the given nonzero vectors of the span of the frame at a set of `a` chosen places above
`p₀` (`fixer`) we have `∑ ‖P_s‖² ≤ (1 + 4 b⁻⁴) b^(-6ka) 𝒟_main`. The element `s` is open if at some
chosen place above `p₀` no leading minor of size less than `n = ϱ + 1` of `frameGram`, the matrix of
the products of the frame with its image under `s`, vanishes. -/
lemma secondMoment_fixer_isOpenElement_le [S.IsAdmissible] [WeilData E]
    (places : Finset (S.chosenPlaces 0))
    (vectors : ∀ w : S.chosenPlaces 0, S.FrameVector w) :
    secondMoment (S.amplitudeSum .full Set.univ)
        {s : S.ResidueGL | s ∈ S.fixer places vectors ∧ S.IsOpenElement s} ≤
      (1 + 4 / S.b ^ 4) * ((S.b ^ (6 * 𝔰.k))⁻¹ ^ #places * S.mainSecondMoment) := by
  -- No open element lies in a scalar coset, so the expansion and the main term apply.
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have hb₁ : 1 ≤ S.b := S.one_le_b
  set target : ℝ := (S.b ^ (6 * 𝔰.k))⁻¹ ^ #places * S.mainSecondMoment with h_target_def
  have h_id : S.identitySecondMoment ≤ target := (le_mul_of_one_le_left identitySecondMoment_nonneg
    (one_le_pow₀ hb₁)).trans (pow_mul_identitySecondMoment_le_mul_mainSecondMoment places)
  have h_target_nonneg : 0 ≤ target := identitySecondMoment_nonneg.trans h_id
  set Ω : Set S.ResidueGL := {s | s ∈ S.fixer places vectors ∧ S.IsOpenElement s}
  have h_avoid : S.AvoidsScalarCosets Ω :=
    fun ζ h_int _ _ s hs h_coset ↦ h_coset.not_isOpenElement hs.2
  have h_off : ∀ s ∈ Ω, s ∉ S.reducedImage besselS :=
    fun s hs h ↦ (inScalarCoset_one h).not_isOpenElement hs.2
  -- With `x = b⁻⁴` we have `(1 + x)^(1/2) ≤ 1 + x / 2` and `b⁻¹⁵ ≤ x / 2`.
  have hx₀ : 0 ≤ (S.b ^ 4)⁻¹ := by positivity
  have hx : (S.b ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hb₁)
  have h_small : (S.b ^ 15)⁻¹ ≤ (S.b ^ 4)⁻¹ / 2 := by
    field_simp
    linarith [le_self_pow₀ hb₁ (by norm_num : 11 ≠ 0)]
  have h_bound : √(secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) Ω) ≤
      (1 + (S.b ^ 4)⁻¹) * √target :=
    calc _ ≤ √((1 + (S.b ^ 4)⁻¹) * target) + (S.b ^ 15)⁻¹ * √S.identitySecondMoment := by
          refine sqrt_secondMoment_compl_besselS_le h_avoid (by positivity) ?_
          rw [h_target_def, ← mul_assoc]
          exact linkSecondMoment_isOpenElement_le places vectors
      _ ≤ (1 + (S.b ^ 4)⁻¹ / 2) * √target + (S.b ^ 4)⁻¹ / 2 * √target := by
        grw [Real.sqrt_mul (by positivity), Real.sqrt_one_add_le (by linarith), h_small, h_id]
      _ = (1 + (S.b ^ 4)⁻¹) * √target := by ring
  calc _ ≤ (1 + (S.b ^ 4)⁻¹) ^ 2 * target := by
        grw [secondMoment_univ_eq_secondMoment_compl_besselS h_off, (Real.sqrt_le_iff.1 h_bound).2,
          mul_pow, Real.sq_sqrt h_target_nonneg]
    _ ≤ (1 + 4 / S.b ^ 4) * target := by
      gcongr
      rw [div_eq_mul_inv]
      nlinarith

/-- For `l < n = ϱ + 1` we have `p₀ ^ (l + r / 2) ≤ b ^ (6 k)`. Here `p₀ = levelPrime 0`,
`b = S.b`, `k = |κ|`, and `r` is the rank of the space, the number of indices in `𝔰.BesselIndex`. -/
lemma levelPrime_pow_mul_sqrt_le (l : Fin 𝔰.n) :
    (S.levelPrime 0 : ℝ) ^ l.val * √(S.levelPrime 0 ^ card 𝔰.BesselIndex) ≤ S.b ^ (6 * 𝔰.k) := by
  -- Square, and use `p₀ ≤ b¹¹`, `r = k + 2 n - 1` and `2000 n ≤ k`.
  have hb : 1 ≤ S.b := S.one_le_b
  have h_exp : 11 * (l.val * 2 + card 𝔰.BesselIndex) ≤ 6 * 𝔰.k * 2 := by
    have h_rank : card 𝔰.BesselIndex = 2 * 𝔰.ϱ + 𝔰.k + 1 := by simp +arith
    linarith [S.thousand_mul_le_k, (l.isLt : l.val < 𝔰.ϱ + 1)]
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  calc _ = (S.levelPrime 0 : ℝ) ^ (l.val * 2 + card 𝔰.BesselIndex) := by
        rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, ← pow_add]
    _ ≤ S.b ^ (11 * (l.val * 2 + card 𝔰.BesselIndex)) := by grw [S.levelPrime_le 0, ← pow_mul]
    _ ≤ (S.b ^ (6 * 𝔰.k)) ^ 2 := by grw [h_exp, ← pow_mul]

open scoped Classical in
/-- Let the filling `S` be admissible (`IsAdmissible`), with large parameter `b = S.b` and with
`k = 𝔰.k` the rank of `X₀`. Let `β ≥ 0` on `ResidueGL` have positive type. Let `Γ` be a subgroup and
`w` a chosen place above `p₀`. The frame consists of the `ϱ + 1` basis vectors `e₁, …, e_ϱ, z`, and
a `FrameVector` at `w` is a nonzero vector of their span, taken modulo `w` or modulo its conjugate.
Suppose that the stabilizer in `Γ` of any such vector carries at most a proportion `b^(-6k)` of the
sum of `β` over `Γ`. Let `l < 𝔰.n`, and let `δ_l` be the leading minor of size `l` of the
`frameGram` of the component `s 0 w` over the residue field at `w`. Then the `s` in `Γ` with
`δ_l = 0` carry at most a proportion `3 / b¹⁰`. -/
lemma sum_leadingMinor_eq_zero_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {β : S.ResidueGL → ℝ} (h_nonneg : ∀ s : S.ResidueGL, 0 ≤ β s)
      {u : S.ResidueGL → V}
    (h_posType : ∀ a b : S.ResidueGL, ⟪u a, u b⟫_ℂ = β (a⁻¹ * b)) {Γ : Subgroup S.ResidueGL}
    {w : S.chosenPlaces 0}
    (h_stab : ∀ d : S.FrameVector w, ∑ s : Γ with s.val ∈ S.vectorFixer w d, β s.val ≤
      (∑ s : Γ, β s.val) / S.b ^ (6 * 𝔰.k)) (l : Fin 𝔰.n) :
    ∑ s : Γ with leadingMinor ((S.latticeMiddle (ResField (w : FinPlace E))).frameGram
        (s.val 0 w).val) l.castSucc = 0, β s.val ≤
      3 * (∑ s : Γ, β s.val) / S.b ^ 10 := by
  -- `δ_l` is the determinant of the pairings of the first `l` frame vectors with their images.
  have hb : 0 < S.b := b_pos
  set total : ℝ := ∑ s : Γ, β s.val
  set stabFactor : ℝ := S.b ^ (6 * 𝔰.k)
  have h_total_nonneg : 0 ≤ total := sum_nonneg fun s _ ↦ h_nonneg s
  -- The group `Γ` acts on the lattice modulo `w`; the residue field has `p₀` elements.
  let π : Γ →* GL 𝔰.BesselIndex (ResField w.val) := MonoidHom.mk' (fun s ↦ s.val 0 w) (by simp)
  have h_card : card (ResField w.val) = S.levelPrime 0 :=
    card_eq_nat_card.trans (card_resField_eq_levelPrime S 0 w)
  -- The columns of `e` are the first `l` frame vectors, those of `J * e` their linear forms.
  let J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (ResField w.val) :=
    (S.latticeMiddle (ResField w.val)).splitGram
  let e : Matrix 𝔰.BesselIndex (Fin l.castSucc) (ResField w.val) :=
    frameImage 1 * inclMatrix (ResField w.val) (Fin.castLE l.castSucc.is_le)
  have h_det (s : Γ) : ((J * e)ᵀ * (π s).val * e).det =
      leadingMinor ((S.latticeMiddle (ResField w.val)).frameGram (s.val 0 w).val) l.castSucc := by
    let ι : Fin l.castSucc → 𝔰.BesselIndex := 𝔰.besselFrame ∘ Fin.castLE l.castSucc.is_le
    rw [show e = inclMatrix (ResField w.val) ι from mul_inclMatrix _ _, mul_inclMatrix,
      mul_inclMatrix, transpose_submatrix, transpose_splitGram]
    rfl
  -- The stabilizer of a vector, or of a form, fixes a vector modulo `w`, or modulo its conjugate.
  have h_le_of_fixes (d : S.FrameVector w) (p : Γ → Prop) [DecidablePred p]
      (hp : ∀ s : Γ, p s → s.val ∈ S.vectorFixer w d) :
      ∑ s : Γ with p s, β s.val ≤ total / stabFactor :=
    (sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ fun s _ h ↦ hp s h)
      fun s _ _ ↦ h_nonneg s).trans (h_stab d)
  have h_coord (v : Fin l.castSucc → ResField w.val) (hv : v ≠ 0) :
      inclMatrix (ResField w.val) (Fin.castLE l.castSucc.is_le) *ᵥ v ≠ 0 :=
    (map_ne_zero_iff _ (inclMatrix_mulVecLin_injective (Fin.castLEEmb l.castSucc.is_le) _)).2 hv
  have h_fix_vector (v : Fin l.castSucc → ResField w.val) (hv : v ≠ 0) :
      ∑ s with e *ᵥ v = π s • e *ᵥ v, β s.val ≤ total / stabFactor := by
    refine h_le_of_fixes ⟨false, _, h_coord v hv⟩ _ fun s hs ↦ ?_
    rw [mem_vectorFixer_false, mulVec_mulVec v]
    exact hs.symm
  have h_fix_form (v : Fin l.castSucc → ResField w.val) (hv : v ≠ 0) :
      ∑ s with (J * e) *ᵥ v = invTransposeGL (π s) • (J * e) *ᵥ v, β s.1 ≤ total / stabFactor := by
    refine h_le_of_fixes ⟨true, _, h_coord v hv⟩ _ fun s hs ↦ ?_
    rw [mem_vectorFixer_true, mulVec_mulVec v, mulVec_mulVec v]
    exact hs.symm
  rw [le_div_iff₀' (by positivity)]
  calc _ ≤ card (ResField w.val) * ∑ s with ((J * e)ᵀ * (π s).val * e).det = 0, β s.val := by
        simp only [h_det, h_card]
        exact mul_le_mul_of_nonneg_right (S.le_levelPrime 0) (sum_nonneg fun s _ ↦ h_nonneg s)
    _ ≤ 2 * total + card (ResField w.val) ^ card (Fin l.castSucc) *
        √(card (ResField w.val) ^ card 𝔰.BesselIndex) * (total / stabFactor) :=
      card_mul_sum_det_eq_zero_le π e (J * e) (fun s ↦ h_nonneg s) (fun a b ↦ h_posType a b) _
        (by positivity) h_fix_vector h_fix_form
    _ ≤ 2 * total + stabFactor * (total / stabFactor) := by
      grw [h_card, Fintype.card_fin, Fin.val_castSucc, levelPrime_pow_mul_sqrt_le]
    _ = 3 * total := by field

open scoped Classical in
/-- Let the filling `S` be admissible (`IsAdmissible`), with `k = 𝔰.k` the rank of `X₀` and `S.b`
its large parameter. Let `β ≥ 0` on `ResidueGL` have positive type: `β (a⁻¹ * b) = ⟪u a, u b⟫` for
all `a`, `b`, for a map `u` into an inner product space. Let `Γ` be a subgroup of `ResidueGL` and
`w` a chosen place above `p₀`. Suppose that for every nonzero vector of the span of the frame,
modulo `w` or its conjugate, the elements of `Γ` that fix it (`vectorFixer`) carry at most a
proportion `S.b^(-6k)` of the sum of `β` over `Γ`. Then the elements of `Γ` that are not open carry
at most a proportion `S.b⁻⁴` of that sum. -/
lemma sum_not_isOpenElement_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {β : S.ResidueGL → ℝ} (h_nonneg : ∀ s : S.ResidueGL, 0 ≤ β s)
      {u : S.ResidueGL → V}
    (h_posType : ∀ a b : S.ResidueGL, ⟪u a, u b⟫_ℂ = β (a⁻¹ * b)) {Γ : Subgroup S.ResidueGL}
    {w : S.chosenPlaces 0}
    (h_stab : ∀ d : S.FrameVector w, ∑ s : Γ with s.val ∈ S.vectorFixer w d, β s.val ≤
      (∑ s : Γ, β s.val) / S.b ^ (6 * 𝔰.k)) :
    ∑ s : Γ with ¬S.IsOpenElement s.val, β s.val ≤ (S.b ^ 4)⁻¹ * ∑ s : Γ, β s.val := by
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have h_total_nonneg : 0 ≤ ∑ s : Γ, β s.val := sum_nonneg fun s _ ↦ h_nonneg s
  let δ (l : Fin 𝔰.n) (s : S.ResidueGL) : ResField w.val :=
    leadingMinor ((S.latticeMiddle (ResField w.val)).frameGram (s 0 w).val) l.castSucc
  calc
    _ ≤ ∑ l : Fin 𝔰.n, ∑ s : Γ with δ l s.val = 0, β s.val := by
      simp only [sum_filter]
      rw [sum_comm]
      refine sum_le_sum fun s _ ↦ ?_
      split_ifs with hs
      · exact sum_nonneg fun l _ ↦ ite_nonneg (h_nonneg s) le_rfl
      · obtain ⟨l, hl⟩ : ∃ l : Fin 𝔰.n, δ l s.val = 0 := by_contra fun h ↦ hs ⟨w, not_exists.1 h⟩
        refine le_trans ?_ (single_le_sum (fun l _ ↦ ite_nonneg (h_nonneg s) le_rfl) (mem_univ l))
        rw [ite_eq_left hl]
    _ ≤ card (Fin 𝔰.n) • (3 * (∑ s : Γ, β s.val) / S.b ^ 10) :=
      sum_le_card_nsmul _ _ _ fun l _ ↦ sum_leadingMinor_eq_zero_le h_nonneg h_posType h_stab l
    _ ≤ (S.b ^ 4)⁻¹ * ∑ s : Γ, β s.val := by
      -- `3 n ≤ 3 b ≤ b⁶`
      have h_three : 3 ≤ S.b ^ 5 := le_trans (by linarith) (le_self_pow₀ S.one_le_b (by norm_num))
      grw [Fintype.card_fin, nsmul_eq_mul, S.succ_le_b, h_three]
      exact le_of_eq (by field)

/-- If `M ≤ (1 + 4 x) C + x M` with `0 ≤ x ≤ 1/10` and `C ≥ 0`, then `M ≤ (1 + 9 x) C`. -/
lemma le_one_add_nine_mul_of_le_add {x C M : ℝ} (hx₀ : 0 ≤ x) (hx : x ≤ 1 / 10) (hC : 0 ≤ C)
    (h : M ≤ (1 + 4 * x) * C + x * M) : M ≤ (1 + 9 * x) * C := by
  -- `(1 - x) (1 + 9 x) - (1 + 4 x) = x (4 - 9 x)`
  have h_gain : 0 ≤ x * (4 - 9 * x) * C := mul_nonneg (mul_nonneg hx₀ (by linarith)) hC
  have h_mul : (1 - x) * M ≤ (1 - x) * ((1 + 9 * x) * C) := by linarith
  exact le_of_mul_le_mul_left h_mul (by linarith)

/-- Let the filling `S` over the CM field `E` be admissible (`IsAdmissible`) and assume Weil data on
`E`, which include a primitive `5040`-th root of unity. If `s ↦ ‖P_s‖²` has positive type, that is,
`‖P_(x⁻¹ y)‖² = ⟪u x, u y⟫` for vectors `u x` of an inner product space, and `‖P_1‖² ≤ 2 D_X`, then
`∑ ‖P_s‖² ≤ (1 + 9 b⁻⁴) 𝒟_main`. -/
theorem sum_secondMoment_le [S.IsAdmissible] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [WeilData E] (u : S.ResidueGL → V)
    (h_posType : ∀ a b : S.ResidueGL,
      ⟪u a, u b⟫_ℂ = (secondMoment (S.amplitudeSum .full Set.univ) {a⁻¹ * b} :
      ℝ))
    (h_one : secondMoment (S.amplitudeSum .full Set.univ) {1} ≤ 2 * S.sourceDim) :
    ∑ s : S.ResidueGL, secondMoment (S.amplitudeSum .full Set.univ) {s} ≤
      (1 + 9 / S.b ^ 4) * S.mainSecondMoment := by
  classical
  -- Choose places and vectors maximizing `stabFactor ^ #places` times the sum over the fixer.
  -- Comparison with the empty set of places shows that it suffices to bound the sum for this
  -- choice.
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have h_main_nonneg : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  let β (s : S.ResidueGL) : ℝ := secondMoment (S.amplitudeSum .full Set.univ) {s}
  have h_nonneg (s : S.ResidueGL) : 0 ≤ β s := secondMoment_nonneg
  set stabFactor : ℝ := S.b ^ (6 * 𝔰.k)
  let fixerMass (places : Finset (S.chosenPlaces 0))
      (vectors : ∀ w : S.chosenPlaces 0, S.FrameVector w) : ℝ :=
    ∑ s : S.ResidueGL with s ∈ S.fixer places vectors, β s
  have : Nonempty (∀ w : S.chosenPlaces 0, S.FrameVector w) := ⟨fun _ ↦ (true, ⟨1, one_ne_zero⟩)⟩
  obtain ⟨places, vectors, h_max_weighted⟩ : ∃ places vectors, ∀ places' vectors',
      stabFactor ^ #places' * fixerMass places' vectors' ≤
        stabFactor ^ #places * fixerMass places vectors := by
    simpa only [Prod.exists, Prod.forall, Function.uncurry_apply_pair] using Finite.exists_max
      (Function.uncurry fun places vectors ↦ stabFactor ^ #places * fixerMass places vectors)
  suffices h_fixer_bound : fixerMass places vectors ≤
      (1 + 9 / S.b ^ 4) * (stabFactor⁻¹ ^ #places * S.mainSecondMoment) by
    calc _ = stabFactor ^ #(∅ : Finset (S.chosenPlaces 0)) * fixerMass ∅ vectors := by
          simp [fixerMass, β, mem_fixer]
      _ ≤ stabFactor ^ #places * fixerMass places vectors := h_max_weighted ∅ vectors
      _ ≤ stabFactor ^ #places *
          ((1 + 9 / S.b ^ 4) * (stabFactor⁻¹ ^ #places * S.mainSecondMoment)) := by gcongr
      _ = (1 + 9 / S.b ^ 4) * S.mainSecondMoment := by
        rw [inv_pow]
        field
  -- If every place is fixed, positive type bounds each term by its value at the identity.
  obtain rfl | h_places := eq_or_ne places univ
  · calc _ = secondMoment (S.amplitudeSum .full Set.univ) (S.fixer univ vectors) :=
          (secondMoment_eq_sum_secondMoment_singleton _
            (S.fixer univ vectors : Set S.ResidueGL)).symm
      _ ≤ stabFactor⁻¹ ^ #univ * S.mainSecondMoment := secondMoment_fixer_univ_le vectors fun s ↦
        (le_apply_one_of_inner_eq (β := β) h_posType s).trans h_one
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (le_add_of_nonneg_right (by positivity))
  -- Take `w ∉ places`. Stabilizers of vectors at `w` are fixers for `insert w places`, so they are
  -- small by maximality.
  obtain ⟨w, hw⟩ : ∃ w : S.chosenPlaces 0, w ∉ places :=
    not_forall.1 (mt eq_univ_iff_forall.2 h_places)
  have fixerMass_eq : fixerMass places vectors = ∑ s : S.fixer places vectors, β s.val :=
    sum_subtype _ (by simp) β
  have h_vector_fixer (d : S.FrameVector w) :
      ∑ s : S.fixer places vectors with s.val ∈ S.vectorFixer w d, β s.val ≤
        fixerMass places vectors / stabFactor := by
    have h_le := h_max_weighted (insert w places) (Function.update vectors w d)
    rw [card_insert_of_notMem hw, pow_succ, mul_assoc, mul_le_mul_iff_right₀ (by positivity),
      ← le_div_iff₀' (by positivity)] at h_le
    rw [sum_subgroup_filter _ (· ∈ S.vectorFixer w d)]
    simpa only [fixerMass, mem_fixer_insert hw] using h_le
  have h_nonopen : ∑ s : S.fixer places vectors with ¬S.IsOpenElement s.val, β s.val ≤
      (S.b ^ 4)⁻¹ * fixerMass places vectors := by
    rw [fixerMass_eq] at h_vector_fixer ⊢
    exact sum_not_isOpenElement_le h_nonneg h_posType h_vector_fixer
  have h_open : ∑ s : S.fixer places vectors with S.IsOpenElement s.val, β s.val ≤
      (1 + 4 / S.b ^ 4) * (stabFactor⁻¹ ^ #places * S.mainSecondMoment) := by
    refine le_trans (le_of_eq ?_) (secondMoment_fixer_isOpenElement_le places vectors)
    rw [sum_subgroup_filter, secondMoment_eq_sum_secondMoment_singleton]
    congr!
  -- Absorb the non-open contribution, at most b⁻⁴ of the fixer mass itself.
  have h_open_nonopen : fixerMass places vectors ≤
      (1 + 4 / S.b ^ 4) * (stabFactor⁻¹ ^ #places * S.mainSecondMoment) +
        (S.b ^ 4)⁻¹ * fixerMass places vectors := by
    grw [← h_open, ← h_nonopen, sum_filter_add_sum_filter_not, fixerMass_eq]
  simp only [div_eq_mul_inv _ (S.b ^ 4)] at h_open_nonopen ⊢
  exact le_one_add_nine_mul_of_le_add (by positivity) (by grw [← hb]; norm_num) (by positivity)
    h_open_nonopen

end Filling

end New
end
end

/-!
# The second moments of the operators `P* s P`, and good forms

Let `S` be admissible filling data, with size parameter `b = S.b`. The finite group
`Ḡ = S.ResidueGL` has one factor for each of the two level primes `p_i = S.levelPrime i`, and
`R̄₀ = S.reducedImage besselS` is the image of the Bessel subgroup in it. The source is the space of
dimension `D_X = S.sourceDim` with coordinates indexed by the classes and the coordinates of the
Bessel function. For a map `P` from the source to a representation `ρ` of `Ḡ` put `P_s = P* ρ(s) P`;
all norms of operators are Hilbert–Schmidt norms. The file proves the two moment bounds for the
`P_s`, and deduces that `e₀ P` is almost an isometry for the projection `e₀` onto the target forms.
We write `𝒟_id = S.identitySecondMoment` and `𝒟_main = S.mainSecondMoment`.

## Main definitions and results

* `New.Filling.HasAmplitudeBlocks`: the blocks of `P_s` are the conjugates of the amplitude sums,
  divided by the covolume.
* `New.Filling.besselTranslate`: the unitary representation `r_ψ` of `R̄₀` on the source, extended
  by `0`.
* `New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sub_besselTranslate_sq_le`: over `R̄₀`
  times one factor of `Ḡ`, `∑ ‖P_s - r_ψ(s)‖² ≤ b⁻¹² 𝒟_id`.
* `New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sub_one_sq_le`: `‖P* P - 1‖² ≤ b⁻¹² D_X`.
* `New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le`: `∑ ‖P_s‖² ≤ (1 + 9 b⁻⁴) 𝒟_main`
  over `Ḡ`.
* `New.Filling.HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp`: `e₀ P` is almost an isometry in
  mean square, with the error `5 b⁻⁴`.

Notions from other files:
* `New.Filling.reduction`: the homomorphism from the stabilizer `K = S.latticeStabilizer` of the
  lattice to `Ḡ` that reduces matrix entries modulo the chosen places above `p₀` and `p₁`.
* `New.Filling.termsOver`: the terms over a block `(c, s, c')`, the rational `γ` such that
  `h_c⁻¹ γ h_c'` lies in `K` and has reduction `s`.
* `New.Filling.amplitudeSum`: the sum of the amplitudes of the terms of a set over a block.
* `New.Filling.identitySecondMoment`, `New.Filling.mainSecondMoment`: the numbers `#R̄₀ · D_X` and
  `D_X² / (deg · mass)`, with `deg = S.besselDegree` and the mass `New.mass` of the genus of the
  standard lattice of rank `r`.

## Relation to the literature

For the normalised Poincaré map `P`, the mean over level translates `s` of `‖P* s P‖²` is at most
nearly `D_X² / D₀`, with `D₀` the expected dimension of the target, and bad types carry little of
`P`. In rank one, Poisson summation on a product of two Kloosterman sides with a sharp diagonal term
is known in the literature. Related work: Herman, Beyond endoscopy for the Rankin–Selberg
L-function, 2011; Iwaniec–Li, The orthogonality of Hecke eigenvalues, 2007;
Michel–Ramakrishnan–Yang, Bessel periods on U(2,1)×U(1,1), 2023.

See `New.Spanning.SecondMoment.SpanningTheorem` and `New.Spanning.RemainingTerms.Sum` for related
work.
-/

@[expose] public section

namespace New.Filling

/-!
## The operators `P_s` and `r_ψ(s)`, and the second moments

In statements about `P`, `ρ` is a representation of `Ḡ`, unitary where stated, on a space of finite
dimension.
-/

section Moments

open Matrix Complex Module InnerProductSpace EuclideanSpace Finset Fintype

attribute [local instance low] Fintype.ofFinite

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} [ok : S.IsAdmissible]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- In a unitary representation `ρ` of a finite group, a central idempotent `z` of the group algebra
(an idempotent whose coefficients form a class function) acts as an orthogonal projection. -/
lemma _root_.New.IsCentralProj.isSymmetricProjection {H : Type} [Group H] [Fintype H]
    {ρ : Representation ℂ H V} (hρ : ∀ (s : H) (x y : V), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ)
    {z : MonoidAlgebra ℂ H} (hz : IsCentralProj z) :
    (ρ.asAlgebraHom z).IsSymmetricProjection :=
  have h_idem : IsIdempotentElem z := hz.1
  ⟨h_idem.map ρ.asAlgebraHom, hz.self_adjoint ρ 1 (innerₛₗ ℂ) hρ⟩

open scoped Classical in
variable (S) in
/-- Let `Ḡ = S.ResidueGL` be the product of the general linear groups over the residue fields at the
chosen places of `S`. The source is the Euclidean space with coordinates `(c, i)`, where `c` is a
class (a double coset of the definite unitary group `U(X₀)` for the level) and `i` is a coordinate
of the Bessel function `W` at the infinite places. For a representation `ρ` of `Ḡ` on `V` and a
linear map `P` from the source to `V`, this says that the block `(c, c')` of `P_s = P* ρ(s) P` is
the complex conjugate of `A(c, s, c') / ν`. Here `ν = unipotentCovolume`, and
`A(c, s, c') = amplitudeSum .full .univ c s c'` is the sum of the amplitudes
`∫ β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^* dy` over all terms, the rational `γ` such that
`h_c⁻¹ γ h_c'` is integral with reduction `s`; `h_c` represents the class `c` and
`β_c = classCutoff c`. This holds for the Poincaré map after scaling. -/
def HasAmplitudeBlocks (ρ : Representation ℂ S.ResidueGL V)
    (P : EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ] V) : Prop :=
  ∀ (s : S.ResidueGL) (x y : S.Classes × S.BesselCoord), ⟪ρ s (P (.single y 1)),
    P (.single x 1)⟫_ℂ =
    S.amplitudeSum .full .univ x.1 s y.1 (x.2, y.2) / S.unipotentCovolume

variable [FiniteDimensional ℂ V] {ρ : Representation ℂ S.ResidueGL V}
  {P : EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ] V}

open scoped Classical in
omit ok [FiniteDimensional ℂ V] in
/-- Let `S` be filling data for a unitary group over the CM field `E`, and `Ḡ = S.ResidueGL` the
product of the general linear groups over the residue fields at the chosen places. Let `ρ` be a
representation of `Ḡ` on `V` and `P` a linear map to `V` from the Euclidean space with basis `e_x`,
where `x` is a pair of a class (a double coset of the definite unitary group `U(X₀)` for the level)
and a coordinate of the Bessel function `W` at the infinite places. Suppose that
`⟪ρ(s) P e_y, P e_x⟫` is `c > 0` times the entry of `amplitudeSum .full .univ`, the sum over all
rational terms of the amplitude integrals of the uncut function `W`. Then `(c ν) ^ (-1/2) P`
satisfies `HasAmplitudeBlocks`, the same identity with `ν⁻¹` in place of `c`, where
`ν = S.unipotentCovolume > 0`. -/
lemma hasAmplitudeBlocks_smul_of_inner_eq {c : ℝ} (hc : 0 < c)
    (hP : ∀ (s : S.ResidueGL) (x y : S.Classes × S.BesselCoord),
      ⟪ρ s (P (.single y 1)), P (.single x 1)⟫_ℂ =
        ofReal c * S.amplitudeSum .full .univ x.1 s y.1 (x.2, y.2)) :
    S.HasAmplitudeBlocks ρ (ofReal √(c * S.unipotentCovolume)⁻¹ • P) := by
  intro s x y
  have hν : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, inner_smul_left, inner_smul_right,
    hP, conj_ofReal, ← mul_assoc, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  field [ofReal_ne_zero.2 hc.ne']

open scoped Classical in
omit ok in
private lemma hilbertSchmidtNorm_sq_of_entries
    {L : Module.End ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord))}
    {A : S.Classes → S.ResidueGL → S.Classes → EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord)}
    {s : S.ResidueGL} (h : ∀ x y : S.Classes × S.BesselCoord,
      ⟪L (.single y 1), .single x 1⟫_ℂ = A x.1 s y.1 (x.2, y.2) / S.unipotentCovolume) :
    hilbertSchmidtNorm L ^ 2 = secondMoment (S := S) A {s} := by
  rw [hilbertSchmidtNorm_sq_eq_sum_entries (basisFun _ ℂ) (basisFun _ ℂ)]
  simp only [basisFun_apply, h]
  simp [secondMoment, sum_filter, norm_sq_eq, sum_prod_type, sum_div, div_pow,
    sum_comm (α := S.Classes) (γ := S.BesselCoord)]

omit ok in
/-- Let `S` be filling data (`Filling`) for a unitary group `G` over the CM field `E`, and let
`Ḡ = S.ResidueGL` be the product of the general linear groups over the residue fields at the chosen
places above the two level primes `p₀`, `p₁`. The source is the Euclidean space with coordinates
`(c, i)`, where `c` is a class (a double coset of the definite unitary group `U(X₀)` for the level)
and `i` is a coordinate of the Bessel function `W` at the infinite places. Let `ρ` be a
representation of `Ḡ` on `V` and `P` a linear map from the source to `V`. Suppose
`HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the conjugate of
`A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum, over the
rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral of
`W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Then the squared
Hilbert–Schmidt norm of `P_s` is `∑ ‖A(c, s, c')‖² / ν²` over pairs of classes, the second moment at
`s` of all terms (`.univ`) for the uncut function `W` (`.full`). -/
lemma HasAmplitudeBlocks.hilbertSchmidtNorm_sq_eq_secondMoment (hP : S.HasAmplitudeBlocks ρ P)
    (s : S.ResidueGL) :
    hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P) ^ 2 =
      secondMoment (S.amplitudeSum .full .univ) {s} := by
  apply hilbertSchmidtNorm_sq_of_entries
  intro x y
  simpa [LinearMap.adjoint_inner_left] using hP s x y

open scoped Classical in
variable (S) in
/-- The operator `r_ψ(s)` on the source: its blocks are the complex conjugates of the sums of
amplitudes (`amplitudeSum`) of the terms in the Bessel subgroup, divided by `unipotentCovolume`. For
`s` in the image `R̄₀` of the Bessel subgroup it is the translation by `s`, twisted by the
character: each class `c` has a term of the Bessel subgroup over some block `(c, s, c')`
(`exists_besselS_mem_termsOver`), its matrix is given by `besselFn_mul_of_eq_embedH`, and
`besselTranslate_apply` gives the value of the operator. -/
noncomputable def besselTranslate (s : S.ResidueGL) :
    EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ]
      EuclideanSpace ℂ (S.Classes × S.BesselCoord) :=
  toEuclideanLin <| of fun x y ↦
    star (S.amplitudeSum .full (S.ratMiddle E).besselS x.1 s y.1 (x.2, y.2) / S.unipotentCovolume)

omit ok in
/-- The operator `r_ψ(s) = besselTranslate s`, whose blocks are sums over rational elements of the
Bessel subgroup with reduction `s`, vanishes for `s` off the image of that subgroup in
`S.ResidueGL`. -/
lemma besselTranslate_eq_zero {s : S.ResidueGL} (hs : s ∉ S.reducedImage besselS) :
    S.besselTranslate s = 0 := by
  ext φ x
  simp [besselTranslate, amplitudeSum_besselS_eq_zero hs, mulVec, dotProduct]

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which contains
a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. Let
`r_ψ(s) = S.besselTranslate s` be the operator on the source `ℂ^(classes × Bessel coordinates)`
whose blocks are the complex conjugates of the normalised amplitude sums of the rational elements of
the Bessel subgroup `besselS`. Let `γ` be a rational element of that subgroup over the block
`(c, s, c')`: `h_c⁻¹ γ h_c'` is integral with reduction `s`, where `h_c` represents the class `c`.
Suppose `W(γ y) = M W(y)` for all points `y` of `G` at the infinite places, where
`W = S.besselFn .full` is the vector of Bessel functions. Then the value of `r_ψ(s) φ` at the class
`c` is the entrywise conjugate of `M` applied to the value of `φ` at `c'`. -/
lemma besselTranslate_apply [HasPrimitiveRoot5040 E] {γ : S.G E} {c c' : S.Classes}
    {s : S.ResidueGL} (hγ : γ ∈ besselS) (hγ_over : γ ∈ S.termsOver c s c')
    {M : Matrix S.BesselCoord S.BesselCoord ℂ}
    (hM : ∀ y : NumberField.InfinitePlace E → 𝔰.G₁,
      S.besselFn .full (S.ratToInf γ * y) = M *ᵥ S.besselFn .full y)
    (φ : EuclideanSpace ℂ (S.Classes × S.BesselCoord)) (i : S.BesselCoord) :
    S.besselTranslate s φ (c, i) = ∑ j : S.BesselCoord, star (M i j) * φ (c', j) := by
  classical
  simp [besselTranslate, mulVec, dotProduct, sum_prod_type,
    amplitudeSum_besselS_apply hγ hγ_over hM, apply_ite, ite_div, S.unipotentCovolume_pos.ne']

/-- For admissible filling data `S` over a CM field `E` with a primitive `5040`-th root of unity,
the operator `r_ψ(1) = besselTranslate 1` is the identity. -/
lemma besselTranslate_one [HasPrimitiveRoot5040 E] : S.besselTranslate 1 = 1 := by
  ext φ ⟨c, i⟩
  have h_over : (1 : S.G E) ∈ S.termsOver c 1 c := (S.classUnipotent c).one_mem.2
  rw [besselTranslate_apply (one_mem _) h_over (M := 1) (by simp)]
  simp [Matrix.one_apply, apply_ite]

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which contains
a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. Then
`r_ψ(s t) = r_ψ(s) r_ψ(t)` for `s` and `t` in `R̄₀`. -/
lemma besselTranslate_mul [HasPrimitiveRoot5040 E] {s t : S.ResidueGL}
    (hs : s ∈ S.reducedImage besselS) (ht : t ∈ S.reducedImage besselS) :
    S.besselTranslate (s * t) = S.besselTranslate s * S.besselTranslate t := by
  -- If `γ` lies over `(c, s, c')` and `δ` over `(c', t, c'')`, then `γ δ` is over `(c, s t, c'')`.
  ext φ ⟨c, i⟩
  obtain ⟨c', γ, hγ, hγ_over⟩ := exists_besselS_mem_termsOver c hs
  obtain ⟨c'', δ, hδ, hδ_over⟩ := exists_besselS_mem_termsOver c' ht
  obtain ⟨M, -, hM⟩ := exists_unitary_besselFn_mul (side := .full) hγ
  obtain ⟨N, -, hN⟩ := exists_unitary_besselFn_mul (side := .full) hδ
  have hMN (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      S.besselFn .full (S.ratToInf (γ * δ) * y) = (M * N) *ᵥ S.besselFn .full y := by
    rw [map_mul, mul_assoc, hM, hN, mulVec_mulVec]
  have h_matrix : S.besselTranslate (s * t) φ (c, i) =
      ∑ k : S.BesselCoord, star ((M * N) i k) * φ (c'', k) :=
    besselTranslate_apply (mul_mem hγ hδ) (termsOver.mul hγ_over hδ_over) hMN φ i
  rw [h_matrix, mul_apply_eq_comp, besselTranslate_apply hγ hγ_over hM]
  simp only [besselTranslate_apply hδ hδ_over hN, Matrix.mul_apply, star_sum, star_mul', sum_mul,
    mul_sum, mul_assoc]
  exact sum_comm

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which contains
a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. Then
`r_ψ(t s) = r_ψ(t) r_ψ(s)` for `t` in `R̄₀` and every `s` in `Ḡ`. -/
lemma besselTranslate_mul_left [HasPrimitiveRoot5040 E] {t : S.ResidueGL}
    (ht : t ∈ S.reducedImage besselS) (s : S.ResidueGL) :
    S.besselTranslate (t * s) = S.besselTranslate t * S.besselTranslate s := by
  by_cases hs : s ∈ S.reducedImage besselS
  · exact besselTranslate_mul ht hs
  · rw [besselTranslate_eq_zero hs, mul_zero,
      besselTranslate_eq_zero (mt (mul_mem_cancel_left ht).1 hs)]

/-- Let `S` be admissible filling data over a CM field `E` with a primitive `5040`-th root of unity.
The adjoint of `r_ψ(s) = besselTranslate s` is `r_ψ(s⁻¹)`. So, by `besselTranslate_mul` and
`besselTranslate_one`, `r_ψ` is a unitary representation of the image of the Bessel subgroup. -/
lemma adjoint_besselTranslate [HasPrimitiveRoot5040 E] (s : S.ResidueGL) :
    (S.besselTranslate s).adjoint = S.besselTranslate s⁻¹ := by
  classical
  rw [besselTranslate, besselTranslate, ← toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  ext x y
  -- The block at `(c', s⁻¹, c)` is the adjoint of that at `(c, s, c')`.
  simp [amplitudeSum_besselS_inv y.1 x.1 s]

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which contains
a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. For `t`
in `R̄₀` the operator `r_ψ(t)` is unitary, so composing an operator `A` of the source on the left
with it does not change the Hilbert–Schmidt norm. -/
lemma hilbertSchmidtNorm_besselTranslate_comp [HasPrimitiveRoot5040 E] {t : S.ResidueGL}
    (ht : t ∈ S.reducedImage besselS)
    (A : EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ]
      EuclideanSpace ℂ (S.Classes × S.BesselCoord)) :
    hilbertSchmidtNorm (S.besselTranslate t ∘ₗ A) = hilbertSchmidtNorm A := by
  have h_adjoint : (S.besselTranslate t).adjoint * S.besselTranslate t = 1 := by
    rw [adjoint_besselTranslate, ← besselTranslate_mul (inv_mem ht) ht, inv_mul_cancel,
      besselTranslate_one]
  have h_norm (x : EuclideanSpace ℂ (S.Classes × S.BesselCoord)) :
      ‖S.besselTranslate t x‖ = ‖x‖ := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), ← LinearMap.adjoint_inner_right, ← mul_apply_eq_comp,
      h_adjoint, one_apply_eq_self, ← norm_eq_sqrt_re_inner]
  exact le_antisymm (hilbertSchmidtNorm_le_of_norm_le fun x ↦ (h_norm (A x)).le)
    (hilbertSchmidtNorm_le_of_norm_le fun x ↦ (h_norm (A x)).ge)

/-- Let `S` be admissible filling data over a CM field `E` with a primitive `5040`-th root of unity.
The trace of `r_ψ(s) = besselTranslate s` is a sum over classes `c` and Bessel coordinates `i`. Each
summand is the `(i, i)` entry of the full amplitude sum `amplitudeSum` of the terms in the Bessel
subgroup `besselS` over the block `(c, s⁻¹, c)`, divided by `unipotentCovolume`. -/
lemma trace_besselTranslate [HasPrimitiveRoot5040 E] (s : S.ResidueGL) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) (S.besselTranslate s) =
      ∑ y : S.Classes × S.BesselCoord,
        S.amplitudeSum .full (S.ratMiddle E).besselS y.1 s⁻¹ y.1 (y.2, y.2) /
          S.unipotentCovolume := by
  classical
  simp [LinearMap.trace_eq_sum_inner _ (basisFun _ ℂ), besselTranslate, inner_single_left,
    amplitudeSum_besselS_inv]

/-- Equivariance on the right. Let `S` be admissible filling data for a unitary group `G` over the
CM field `E`, which contains a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the
product of the general linear groups over the residue fields at the chosen places above the two
level primes `p₀`, `p₁`. The source is the Euclidean space with coordinates `(c, i)`, where `c` is a
class (a double coset of the definite unitary group `U(X₀)` for the level) and `i` is a coordinate
of the Bessel function `W` at the infinite places. Let `ρ` be a representation of `Ḡ` on `V` and `P`
a linear map from the source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of
`P_s = P* ρ(s) P` is the conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and
`A(c, s, c')` is the sum, over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with
reduction `s`, of an integral of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class
`c`). Let `r_ψ(s) = S.besselTranslate s` be the operator on the source with the same blocks, but
summed only over the `γ` in the Bessel subgroup `besselS` (block unitriangular elements times
`U(X₀)`), and let `R̄₀` be the image of that subgroup in `Ḡ`. Then `P_(s t) = P_s r_ψ(t)` for `t` in
`R̄₀`. -/
lemma HasAmplitudeBlocks.adjoint_comp_rep_mul_right [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P) (s : S.ResidueGL) {t : S.ResidueGL}
      (ht : t ∈ S.reducedImage besselS) :
    P.adjoint ∘ₗ ρ (s * t) ∘ₗ P = (P.adjoint ∘ₗ ρ s ∘ₗ P) ∘ₗ S.besselTranslate t := by
  classical
  refine (basisFun _ ℂ).toBasis.ext fun ⟨d, j⟩ ↦ ext_inner_right_basis (basisFun _ ℂ).toBasis ?_
  rintro ⟨c, i⟩
  -- A term `δ` of the Bessel subgroup over `(d, t⁻¹, d')` gives column `(d, j)` of `r_ψ(t)`.
  obtain ⟨d', δ, hδ, hδ_over⟩ := exists_besselS_mem_termsOver d (inv_mem ht)
  obtain ⟨N, -, hN⟩ := exists_unitary_besselFn_mul (side := .full) hδ
  have h_col : S.besselTranslate t (.single (d, j) 1) =
      ∑ k : S.BesselCoord, N j k • EuclideanSpace.single (d', k) 1 := by
    ext ⟨e, k⟩
    have h_block : starRingEnd ℂ (S.amplitudeSum .full (S.ratMiddle E).besselS e t d (k, j)) =
        if d' = e then S.unipotentCovolume * N j k else 0 := by
      rw [← Complex.star_def, ← amplitudeSum_besselS_inv, amplitudeSum_besselS_apply hδ hδ_over hN]
    by_cases h : d' = e
    · simp [besselTranslate, h_block, h, S.unipotentCovolume_pos.ne', Pi.single_apply,
        Function.swap]
    · simp [besselTranslate, h_block, h, Ne.symm h]
  -- The blocks of all terms transform in the same way, as the set of all terms is stable.
  have h_move : S.amplitudeSum .full .univ c (s * t) d (i, j) =
      ∑ k : S.BesselCoord, star (N j k) * S.amplitudeSum .full .univ c s d' (i, k) := by
    simpa using amplitudeSum_mul_inv_apply (by simp [IsStable] : S.IsStable Set.univ) hδ hδ_over
      (fun γ ↦ by simp) hN c s i j
  simp only [OrthonormalBasis.coe_toBasis, basisFun_apply]
  calc ⟪(P.adjoint ∘ₗ ρ (s * t) ∘ₗ P) (.single (d, j) 1), .single (c, i) 1⟫_ℂ
      = ∑ k : S.BesselCoord,
          star (N j k) * (S.amplitudeSum .full .univ c s d' (i, k) / S.unipotentCovolume) := by
        rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.comp_apply,
          hP (s * t) (c, i) (d, j), h_move, sum_div]
        simp only [mul_div_assoc]
    _ = ⟪((P.adjoint ∘ₗ ρ s ∘ₗ P) ∘ₗ S.besselTranslate t) (.single (d, j) 1),
          .single (c, i) 1⟫_ℂ := by
        simp only [LinearMap.comp_apply, h_col, map_sum, map_smul, sum_inner, inner_smul_left,
          LinearMap.adjoint_inner_left, hP s (c, i), Complex.star_def]

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which contains
a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. The
source is the Euclidean space with coordinates `(c, i)`, where `c` is a class (a double coset of the
definite unitary group `U(X₀)` for the level) and `i` is a coordinate of the Bessel function `W` at
the infinite places. Let `ρ` be a unitary representation of `Ḡ` on `V` and `P` a linear map from the
source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the
conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum,
over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral
of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Let
`r_ψ(s) = S.besselTranslate s` be the operator on the source with the same blocks, but summed only
over the `γ` in the Bessel subgroup `besselS` (block unitriangular elements times `U(X₀)`), and let
`R̄₀` be the image of that subgroup in `Ḡ`. Then `ρ(t) P = P r_ψ(t)` for `t` in `R̄₀`. -/
lemma HasAmplitudeBlocks.rep_comp_eq_comp_besselTranslate [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P)
    (hρ : ∀ (s : S.ResidueGL) (x y : V), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ) {t : S.ResidueGL}
    (ht : t ∈ S.reducedImage besselS) :
    ρ t ∘ₗ P = P ∘ₗ S.besselTranslate t := by
  -- The difference `d` is orthogonal to all translates of the image of `P`, hence to itself.
  ext1 φ
  set d : V := ρ t (P φ) - P (S.besselTranslate t φ) with hd
  have h_orth (s : S.ResidueGL) (φ' : EuclideanSpace ℂ (S.Classes × S.BesselCoord)) :
      ⟪ρ s (P φ'), d⟫_ℂ = 0 := by
    have h_apply : P.adjoint (ρ (s⁻¹ * t) (P φ)) =
        P.adjoint (ρ s⁻¹ (P (S.besselTranslate t φ))) :=
      LinearMap.congr_fun (hP.adjoint_comp_rep_mul_right s⁻¹ ht) φ
    have h_zero : P.adjoint (ρ s⁻¹ d) = 0 := by
      rw [hd, map_sub, map_sub, ← h_apply, map_mul, mul_apply_eq_comp, sub_self]
    rw [← hρ s⁻¹, ρ.inv_self_apply, ← LinearMap.adjoint_inner_right, h_zero, inner_zero_right]
  have h_self : ⟪d, d⟫_ℂ = 0 := by
    calc ⟪d, d⟫_ℂ = ⟪ρ t (P φ), d⟫_ℂ - ⟪P (S.besselTranslate t φ), d⟫_ℂ := inner_sub_left ..
      _ = 0 := by simpa [h_orth t φ] using h_orth 1 (S.besselTranslate t φ)
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h_self)

/-- Equivariance on the left. Let `S` be admissible filling data for a unitary group `G` over the CM
field `E`, which contains a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the
product of the general linear groups over the residue fields at the chosen places above the two
level primes `p₀`, `p₁`. The source is the Euclidean space with coordinates `(c, i)`, where `c` is a
class (a double coset of the definite unitary group `U(X₀)` for the level) and `i` is a coordinate
of the Bessel function `W` at the infinite places. Let `ρ` be a unitary representation of `Ḡ` on `V`
and `P` a linear map from the source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of
`P_s = P* ρ(s) P` is the conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and
`A(c, s, c')` is the sum, over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with
reduction `s`, of an integral of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class
`c`). Let `r_ψ(s) = S.besselTranslate s` be the operator on the source with the same blocks, but
summed only over the `γ` in the Bessel subgroup `besselS` (block unitriangular elements times
`U(X₀)`), and let `R̄₀` be the image of that subgroup in `Ḡ`. Then `P_(t s) = r_ψ(t) P_s` for `t` in
`R̄₀`. -/
lemma HasAmplitudeBlocks.adjoint_comp_rep_mul_left [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P)
    (hρ : ∀ (s : S.ResidueGL) (x y : V), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ) (s : S.ResidueGL)
    {t : S.ResidueGL} (ht : t ∈ S.reducedImage besselS) :
    P.adjoint ∘ₗ ρ (t * s) ∘ₗ P = S.besselTranslate t ∘ₗ (P.adjoint ∘ₗ ρ s ∘ₗ P) := by
  -- The adjoint of `t⁻¹ P = P r_ψ(t⁻¹)` is `P* t = r_ψ(t) P*`.
  have h_adjoint : P.adjoint ∘ₗ ρ t = S.besselTranslate t ∘ₗ P.adjoint := by
    simpa [LinearMap.adjoint_comp, adjoint_rep_of_unitary hρ, adjoint_besselTranslate] using
      congrArg LinearMap.adjoint (hP.rep_comp_eq_comp_besselTranslate hρ (inv_mem ht))
  rw [map_mul, End.mul_eq_comp, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, h_adjoint]
  simp only [LinearMap.comp_assoc]

/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which contains
a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. The
source is the Euclidean space with coordinates `(c, i)`. Suppose `HasAmplitudeBlocks`: the block
`(c, c')` of `P_s = P* ρ(s) P` is the conjugate of `A(c, s, c') / ν`, where
`ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum, over the rational `γ` in `G` such that
`h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs
(`h_c` represents the class `c`). Then the squared Hilbert–Schmidt norm of `P_s - r_ψ(s)` is the
second moment `∑ ‖A'(c, s, c')‖² / ν²` over pairs of classes, where `A'` is summed over the `γ`
outside the Bessel subgroup and `‖·‖` is the Euclidean norm of the entries. -/
lemma HasAmplitudeBlocks.hilbertSchmidtNorm_sub_besselTranslate_sq [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P) (s : S.ResidueGL) :
    hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) ^ 2 =
      secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) {s} := by
  classical
  apply hilbertSchmidtNorm_sq_of_entries
  intro x y
  rw [LinearMap.sub_apply, inner_sub_left, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
    LinearMap.comp_apply, hP s x y, amplitudeSum_eq_inter_compl_add_inter Set.univ
      (S.ratMiddle E).besselS]
  simp [besselTranslate, inner_single_right, add_div, Set.univ_inter]

open scoped Classical in
/-- **Second moment near the Bessel subgroup.** Let `S` be admissible filling data for a unitary
group `G` over the CM field `E`, which contains a primitive `5040`-th root of unity, and let
`Ḡ = S.ResidueGL` be the product of the general linear groups over the residue fields at the chosen
places above the two level primes `p₀`, `p₁`. The source is the Euclidean space with coordinates
`(c, i)`, where `c` is a class (a double coset of the definite unitary group `U(X₀)` for the level)
and `i` is a coordinate of the Bessel function `W` at the infinite places. Let `ρ` be a
representation of `Ḡ` on `V` and `P` a linear map from the source to `V`. Suppose
`HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the conjugate of
`A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum, over the
rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral of
`W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Let
`r_ψ(s) = S.besselTranslate s` be the operator on the source with the same blocks, but summed only
over the `γ` in the Bessel subgroup `besselS` (block unitriangular elements times `U(X₀)`), and let
`R̄₀` be the image of that subgroup in `Ḡ`. Then `∑ ‖P_s - r_ψ(s)‖² ≤ b⁻¹² 𝒟_id` in Hilbert–Schmidt
norm, the sum being over the `s` that coincide with an element of `R̄₀` above the prime `p_(i+1)`
other than `p_i`. Here `b = S.b ≥ 1000` is the size parameter of `S`, and
`𝒟_id = S.identitySecondMoment` is `#R̄₀` times the dimension of the source. -/
theorem HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sub_besselTranslate_sq_le [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P) (i : Fin 2) :
    ∑ s : S.ResidueGL with ∃ t ∈ S.reducedImage besselS, s (i + 1) = t (i + 1),
      hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) ^ 2 ≤
      (S.b ^ 12)⁻¹ * S.identitySecondMoment := by
  simp only [hP.hilbertSchmidtNorm_sub_besselTranslate_sq]
  exact (secondMoment_eq_sum_secondMoment_singleton _
    {s | ∃ t ∈ S.reducedImage besselS, s (i + 1) = t (i + 1)}).symm.trans_le
      (secondMoment_compl_besselS_le (i + 1))

omit ok in
open scoped Classical in
/-- If `#R̄₀ · y ≤ b⁻¹² 𝒟_id`, then `y ≤ b⁻¹² D_X`. Here `R̄₀` is the image of the Bessel subgroup
in `S.ResidueGL`, `b = S.b`, `D_X = sourceDim` and `𝒟_id = identitySecondMoment = #R̄₀ · D_X`. -/
lemma le_sourceDim_div_of_card_nsmul_le {y : ℝ}
    (h_le : #{s : S.ResidueGL | s ∈ S.reducedImage besselS} • y ≤
      (S.b ^ 12)⁻¹ * S.identitySecondMoment) :
    y ≤ S.sourceDim / S.b ^ 12 := by
  rw [identitySecondMoment, nsmul_eq_mul, ← Fintype.card_subtype, card_eq_nat_card, mul_left_comm,
    ← div_eq_inv_mul] at h_le
  exact le_of_mul_le_mul_left h_le (Nat.cast_pos.2 Nat.card_pos)

/-- **Near isometry.** Let `S` be admissible filling data for a unitary group `G` over the CM field
`E`, which contains a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the product of
the general linear groups over the residue fields at the chosen places above the two level primes
`p₀`, `p₁`. The source is the Euclidean space with coordinates `(c, i)`, where `c` is a class (a
double coset of the definite unitary group `U(X₀)` for the level) and `i` is a coordinate of the
Bessel function `W` at the infinite places. Let `ρ` be a representation of `Ḡ` on `V` and `P` a
linear map from the source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of
`P_s = P* ρ(s) P` is the conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and
`A(c, s, c')` is the sum, over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with
reduction `s`, of an integral of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class
`c`). Then `‖P* P - 1‖² ≤ b⁻¹² D_X` in Hilbert–Schmidt norm, where `D_X = S.sourceDim` is the
dimension of the source and `b = S.b ≥ 1000` is the size parameter of `S`. -/
theorem HasAmplitudeBlocks.hilbertSchmidtNorm_sub_one_sq_le [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P) :
    hilbertSchmidtNorm (P.adjoint ∘ₗ P - 1) ^ 2 ≤ S.sourceDim / S.b ^ 12 := by
  classical
  -- For `s ∈ R̄₀` we have `P_s - r_ψ(s) = (P* P - 1) r_ψ(s)`, which has the norm of `P* P - 1`.
  set D : End ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) := P.adjoint ∘ₗ P - 1 with hD
  have h_eq (s : S.ResidueGL) (hs : s ∈ S.reducedImage besselS) :
      hilbertSchmidtNorm D = hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) := by
    have h_right : P.adjoint ∘ₗ ρ s ∘ₗ P = (P.adjoint ∘ₗ P) ∘ₗ S.besselTranslate s := by
      simpa [End.one_eq_id] using hP.adjoint_comp_rep_mul_right 1 hs
    calc hilbertSchmidtNorm D
      _ = hilbertSchmidtNorm (S.besselTranslate s⁻¹ ∘ₗ D.adjoint) := by
        rw [hilbertSchmidtNorm_besselTranslate_comp (inv_mem hs), hilbertSchmidtNorm_adjoint]
      _ = hilbertSchmidtNorm (D ∘ₗ S.besselTranslate s) := by
        rw [← adjoint_besselTranslate, ← LinearMap.adjoint_comp, hilbertSchmidtNorm_adjoint]
      _ = hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) := by
        rw [h_right, hD, LinearMap.sub_comp, End.one_eq_id, LinearMap.id_comp]
  refine le_sourceDim_div_of_card_nsmul_le ?_
  calc #{s : S.ResidueGL | s ∈ S.reducedImage besselS} • hilbertSchmidtNorm D ^ 2
    _ ≤ ∑ s with s ∈ S.reducedImage besselS,
        hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) ^ 2 :=
      card_nsmul_le_sum _ _ _ fun s hs ↦ by rw [h_eq s (mem_filter.1 hs).2]
    _ ≤ ∑ s with ∃ t ∈ S.reducedImage besselS, s (0 + 1) = t (0 + 1),
        hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ fun s _ hs ↦ ⟨s, hs, rfl⟩)
        fun s _ _ ↦ sq_nonneg _
    _ ≤ (S.b ^ 12)⁻¹ * S.identitySecondMoment :=
      hP.sum_hilbertSchmidtNorm_sub_besselTranslate_sq_le 0

omit ok in
/-- The identity of the source has squared Hilbert–Schmidt norm `D_X = sourceDim`. -/
lemma hilbertSchmidtNorm_one_sq_eq_sourceDim :
    hilbertSchmidtNorm (1 : End ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord))) ^ 2 =
      S.sourceDim := by
  simp [hilbertSchmidtNorm_sq_eq_sum (basisFun _ ℂ), sourceDim]

/-- Let `S` be admissible filling data (`Filling`, `IsAdmissible`) for a unitary group `G` over the
CM field `E`, which contains a primitive `5040`-th root of unity, and let `Ḡ = S.ResidueGL` be the
product of the general linear groups over the residue fields at the chosen places above the two
level primes `p₀`, `p₁`. The source is the Euclidean space with coordinates `(c, i)`, where `c` is a
class (a double coset of the definite unitary group `U(X₀)` for the level) and `i` is a coordinate
of the Bessel function `W` at the infinite places. Let `ρ` be a representation of `Ḡ` on `V` and `P`
a linear map from the source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of
`P_s = P* ρ(s) P` is the conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and
`A(c, s, c')` is the sum, over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with
reduction `s`, of an integral of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class
`c`). Then `‖P* P‖² ≤ 2 D_X` in Hilbert–Schmidt norm, where `D_X = S.sourceDim` is the dimension of
the source. -/
lemma HasAmplitudeBlocks.hilbertSchmidtNorm_adjoint_comp_sq_le [HasPrimitiveRoot5040 E]
    (hP : S.HasAmplitudeBlocks ρ P) :
    hilbertSchmidtNorm (P.adjoint ∘ₗ P) ^ 2 ≤ 2 * S.sourceDim := by
  -- `‖P* P‖ ≤ ‖P* P - 1‖ + ‖1‖ ≤ (1/3 + 1) ‖1‖`
  have hb : 1000 ≤ S.b := S.thousand_le_b
  set one : End ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) := 1
  have h_triangle : hilbertSchmidtNorm (P.adjoint ∘ₗ P) ≤ hilbertSchmidtNorm (P.adjoint ∘ₗ P - one)
    + hilbertSchmidtNorm one := by
    simpa [hilbertSchmidtNorm] using norm_add_le (hilbertSchmidtVector (P.adjoint ∘ₗ P - one))
      (hilbertSchmidtVector one)
  have h_near : hilbertSchmidtNorm (P.adjoint ∘ₗ P - one) ≤ hilbertSchmidtNorm one / 3 := by
    refine le_of_pow_le_pow_left₀ (n := 2) (by decide)
      (div_nonneg (hilbertSchmidtNorm_nonneg _) zero_le_three) ?_
    grw [hP.hilbertSchmidtNorm_sub_one_sq_le, div_pow, hilbertSchmidtNorm_one_sq_eq_sourceDim,
      ← hb]
    gcongr
    norm_num
  rw [← hilbertSchmidtNorm_one_sq_eq_sourceDim]
  nlinarith [hilbertSchmidtNorm_nonneg (P.adjoint ∘ₗ P), hilbertSchmidtNorm_nonneg one]

/-- **Second moment.** Let `S` be admissible filling data (`Filling`, `IsAdmissible`) for a unitary
group `G` over the CM field `E`, which carries Weil data (a primitive `5040`-th root of unity and a
splitting character, see `WeilData`), and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. The
source is the Euclidean space with coordinates `(c, i)`, where `c` is a class (a double coset of the
definite unitary group `U(X₀)` for the level) and `i` is a coordinate of the Bessel function `W` at
the infinite places. Let `ρ` be a unitary representation of `Ḡ` on `V` and `P` a linear map from the
source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the
conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum,
over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral
of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Then
`∑ ‖P_s‖² ≤ (1 + 9 b⁻⁴) 𝒟_main` in Hilbert–Schmidt norm, the sum being over all `s` in `Ḡ`. Here
`b = S.b ≥ 1000` is the size parameter of `S`, and `𝒟_main = S.mainSecondMoment` is the square of
the dimension of the source divided by the product of `S.besselDegree` (the product of the degree
constants of the local Bessel systems) and `New.mass` (the sum of `1 / #Aut` over the genus of the
standard lattice). -/
theorem HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le [WeilData E] (hP : S.HasAmplitudeBlocks ρ P)
    (hρ : ∀ (s : S.ResidueGL) (x y : V), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ) :
    ∑ s : S.ResidueGL, hilbertSchmidtNorm (P.adjoint ∘ₗ ρ s ∘ₗ P) ^ 2 ≤
      (1 + 9 / S.b ^ 4) * S.mainSecondMoment := by
  -- `s ↦ ‖P_s‖²` has positive type and `‖P_1‖² ≤ 2 D_X`, so `sum_secondMoment_le` applies.
  have h_gram (s t : S.ResidueGL) : ⟪hilbertSchmidtVector ((ρ s ∘ₗ P) ∘ₗ (ρ s ∘ₗ P).adjoint),
      hilbertSchmidtVector ((ρ t ∘ₗ P) ∘ₗ (ρ t ∘ₗ P).adjoint)⟫_ℂ =
        (secondMoment (S.amplitudeSum .full .univ) {s⁻¹ * t} : ℝ) := by
    rw [inner_hilbertSchmidtVector_translate hρ, hP.hilbertSchmidtNorm_sq_eq_secondMoment]
  have h_one : secondMoment (S.amplitudeSum .full .univ) {1} ≤ 2 * S.sourceDim := by
    rw [← hP.hilbertSchmidtNorm_sq_eq_secondMoment, map_one, End.one_eq_id (M := V),
      LinearMap.id_comp]
    exact hP.hilbertSchmidtNorm_adjoint_comp_sq_le
  simpa [hP.hilbertSchmidtNorm_sq_eq_secondMoment] using sum_secondMoment_le _ h_gram h_one

/-! ## Good forms: the remainder -/

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
open scoped Classical in
omit ok in
/-- **The remainder.** Let `S` be admissible filling data (`Filling`, `IsAdmissible`) for a unitary
group `G` over the CM field `E`, which contains a primitive `5040`-th root of unity, and let
`Ḡ = S.ResidueGL` be the product of the general linear groups over the residue fields at the chosen
places above the two level primes `p₀`, `p₁`. The source is the Euclidean space with coordinates
`(c, i)`, where `c` is a class (a double coset of the definite unitary group `U(X₀)` for the level)
and `i` is a coordinate of the Bessel function `W` at the infinite places. Let `ρ` be a unitary
representation of `Ḡ` on `V` and `P` a linear map from the source to `V`. Suppose
`HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the conjugate of
`A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum, over the
rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral of
`W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Let
`r_ψ(s) = S.besselTranslate s` be the operator on the source with the same blocks, but summed only
over the `γ` in the Bessel subgroup `besselS` (block unitriangular elements times `U(X₀)`). Write
`Ḡ = G_0 × G_1`, where `G_i` is the factor above `p_i`, made of matrices indexed by the basis
`𝔰.BesselIndex` of the hermitian space of shape `𝔰`, and embedded by `Pi.mulSingle i`. Then for a
central idempotent `x = ∑ x(t) t` of `ℂ[G_i]` (an idempotent whose coefficients form a class
function; it is then self-adjoint) we have `‖∑ x(t) (P_t - r_ψ(t))‖² ≤ b⁻¹² D_X` in Hilbert–Schmidt
norm, the sum being over `t` in `G_i`. Here `b = S.b ≥ 1000` is the size parameter of `S` and
`D_X = S.sourceDim` is the dimension of the source. -/
lemma HasAmplitudeBlocks.hilbertSchmidtNorm_sum_smul_sub_besselTranslate_sq_le [S.IsAdmissible]
    [HasPrimitiveRoot5040 E] {ρ : Representation ℂ S.ResidueGL V}
    {P : EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ] V} (hP : S.HasAmplitudeBlocks ρ P)
    (hρ : ∀ (s : S.ResidueGL) (v v' : V), ⟪ρ s v, ρ s v'⟫_ℂ = ⟪v, v'⟫_ℂ) (i : Fin 2)
    {x : MonoidAlgebra ℂ (∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val))}
    (hx : IsCentralProj x) :
    hilbertSchmidtNorm (∑ t : ∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val),
        x.coeff t •
          (P.adjoint ∘ₗ ρ (Pi.mulSingle i t) ∘ₗ P - S.besselTranslate (Pi.mulSingle i t))) ^ 2 ≤
      S.sourceDim / S.b ^ 12 := by
  -- Put `P'_s = P_s - r_ψ(s)` and `P'_x = ∑ x(t) P'_t`. The map `f ↦ ∑ x(t) f(· t)` is a
  -- contraction on functions on the group. Apply it to `P'` cut down to `Ω = R̄₀ G_i`, where `R̄₀`
  -- is the image of the Bessel subgroup; the value at `s ∈ R̄₀` is `r_ψ(s) P'_x`, which has the
  -- norm of `P'_x`.
  let G (j : Fin 2) : Type := ∀ w : S.chosenPlaces j, GL 𝔰.BesselIndex (ResField w.val)
  let φ : G i →* S.ResidueGL := MonoidHom.mulSingle G i
  let P' (s : S.ResidueGL) : End ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) :=
    P.adjoint ∘ₗ ρ s ∘ₗ P - S.besselTranslate s
  let Ω : Set S.ResidueGL := {s | ∃ r ∈ S.reducedImage besselS, s (i + 1) = r (i + 1)}
  -- `f` is `P'` cut down to `Ω`, with values in the Hilbert space of operators.
  let f (s : S.ResidueGL) :
      PiLp 2 fun _ : Fin (finrank ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord))) ↦
        EuclideanSpace ℂ (S.Classes × S.BesselCoord) :=
    if s ∈ Ω then hilbertSchmidtVector (P' s) else 0
  have h_left {s : S.ResidueGL} (hs : s ∈ S.reducedImage besselS) (u : S.ResidueGL) :
      P' (s * u) = S.besselTranslate s ∘ₗ P' u := by
    simp only [P', hP.adjoint_comp_rep_mul_left hρ u hs, besselTranslate_mul_left hs,
      LinearMap.comp_sub, End.mul_eq_comp]
  have h_value {s : S.ResidueGL} (hs : s ∈ S.reducedImage besselS) :
      ‖∑ t : G i, x.coeff t • f (s * φ t)‖ = hilbertSchmidtNorm
        (∑ t : G i, x.coeff t • P' (φ t)) := by
    -- `φ t` is trivial above the other prime, so `s * φ t` lies in `Ω`.
    have h_mem (t : G i) : s * φ t ∈ Ω := ⟨s, hs, by simp [φ]⟩
    have h_sum : ∑ t : G i, x.coeff t • f (s * φ t) =
        hilbertSchmidtVector (S.besselTranslate s ∘ₗ ∑ t : G i, x.coeff t • P' (φ t)) := by
      simp only [f, h_mem, ite_true, h_left hs, ← End.mul_eq_comp, mul_sum, mul_smul_comm, map_sum,
        map_smul]
    rw [h_sum, ← hilbertSchmidtNorm, hilbertSchmidtNorm_besselTranslate_comp hs]
  have h_conv : ∑ s : S.ResidueGL, ‖∑ t : G i, x.coeff t • f (s * φ t)‖ ^ 2 ≤
      ∑ s : S.ResidueGL, ‖f s‖ ^ 2 := by
    calc ∑ s : S.ResidueGL, ‖∑ t : G i, x.coeff t • f (s * φ t)‖ ^ 2
      _ = ∑ s : S.ResidueGL, ‖∑ t : G i, x.coeff t • f ((φ t)⁻¹ * s)⁻¹‖ ^ 2 := by
        rw [← Equiv.sum_comp (Equiv.inv S.ResidueGL)]
        simp
      _ ≤ ∑ s : S.ResidueGL, ‖f s⁻¹‖ ^ 2 := hx.sum_norm_sq_conv_le φ fun s ↦ f s⁻¹
      _ = ∑ s : S.ResidueGL, ‖f s‖ ^ 2 := Equiv.sum_comp (Equiv.inv S.ResidueGL) fun s ↦ ‖f s‖ ^ 2
  refine le_sourceDim_div_of_card_nsmul_le ?_
  calc #{s : S.ResidueGL | s ∈ S.reducedImage besselS} • hilbertSchmidtNorm
         (∑ t : G i, x.coeff t • P' (φ t)) ^ 2
    _ ≤ ∑ s : S.ResidueGL with s ∈ S.reducedImage besselS, ‖∑ t : G i,
      x.coeff t • f (s * φ t)‖ ^ 2 :=
      card_nsmul_le_sum _ _ _ fun s hs ↦ by rw [h_value (mem_filter.1 hs).2]
    _ ≤ ∑ s : S.ResidueGL, ‖∑ t : G i, x.coeff t • f (s * φ t)‖ ^ 2 := by grw [← subset_univ]
    _ ≤ ∑ s : S.ResidueGL, ‖f s‖ ^ 2 := h_conv
    _ = ∑ s : S.ResidueGL with s ∈ Ω, hilbertSchmidtNorm (P' s) ^ 2 := by
      simp [f, sum_filter, apply_ite (‖·‖), ite_pow, hilbertSchmidtNorm]
    _ ≤ (S.b ^ 12)⁻¹ * S.identitySecondMoment :=
      hP.sum_hilbertSchmidtNorm_sub_besselTranslate_sq_le i

end Moments

/-! ## Good forms: the trace of `r_ψ` against a central idempotent of one factor -/

section BesselTrace

open NumberField Pi MeasureTheory Floors IntegralPlace Finset ENNReal Complex
open scoped Classical

open scoped BigOperators

variable {E : Type} [Field E] [CMType E] [WeilData E] {𝔰 : Shape}
  (S : Filling E 𝔰) [ok : S.IsAdmissible]

/-- For a finite group `G` and a central idempotent `x` of the complex group algebra
`MonoidAlgebra ℂ G` (`IsCentralProj x`), `∑ s, ‖x.coeff s‖² = (x.coeff 1).re`. -/
lemma sum_norm_sq_coeff_of_isCentralProj {G : Type*} [Group G] [Fintype G] {x : MonoidAlgebra ℂ G}
    (hx : IsCentralProj x) :
    ∑ s : G, ‖x.coeff s‖ ^ 2 = (x.coeff 1).re := by
  -- `x s⁻¹ = conj (x s)` as `|G| x` is a character; compare the coefficients of `1` in `x * x = x`.
  have h_inv (s : G) : x.coeff s⁻¹ = starRingEnd ℂ (x.coeff s) := by
    simpa using hx.isChar_card_mul_coeff.apply_inv s
  simpa [h_inv, x.coeff_mul_apply_left, Complex.sq_norm, Finsupp.sum_fintype, mul_conj] using
    congr_arg (fun y ↦ (y.coeff 1).re) hx.1

omit ok in
omit [WeilData E] in
/-- Let `S` be filling data over a CM field `E`. Let `γ` be in the Bessel
subgroup and `k = translateByClassReps c c γ`, that is `h_c⁻¹ γ h_c` for the representative `h_c` of
the class `c`. If `k` lies in the stabilizer `latticeStabilizer` of the lattice and reduces to `1`
at the chosen places above the level prime `p_j`, then `k` lies in the unipotent subgroup
`besselU`. -/
lemma mem_besselU_of_reduction_eq_one {c : S.Classes} {γ : S.G E} {j : Fin 2}
    {k : S.latticeStabilizer}
    (hγ : γ ∈ (S.ratMiddle E).besselS) (hk : k.val = S.translateByClassReps c c γ)
    (hk_red : S.reduction k j = 1) :
    k.val ∈ (S.latticeMiddle (𝔸f E)).besselU := by
  -- Write `γ = u δ` with `u` unipotent and `δ` in `U(X₀)`; then `k = u' y` with `y = h_c⁻¹ δ h_c`
  -- and `u'` unipotent. It remains to see that `δ = 1`.
  obtain ⟨u, hu, δ, rfl⟩ : ∃ u ∈ besselU, ∃ g : U 1, γ = u * toBesselH 𝔰 (S.N : E) g :=
    exists_besselU_mul_toBesselH hγ S.isUnit_natCast_N
  let y : Gf E 𝔰.κ := c.out⁻¹ * stdEmbFin δ * c.out
  have hy : k * (S.inclHFin y)⁻¹ ∈ besselU := by
    simpa [y, hk, translateByClassReps, ratToFin_toBesselH, mul_assoc] using
      hu.translateByClassReps_mem_besselU c
  -- The `H`-part of an integral element of `𝖴 H` is integral.
  have hyK : S.inclHFin y ∈ S.latticeStabilizer :=
    (mem_unitaryLevel_of_besselU_mul hy (inclHFin_mem_besselH y)
      (unitaryLevel_one.ge (by simpa [latticeStabilizer] using k.prop))).1
  -- Each entry of `y` is the entry of `k` or of `1`, so `y` reduces to `1` where `k` does.
  have h_red (w : S.chosenPlaces j) : S.reduction ⟨S.inclHFin y, hyK⟩ j w = 1 := by
    ext a b
    rcases besselH_apply_eq_or hy (inclHFin_mem_besselH y) a b with h_entry | h_entry
    · rw [reduction_apply_congr k j w (by simpa using h_entry), hk_red, Pi.one_apply]
    · rw [reduction_apply_congr 1 j w h_entry, map_one, Pi.one_apply, Pi.one_apply]
  -- Freeness: a rational `δ` whose conjugate `y` is integral and reduces to `1` is `1`.
  obtain rfl := eq_one_of_reduceAt_eq_one le_rfl j _ fun w ↦
    (S.reduction_inclHFin_eq_one_iff hyK j w).mp (h_red w)
  -- Now `δ = 1`, hence `y = 1` and `k = k y⁻¹`.
  simpa [y] using hy

/-- The character `ψ_U` on the image `Ū₀` of the integral unipotent elements in the finite group
`S.ResidueGL`, extended by `0`. Its value at `s` is `S.unipotentChar k` for a unipotent `k` that
reduces to `s`; the choice does not matter (`extendedBesselChar_toPlaces_eq_reducedChar`). -/
noncomputable def reducedChar (s : S.ResidueGL) : ℂ :=
  if h : ∃ k : S.latticeStabilizer, k.val ∈ (S.latticeMiddle (𝔸f E)).besselU ∧ S.reduction k = s
    then
    S.unipotentChar h.choose
  else
    0

/-- The mean `ψ_U^♮(s)` of `ψ_U = reducedChar`, extended by `0`, over the conjugates of `s` in the
finite group `S.ResidueGL`. -/
noncomputable def reducedCharMean (s : S.ResidueGL) : ℂ := 𝔼 g : S.ResidueGL,
  S.reducedChar (g * s * g⁻¹)

omit ok [WeilData E] in
/-- The mean `ψ_U^♮` of `ψ_U` over conjugates is a class function. -/
lemma reducedCharMean_conj (g s : S.ResidueGL) :
    S.reducedCharMean (g * s * g⁻¹) = S.reducedCharMean s :=
  expect_equiv (.mulRight g) (by simp) fun t _ ↦ by simp [mul_assoc]

/-- Let `S` be admissible filling data over a CM field `E` with Weil data, and let `s` in
`S.ResidueGL` be `1` above the level prime `p_j`. The trace of `r_ψ(s) = S.besselTranslate s`, the
translation of the source by `s` twisted by the Bessel character, is `D_X ψ_U(s)`. Here
`D_X = S.sourceDim` and `ψ_U = S.reducedChar` is the character of the integral unipotent group, read
on reductions and extended by `0` off its image. -/
lemma trace_besselTranslate_eq_mul_reducedChar {j : Fin 2} {s : S.ResidueGL} (hs : s j = 1) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) (S.besselTranslate s) =
      S.sourceDim * S.reducedChar s := by
  rw [trace_besselTranslate, reducedChar]
  split_ifs with h
  · -- If `s` is the reduction of a unipotent `k`, the block at `s⁻¹` is `ψ_U(k)` times the block at
    -- `1`, which is the covolume times the identity.
    obtain ⟨hk_unip, hk_red⟩ := h.choose_spec
    have h_move (c : S.Classes) :=
      amplitudeSum_besselU_mul (side := .full) isStable_besselS (u := 1) (one_mem _) hk_unip c 1 c
    simp [hk_red] at h_move
    simp [h_move, amplitudeSum_besselS_one_eq_ite, S.unipotentCovolume_pos.ne', sourceDim]
  · -- Otherwise there is no term: its translate `k` by the class representatives would be unipotent
    -- with the reduction `s⁻¹`.
    have (c : S.Classes) : IsEmpty ↥(↑(S.ratMiddle E).besselS ∩ S.termsOver c s⁻¹ c) :=
      ⟨fun ⟨_, hγ, k, hk_red, hk⟩ ↦ h ⟨k⁻¹, inv_mem <|
        S.mem_besselU_of_reduction_eq_one (j := j) hγ hk (by simp [hk_red, hs]), by simp [hk_red]⟩⟩
    simp [amplitudeSum, tsum_empty]

omit ok [WeilData E] in
/-- Let `S` be filling data for a unitary group `G` over the CM field `E`, with level primes `p₀`,
`p₁`, and let `Ḡ = S.ResidueGL` be the product of the general linear groups over the residue fields
at the chosen places above them. Let `M = p₀ p₁`, and let `T` be a finite conjugation-stable set of
finite places off which `M⁻¹` is integral, so that `T` contains the places above `M`. Over the
product `LocProd T` of the completions at `T`, let `K` be the group of integral points of `G` and
`K(M)` its principal congruence subgroup of level `M`. Let `F` be a filling datum (`IsFillingData`):
a large lattice datum with `3ϱ + 6` hyperbolic pairs and `k - (6ϱ + 13)` orthonormal vectors, for
the ranks `ϱ = 𝔰.ϱ` and `k = 𝔰.k` of the shape, with modulus `F.levelUnit = M` and local character
`ψ(x) = ψ_f(-x / ϖ)`, where `ϖ` generates the different. The function
`χ_M = extendedBesselChar F.levelUnit` is `ψ(σ(u) / M)` on `u K(M)` for `u` in the block
unitriangular group `𝖴 = besselU`, with `σ(u)` the sum of the entries at the simple roots, and `0`
off `𝖴 K(M)`. Then for `l` in the stabilizer of the lattice, `χ_M` at the component of `l` at `T` is
`ψ_U` at the reduction of `l`, where `ψ_U = S.reducedChar` is the character `u ↦ ψ_f(-σ(u) / (M ϖ))`
of the integral points of `𝖴`, read on their reductions in `Ḡ` and extended by `0`. -/
lemma extendedBesselChar_toPlaces_eq_reducedChar {T : Finset (FinPlace E)} [T.StarStable]
    [Fact (S.ideleM⁻¹.val ∈ integralOff T)] [hInt : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (l : S.latticeStabilizer) :
    extendedBesselChar F.levelUnit (S.toPlaces T l) = S.reducedChar (S.reduction l) := by
  rw [reducedChar]
  split_ifs with h
  · obtain ⟨hk_unip, hk_red⟩ :
        h.choose.val ∈ (S.latticeMiddle (𝔸f E)).besselU ∧ S.reduction h.choose = S.reduction l :=
      h.choose_spec
    have h_local : S.toPlaces T h.choose ∈ (S.latticeMiddle (LocProd T)).besselU :=
      hk_unip.map_mem_agreeWithOneOn _
    have h_cong : (S.toPlaces T h.choose)⁻¹ * S.toPlaces T l ∈
        unitaryLevel hInt.integers F.levelUnit (S.latticeMiddle (LocProd T)).splitGram :=
      (hF.reduction_eq_iff _ l).mp hk_red
    rw [extendedBesselChar_eq h_local h_cong,
      hF.psi_simpleRootSum_eq_unipotentChar (mem_latticeStabilizer_iff.mp h.choose.prop).1]
  · -- If `l ∈ u K(M)` at `T` with `u` unipotent, lift `u` to an integral unipotent element.
    by_contra h_ne
    obtain ⟨u, hu, hul⟩ : ∃ u ∈ (S.latticeMiddle (LocProd T)).besselU,
        u⁻¹ * S.toPlaces T l ∈ unitaryLevel hInt.integers F.levelUnit
          (S.latticeMiddle (LocProd T)).splitGram :=
      exists_besselU_of_extendedBesselChar_ne_zero h_ne
    obtain ⟨k, rfl, hk_off, hk_unip, -⟩ := S.exists_isIntegralOff_toPlaces_eq u
    have hk_int : k ∈ S.latticeStabilizer := by
      refine mem_latticeStabilizer_iff.mpr ⟨hk_off, ?_⟩
      -- `k = l (k⁻¹ l)⁻¹`, and both factors are integral at `T`.
      simpa using
        div_mem (mem_latticeStabilizer_iff.mp l.prop).2 (unitaryLevel_le_unitaryLevel_one hul)
    exact h ⟨⟨k, hk_int⟩, hk_unip hu, (hF.reduction_eq_iff ⟨k, hk_int⟩ l).mpr hul⟩

omit [WeilData E] in
/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, and let
`Ḡ = S.ResidueGL` be the product of the general linear groups over the residue fields at the chosen
places above the two level primes `p₀`, `p₁`. Let `M = p₀ p₁`, and let `T` be a finite
conjugation-stable set of finite places off which `M⁻¹` is integral, so that `T` contains the places
above `M`. Over the product `LocProd T` of the completions at `T`, let `K` be the group of integral
points of `G` and `K(M)` its principal congruence subgroup of level `M`. Let `F` be a filling datum
(`IsFillingData`): a large lattice datum with `3ϱ + 6` hyperbolic pairs and `k - (6ϱ + 13)`
orthonormal vectors, for the ranks `ϱ = 𝔰.ϱ` and `k = 𝔰.k` of the shape, with modulus
`F.levelUnit = M` and local character `ψ(x) = ψ_f(-x / ϖ)`, where `ϖ` generates the different. The
function `χ_M = extendedBesselChar F.levelUnit` is `ψ(σ(u) / M)` on `u K(M)` for `u` in the block
unitriangular group `𝖴 = besselU`, with `σ(u)` the sum of the entries at the simple roots, and `0`
off `𝖴 K(M)`. Then for `l` in the stabilizer of the lattice, `∫_K χ_M(y l y⁻¹) dy` for the measure
`dy = F.groupMeasure` is `vol(K)` times the value at the reduction of `l` of `S.reducedCharMean`,
the mean of `ψ_U` over conjugates. Here `ψ_U = S.reducedChar` is the character
`u ↦ ψ_f(-σ(u) / (M ϖ))` of the integral points of `𝖴`, read on their reductions in `Ḡ` and extended
by `0`. -/
lemma integral_extendedBesselChar_conj_eq {T : Finset (FinPlace E)} [T.StarStable]
    [Fact (S.ideleM⁻¹.val ∈ integralOff T)] [hInt : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (l : S.latticeStabilizer) :
    ∫ y : (S.latticeMiddle (LocProd T)).G
        in unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram,
        extendedBesselChar F.levelUnit (y * S.toPlaces T l * y⁻¹) ∂F.groupMeasure =
      F.groupMeasure.real (unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram) •
        S.reducedCharMean (S.reduction l) := by
  -- Translate `y` by a lift `σ s` of each `s` in `S.ResidueGL` and sum; the integrand becomes
  -- constant.
  set K : Subgroup (U (S.latticeMiddle (LocProd T)).splitGram) :=
    unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram
  let φ (y : (S.latticeMiddle (LocProd T)).G) : ℂ :=
    extendedBesselChar F.levelUnit (y * S.toPlaces T l * y⁻¹)
  choose σ hσ using ok.reduction_surjective
  have h_translate (g : S.ResidueGL) :
      ∫ y in K, φ (S.toPlaces T (σ g) * y) ∂F.groupMeasure = ∫ y in K, φ y ∂F.groupMeasure := by
    have h_mem : S.toPlaces T (σ g) ∈ K := (mem_latticeStabilizer_iff.mp (σ g).prop).2
    rw [← (measurePreserving_mul_left F.groupMeasure _).setIntegral_image_emb
      (measurableEmbedding_mulLeft _)]
    simp [Set.preimage, mul_mem_cancel_left, h_mem]
  have h_const (y : (S.latticeMiddle (LocProd T)).G) (hy : y ∈ K) :
      ∑ g : S.ResidueGL, φ (S.toPlaces T (σ g) * y) =
        Fintype.card S.ResidueGL * S.reducedCharMean (S.reduction l) := by
    obtain ⟨k, rfl, hk_off, -⟩ := S.exists_isIntegralOff_toPlaces_eq y
    lift k to S.latticeStabilizer using mem_latticeStabilizer_iff.2 ⟨hk_off, hy⟩
    rw [← S.reducedCharMean_conj (S.reduction k), reducedCharMean, Fintype.card_mul_expect]
    refine sum_congr rfl fun g _ ↦ ?_
    -- The integrand is `extendedBesselChar F.levelUnit` at the integral element
    -- `(σ g k) l (σ g k)⁻¹`.
    simpa [φ, hσ, mul_assoc] using
      S.extendedBesselChar_toPlaces_eq_reducedChar hF (σ g * k * l * (σ g * k)⁻¹)
  refine mul_left_cancel₀ (a := (Fintype.card S.ResidueGL : ℂ)) (by simp) ?_
  calc Fintype.card S.ResidueGL * ∫ y in K, φ y ∂F.groupMeasure
      = ∑ g : S.ResidueGL, ∫ y in K, φ (S.toPlaces T (σ g) * y) ∂F.groupMeasure := by
        simp only [h_translate, sum_const, card_univ, nsmul_eq_mul]
    _ = ∫ y in K, ∑ g : S.ResidueGL, φ (S.toPlaces T (σ g) * y) ∂F.groupMeasure :=
        (integral_finsetSum _ fun g _ ↦
          ContinuousOn.integrableOn_compact unitaryLevel_open_compact.2 (by fun_prop)).symm
    _ = Fintype.card S.ResidueGL * F.groupMeasure.real K • S.reducedCharMean (S.reduction l) := by
        rw [setIntegral_congr_fun measurableSet_unitaryLevel h_const, setIntegral_const,
          mul_smul_comm]

omit [WeilData E] ok in
/-- Let `S` be admissible filling data for a unitary group `G` over the CM field `E`, which carries
Weil data, and let `Ḡ = S.ResidueGL` be the product of the general linear groups over the residue
fields at the chosen places above the two level primes `p₀`, `p₁`. Let `M = p₀ p₁`, and let `T` be a
finite conjugation-stable set of finite places off which `M⁻¹` is integral, so that `T` contains the
places above `M`. Over the product `LocProd T` of the completions at `T`, let `K` be the group of
integral points of `G` and `K(M)` its principal congruence subgroup of level `M`. Let `F` be a
filling datum (`IsFillingData`): a large lattice datum with `3ϱ + 6` hyperbolic pairs and
`k - (6ϱ + 13)` orthonormal vectors, for the ranks `ϱ = 𝔰.ϱ` and `k = 𝔰.k` of the shape, with
modulus `F.levelUnit = M` and local character `ψ(x) = ψ_f(-x / ϖ)`, where `ϖ` generates the
different. The function `χ_M = extendedBesselChar F.levelUnit` is `ψ(τ(u) / M)` on `u K(M)` for `u`
in the block unitriangular group `𝖴 = besselU`, with `τ(u)` the sum of the entries at the simple
roots, and `0` off `𝖴 K(M)`. Suppose that `T` consists of chosen places and their conjugates, and
put `a z = ∫_K χ_M(y z y⁻¹) dy` for the measure `dy = F.groupMeasure`. For a finite family `σ` in
the stabilizer of the lattice whose members have different reductions in `Ḡ` we have
`∑ |a (σ s)|² ≤ 2 vol(K)²`, where `a` is evaluated at the component of `σ s` at `T`. -/
lemma sum_sq_norm_integral_extendedBesselChar_conjugate_le {T : Finset (FinPlace E)} [T.StarStable]
    [Fact (S.ideleM⁻¹.val ∈ integralOff T)] (hT : T ⊆ S.chosenPlacesAndConj)
    [hInt : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) {ι : Type*} [Fintype ι] {σ : ι → S.latticeStabilizer}
    (hσ : Function.Injective fun s : ι ↦ S.reduction (σ s)) :
    ∑ s : ι,
        ‖∫ y : (S.latticeMiddle (LocProd T)).G
            in unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram,
          extendedBesselChar F.levelUnit (y * S.toPlaces T (σ s) * y⁻¹) ∂F.groupMeasure‖ ^ 2 ≤
      2 * F.groupMeasure.real
        (unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram) ^ 2 := by
  set K : Subgroup (U (S.latticeMiddle (LocProd T)).splitGram) :=
    unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram
  let a (z : (S.latticeMiddle (LocProd T)).G) : ℂ := ∫ y in K,
    extendedBesselChar F.levelUnit (y * z * y⁻¹) ∂F.groupMeasure
  -- `a` is constant on the cosets `C s = σ(s) K(M)`: `K` normalises `K(M)`, and `χ_M` is right
  -- invariant under `K(M)`.
  let C (s : ι) : Set (U (S.latticeMiddle (LocProd T)).splitGram) :=
    ((S.toPlaces T (σ s))⁻¹ * ·) ⁻¹' F.congruenceSubgroup
  have hC_meas (s : ι) : MeasurableSet (C s) := measurable_const_mul _ measurableSet_unitaryLevel
  have ha_const (s : ι) : ∀ z ∈ C s, a z = a (S.toPlaces T (σ s)) := fun z hz ↦
    setIntegral_congr_fun measurableSet_unitaryLevel fun y hy ↦ by
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left] using
        extendedBesselChar_mul_of_mem_unitaryLevel (y := y * S.toPlaces T (σ s) * y⁻¹)
          (conj_mem_unitaryLevel hy hz)
  -- The cosets are disjoint, since the `σ s` have different reductions.
  have hC_disj : Pairwise (Function.onFun Disjoint C) := by
    intro s t hst
    refine Set.disjoint_left.mpr fun z hs ht ↦ hst <| hσ <| (hF.reduction_eq_iff _ _).2 ?_
    have h := mul_mem hs.out (inv_mem ht.out)
    rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at h
  -- The integral of `|a|²` over these cosets is at most `massIntegral K = ∫ |a|²`; bound this by
  -- `IsLargeLatticeData.massIntegral_le_main_add_error` with `Q = 2`, and by
  -- `2⁻¹ ^ n ≤ groupMeasure(K)`.
  have h_lintegral :
      (∑ s : ι, ‖a (S.toPlaces T (σ s))‖ₑ ^ 2) * F.groupMeasure F.congruenceSubgroup ≤
        2 * F.groupMeasure K ^ 2 * F.groupMeasure F.congruenceSubgroup := by
    have h_coset (s : ι) : ∫⁻ z in C s, ‖a z‖ₑ ^ 2 ∂F.groupMeasure =
        ‖a (S.toPlaces T (σ s))‖ₑ ^ 2 * F.groupMeasure F.congruenceSubgroup := by
      rw [setLIntegral_congr_fun (hC_meas s) fun z hz ↦ by rw [ha_const s z hz]]
      rw [setLIntegral_const, measure_preimage_mul]
    have h_rank : 𝔰.n + 2 * 10 ^ 9 * 𝔰.n ^ 4 ≤ 𝔰.k := by
      obtain ⟨h₁, h₂, h₃⟩ := S.pow_chain
      linarith [Nat.le_self_pow (n := 4) (by norm_num) 𝔰.n]
    calc (∑ s : ι, ‖a (S.toPlaces T (σ s))‖ₑ ^ 2) * F.groupMeasure F.congruenceSubgroup
        = ∑' s : ι, ∫⁻ z in C s, ‖a z‖ₑ ^ 2 ∂F.groupMeasure := by
          simp only [h_coset, sum_mul, tsum_fintype]
      _ = ∫⁻ z in ⋃ s, C s, ‖a z‖ₑ ^ 2 ∂F.groupMeasure := (lintegral_iUnion hC_meas hC_disj _).symm
      _ ≤ F.massIntegral K := setLIntegral_le_lintegral ..
      _ ≤ F.groupMeasure K * F.groupMeasure F.congruenceSubgroup * (F.groupMeasure K + 2⁻¹ ^ 𝔰.n) :=
          hF.massIntegral_le_main_add_error ⟨_, unitaryLevel_le_unitaryLevel_one, le_rfl⟩ le_rfl
            IsLargeLatticeData.modulus_le_half h_rank
      _ ≤ 2 * F.groupMeasure K ^ 2 * F.groupMeasure F.congruenceSubgroup := by
          grw [hF.inv_two_pow_le_groupMeasure (volume_integers_diff_intUnits_le hT)]
          exact le_of_eq (by ring)
  -- Pass to real numbers and cancel `groupMeasure(K(M)) > 0`.
  have h_pos : 0 < F.groupMeasure.real F.congruenceSubgroup :=
    toReal_pos ((unitaryLevel_open_compact.1 (g := F.levelUnit)).measure_ne_zero _ (by simp))
      (hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one)
  refine le_of_mul_le_mul_right ?_ h_pos
  simpa [toReal_sum, Measure.real] using
    toReal_mono (by simp [mul_eq_top, K, hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one])
      h_lintegral

omit ok [WeilData E] in
/-- Let `S` be filling data over the CM field `E`, with level primes `p₀`, `p₁` and, for each `p_i`,
a chosen set `S.chosenPlaces i` of places of norm `p_i`, such that the chosen places and their
conjugates have product `M = p₀ p₁`. If a finite set `T` of finite places contains all of these,
then the inverse of the finite idele `S.ideleM` of `M` is integral off `T`. -/
lemma inv_ideleM_mem_integralOff {T : Finset (FinPlace E)}
    (hT_mem : ∀ (i : Fin 2) (w : S.chosenPlaces i), w.val ∈ T ∧ star w.val ∈ T) :
    S.ideleM⁻¹.val ∈ integralOff T := by
  -- `M` divides the idempotent of the places off `T`, as it vanishes at the places of `T`.
  let r : Ô E := ⟨idem (↑T : Set (FinPlace E))ᶜ, idem_mem_Ô _⟩
  have h_vanish (i : Fin 2) (w : S.chosenPlaces i) :
      reduceAt w.val r = 0 ∧ reduceAt w.val (star r) = 0 := by
    grind [reduceAt_idem, star_idem, coe_star_Ô]
  have h_idem : S.ideleM⁻¹ • idem Tᶜ ∈ Ô E := by
    refine (S.inv_ideleM_smul_mem_iff r).2 ?_
    rintro ⟨⟨i, w⟩, _ | _⟩
    · rw [reduceAboveM_false, (h_vanish i w).1]
    · rw [reduceAboveM_true, RingHom.comp_apply, starRingEnd_apply, (h_vanish i w).2]
  exact (mem_integralOff T).2 (idem_mul_mem_Ô.1 (by rwa [mul_comm]))

omit ok in
/-- **The induced character.** Let `S` be admissible filling data for a unitary group `G` over the
CM field `E`, which carries Weil data, and let `Ḡ = S.ResidueGL` be the product of the general
linear groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`.
Let `ψ_U = S.reducedChar` be the additive character (`unipotentChar`) of the integral block
unitriangular elements of `G`, read on their reductions in `Ḡ` and extended by `0`, and let
`ψ_U^♮(s) = S.reducedCharMean s` be its mean over the conjugates of `s`. Then `∑ |ψ_U^♮(s)|² ≤ 2`,
the sum being over all `s` in `Ḡ`. -/
theorem sum_norm_reducedCharMean_sq_le [ok : S.IsAdmissible] :
    ∑ s : S.ResidueGL, ‖S.reducedCharMean s‖ ^ 2 ≤ 2 := by
  -- Work at the set `T` of the chosen places and their conjugates, with a lift `σ s` of each `s`.
  choose σ hσ using ok.reduction_surjective
  let T : Finset (FinPlace E) := S.chosenPlacesAndConj
  have : T.StarStable := by
    refine ⟨fun w hw ↦ ?_⟩
    obtain ⟨i, s, hs, rfl | rfl⟩ := mem_chosenPlacesAndConj.1 hw
    · exact mem_chosenPlacesAndConj.2 ⟨i, w, hs, .inr rfl⟩
    · exact mem_chosenPlacesAndConj.2 ⟨i, s, hs, .inl (star_star s)⟩
  have hT_mem (i : Fin 2) (w : S.chosenPlaces i) : w.val ∈ T ∧ star w.val ∈ T :=
    ⟨mem_chosenPlacesAndConj.2 ⟨i, w, w.prop, .inl rfl⟩,
      mem_chosenPlacesAndConj.2 ⟨i, w, w.prop, .inr rfl⟩⟩
  have : Fact (S.ideleM⁻¹.val ∈ integralOff T) := ⟨S.inv_ideleM_mem_integralOff hT_mem⟩
  -- The product of the completions at `T` has a large lattice datum `F` of modulus `M`.
  obtain ⟨hInt, F, hF⟩ := S.exists_isFillingData T
  set K : Subgroup (U (S.latticeMiddle (LocProd T)).splitGram) :=
    unitaryLevel hInt.integers 1 (S.latticeMiddle (LocProd T)).splitGram
  have hK_pos : 0 < F.groupMeasure.real K :=
    toReal_pos ((unitaryLevel_open_compact.1 (g := 1)).measure_ne_zero _ (by simp))
      (hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one)
  -- The integrals in `sum_sq_norm_integral_extendedBesselChar_conjugate_le` are the measure of `K`
  -- times `ψ_U^♮(s)`.
  have h_sq : F.groupMeasure.real K ^ 2 * ∑ s, ‖S.reducedCharMean s‖ ^ 2 ≤
      F.groupMeasure.real K ^ 2 * 2 := by
    have h_inj : Function.Injective fun s : S.ResidueGL ↦ S.reduction (σ s) := fun s t hst ↦ by
      simpa [hσ] using hst
    simpa only [S.integral_extendedBesselChar_conj_eq hF, hσ,
      norm_smul_of_nonneg measureReal_nonneg, mul_pow,
      ← mul_sum, mul_comm (2 : ℝ)] using S.sum_sq_norm_integral_extendedBesselChar_conjugate_le
        (T := T) subset_rfl hF h_inj
  exact le_of_mul_le_mul_left h_sq (pow_pos hK_pos 2)

attribute [local instance low] Fintype.ofFinite in
/-- **The trace.** Let `S` be admissible filling data for a unitary group `G` over the CM field `E`,
which carries Weil data, and let `Ḡ = S.ResidueGL` be the product of the general linear groups over
the residue fields at the chosen places above the two level primes `p₀`, `p₁`. Let
`r_ψ(s) = S.besselTranslate s` be the operator on the source `ℂ^(classes × Bessel coordinates)`
whose blocks are the complex conjugates of the normalised amplitude sums of the rational elements of
the Bessel subgroup `besselS`. Let `x` be a central idempotent of the group algebra of the factor of
`Ḡ` above `p_i`, made of matrices indexed by the basis `𝔰.BesselIndex` of the hermitian space, with
`Re x(1) ≤ b⁻⁸ / 2`. Then the trace of `r_ψ(x) = ∑ x(s) r_ψ(s)` has real part at most `b⁻⁴ D_X`. -/
lemma re_sum_coeff_mul_trace_besselTranslate_le {i : Fin 2}
    {x : MonoidAlgebra ℂ (∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val))}
    (hx : IsCentralProj x) (hx_small : (x.coeff 1).re ≤ (S.b ^ 8)⁻¹ / 2) :
    (∑ s : ∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val), x.coeff s *
        LinearMap.trace ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord))
          (S.besselTranslate (mulSingle i s))).re ≤
      (S.b ^ 4)⁻¹ * S.sourceDim := by
  -- The element `mulSingle i s` is `1` above the other prime, so the trace is `D_X ψ_U(s)`.
  have h_trace (s : ∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val)) :
      LinearMap.trace ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord))
        (S.besselTranslate (mulSingle i s)) = S.sourceDim * S.reducedChar (mulSingle i s) :=
    S.trace_besselTranslate_eq_mul_reducedChar (j := i + 1) (by simp)
  -- As `x` is a class function, `ψ_U` may be replaced by its mean over conjugates.
  have h_mean : ∑ s, x.coeff s * S.reducedChar (mulSingle i s) =
      ∑ s, x.coeff s * S.reducedCharMean (mulSingle i s) := by
    have h_conj (g : S.ResidueGL) : ∑ s, x.coeff s * S.reducedChar (g * mulSingle i s * g⁻¹) =
        ∑ s, x.coeff s * S.reducedChar (mulSingle i s) := by
      refine Fintype.sum_equiv (MulAut.conj (g i)) _ _ fun s ↦ ?_
      have h_single : g * mulSingle i s * g⁻¹ = mulSingle i (g i * s * (g i)⁻¹) :=
        Function.eq_update_iff.2 (by simp +contextual)
      rw [h_single, EquivLike.coe_coe, MulAut.conj_apply, hx.2]
    simp only [reducedCharMean, mul_expect, ← expect_sum_comm, h_conj, Fintype.expect_const]
  have h_sq : ∑ s, ‖S.reducedCharMean (mulSingle i s)‖ ^ 2 ≤ 2 := by
    refine .trans ?_ S.sum_norm_reducedCharMean_sq_le
    rw [← sum_image (f := fun s ↦ ‖S.reducedCharMean s‖ ^ 2) (mulSingle_injective i).injOn]
    exact sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
  -- Cauchy–Schwarz, with `∑ |x s|² = Re x(1) ≤ b⁻⁸ / 2` and `∑ |ψ_U^♮|² ≤ 2`.
  have h_bound : ‖∑ s, x.coeff s * S.reducedCharMean (mulSingle i s)‖ ≤ (S.b ^ 4)⁻¹ := by
    refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
    calc ‖∑ s, x.coeff s * S.reducedCharMean (mulSingle i s)‖ ^ 2
        ≤ (∑ s, ‖x.coeff s‖ * ‖S.reducedCharMean (mulSingle i s)‖) ^ 2 := by
          grw [norm_sum_le, norm_mul_le]
      _ ≤ (S.b ^ 8)⁻¹ / 2 * 2 := by
          grw [sum_mul_sq_le_sq_mul_sq, sum_norm_sq_coeff_of_isCentralProj hx, hx_small, h_sq]
      _ = (S.b ^ 4)⁻¹ ^ 2 := by ring
  calc (∑ s, x.coeff s * LinearMap.trace ℂ _ (S.besselTranslate (mulSingle i s))).re
      = (S.sourceDim * ∑ s, x.coeff s * S.reducedCharMean (mulSingle i s)).re := by
        simp only [← h_mean, h_trace, mul_left_comm (x.coeff _), mul_sum]
    _ ≤ S.sourceDim * ‖∑ s, x.coeff s * S.reducedCharMean (mulSingle i s)‖ := by
        grw [re_le_norm, norm_mul, norm_natCast]
    _ ≤ (S.b ^ 4)⁻¹ * S.sourceDim := by
        grw [h_bound, mul_comm]

end BesselTrace

/-! ## Good forms: one prime and both primes -/

section GoodForms

open Matrix Complex Module InnerProductSpace EuclideanSpace Finset Fintype

attribute [local instance low] Fintype.ofFinite

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} [ok : S.IsAdmissible]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ S.ResidueGL V} {P : EuclideanSpace ℂ (S.Classes × S.BesselCoord) →ₗ[ℂ] V}

open scoped Classical in
/-- **One prime.** Let `S` be admissible filling data (`Filling`, `IsAdmissible`) for a unitary
group `G` over the CM field `E`, which carries Weil data (a primitive `5040`-th root of unity and a
splitting character, see `WeilData`), and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. The
source is the Euclidean space with coordinates `(c, i)`, where `c` is a class (a double coset of the
definite unitary group `U(X₀)` for the level) and `i` is a coordinate of the Bessel function `W` at
the infinite places. Let `ρ` be a unitary representation of `Ḡ` on `V` and `P` a linear map from the
source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the
conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum,
over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral
of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Let `x` be a central
idempotent (an idempotent whose coefficients form a class function; it is then self-adjoint) of the
group algebra of the factor of `Ḡ` above `p_i`, made of matrices indexed by the basis
`𝔰.BesselIndex` of the hermitian space, with `Re x(1) ≤ b⁻⁸ / 2`, where `b = S.b ≥ 1000` is the size
parameter of `S`. Then `‖x P‖² ≤ 2 b⁻⁴ D_X` in Hilbert–Schmidt norm, where `x` acts on `V` through
`ρ` and `D_X = S.sourceDim` is the dimension of the source. -/
lemma HasAmplitudeBlocks.hilbertSchmidtNorm_asAlgebraHom_comp_sq_le [WeilData E]
    (hP : S.HasAmplitudeBlocks ρ P)
    (hρ : ∀ (s : S.ResidueGL) (v v' : V), ⟪ρ s v, ρ s v'⟫_ℂ = ⟪v, v'⟫_ℂ) (i : Fin 2)
    {x : MonoidAlgebra ℂ (∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val))}
    (hx : IsCentralProj x) (hx_small : (x.coeff 1).re ≤ (S.b ^ 8)⁻¹ / 2) :
    hilbertSchmidtNorm
        (Representation.asAlgebraHom (ρ.comp (MonoidHom.mulSingle
          (fun j : Fin 2 ↦ ∀ w : S.chosenPlaces j, GL 𝔰.BesselIndex (ResField w.val)) i)) x ∘ₗ
          P) ^ 2 ≤
      2 * (S.b ^ 4)⁻¹ * S.sourceDim := by
  have hb : 1000 ≤ S.b := S.thousand_le_b
  set e : End ℂ V := Representation.asAlgebraHom (ρ.comp (.mulSingle _ i)) x with he_def
  have he : e.IsSymmetricProjection :=
    hx.isSymmetricProjection (ρ := ρ.comp (.mulSingle _ i)) fun _ ↦ hρ _
  set P' : End ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) := ∑ t, x.coeff t •
    (P.adjoint ∘ₗ ρ (Pi.mulSingle i t) ∘ₗ P - S.besselTranslate (Pi.mulSingle i t)) with hP'
  -- `‖x P‖² = tr (P* x P) = tr r_ψ(x) + tr P'_x`, with `r_ψ(x) = ∑ x(t) r_ψ(t)`, `P'_x = P'`.
  have h_trace : hilbertSchmidtNorm (e ∘ₗ P) ^ 2 =
      (∑ t, x.coeff t * LinearMap.trace ℂ _ (S.besselTranslate (Pi.mulSingle i t))).re +
        (LinearMap.trace ℂ _ P').re := by
    have h_proj : (e ∘ₗ P).adjoint ∘ₗ e ∘ₗ P = P.adjoint ∘ₗ e ∘ₗ P := by
      rw [LinearMap.adjoint_comp, he.isSymmetric.adjoint_eq, LinearMap.comp_assoc,
        ← LinearMap.comp_assoc P e e, ← End.mul_eq_comp, he.isIdempotentElem.eq]
    have h_sum : P.adjoint ∘ₗ e ∘ₗ P =
        ∑ t, x.coeff t • (P.adjoint ∘ₗ ρ (Pi.mulSingle i t) ∘ₗ P) := by
      ext1 v
      simp [he_def, Representation.asAlgebraHom_eq_sum]
    rw [← ofReal_re (_ ^ 2), hilbertSchmidtNorm_sq_eq_trace, h_proj, h_sum, ← add_re, hP']
    simp [mul_sub]
  have h_bessel :
      (∑ t, x.coeff t * LinearMap.trace ℂ _ (S.besselTranslate (Pi.mulSingle i t))).re ≤
        (S.b ^ 4)⁻¹ * S.sourceDim :=
    S.re_sum_coeff_mul_trace_besselTranslate_le hx hx_small
  -- `|tr P'_x| ≤ ‖1‖ ‖P'_x‖`
  have h_rest : (LinearMap.trace ℂ _ P').re ≤ (S.b ^ 4)⁻¹ * S.sourceDim := by
    have h_inner : LinearMap.trace ℂ _ P' = ⟪hilbertSchmidtVector 1,
      hilbertSchmidtVector P'⟫_ℂ := by
      rw [inner_hilbertSchmidtVector, End.one_eq_id, LinearMap.adjoint_id, LinearMap.id_comp]
    rw [h_inner]
    refine (re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    refine le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity) ?_
    calc
      _ = S.sourceDim * hilbertSchmidtNorm P' ^ 2 := by
        rw [mul_pow, ← hilbertSchmidtNorm_one_sq_eq_sourceDim, hilbertSchmidtNorm,
          hilbertSchmidtNorm]
      _ ≤ S.sourceDim * (S.sourceDim / S.b ^ 12) := by
        grw [hP.hilbertSchmidtNorm_sum_smul_sub_besselTranslate_sq_le hρ i hx]
      _ ≤ S.sourceDim * (S.sourceDim / S.b ^ 8) := by gcongr <;> linarith
      _ = ((S.b ^ 4)⁻¹ * S.sourceDim) ^ 2 := by ring
  linarith

variable {g : ∀ i : Fin 2,
  MonoidAlgebra ℂ (∀ w : S.chosenPlaces i, GL 𝔰.BesselIndex (ResField w.val))}

omit ok [FiniteDimensional ℂ V] in
/-- The source has dimension `D_X = S.sourceDim`. -/
lemma finrank_source_eq_sourceDim :
    (finrank ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) : ℝ) = S.sourceDim := by
  simp [sourceDim]

/-- **Both primes.** Let `S` be admissible filling data (`Filling`, `IsAdmissible`) for a unitary
group `G` over the CM field `E`, which carries Weil data (a primitive `5040`-th root of unity and a
splitting character, see `WeilData`), and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. The
source is the Euclidean space with coordinates `(c, i)`, where `c` is a class (a double coset of the
definite unitary group `U(X₀)` for the level) and `i` is a coordinate of the Bessel function `W` at
the infinite places. Let `ρ` be a unitary representation of `Ḡ` on `V` and `P` a linear map from the
source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the
conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum,
over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral
of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Let `g_i` be a central
idempotent (an idempotent whose coefficients form a class function; it is then self-adjoint) of the
group algebra of the factor of `Ḡ` above `p_i`, such that the coefficient of `1 - g_i` at `1` has
real part at most `b⁻⁸ / 2`, where `b = S.b ≥ 1000` is the size parameter of `S`. Let
`e₀ = piTensorElem g` be the tensor product `g₀ ⊗ g₁` in `ℂ[Ḡ]`, acting on `V` through `ρ`. Then
`‖(1 - e₀) P‖² ≤ 4 b⁻⁴ D_X` in Hilbert–Schmidt norm, where `D_X = S.sourceDim` is the dimension of
the source. -/
theorem HasAmplitudeBlocks.hilbertSchmidtNorm_one_sub_piTensorElem_comp_sq_le [WeilData E]
    (hP : S.HasAmplitudeBlocks ρ P) (hρ : ∀ (s : S.ResidueGL) (x y : V), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x,
      y⟫_ℂ)
    (hg : ∀ i : Fin 2, IsCentralProj (g i))
    (hg_small : ∀ i : Fin 2, ((1 - g i).coeff 1).re ≤ (S.b ^ 8)⁻¹ / 2) :
    hilbertSchmidtNorm ((1 - ρ.asAlgebraHom (piTensorElem g)) ∘ₗ P) ^ 2 ≤
      4 * (S.b ^ 4)⁻¹ * S.sourceDim := by
  let e (i : Fin 2) : End ℂ V := Representation.asAlgebraHom (ρ.comp (.mulSingle _ i)) (g i)
  have h_factor : ρ.asAlgebraHom (piTensorElem g) = e 0 * e 1 := by
    have h_split : g = Pi.mulSingle 0 (g 0) * Pi.mulSingle 1 (g 1) := by
      ext i : 1
      fin_cases i <;> simp
    rw [h_split, map_mul, map_mul, asAlgebraHom_piTensorElem_mulSingle,
      asAlgebraHom_piTensorElem_mulSingle]
  have h_proj : (e 0).IsSymmetricProjection :=
    (hg 0).isSymmetricProjection (ρ := ρ.comp (.mulSingle _ 0)) fun _ ↦ hρ _
  have h_prime (i : Fin 2) : hilbertSchmidtNorm ((1 - e i) ∘ₗ P) ^ 2 ≤ 2 * (S.b ^ 4)⁻¹ *
    S.sourceDim := by
    simpa [e] using hP.hilbertSchmidtNorm_asAlgebraHom_comp_sq_le hρ i (hg i).one_sub (hg_small i)
  rw [h_factor]
  calc hilbertSchmidtNorm ((1 - e 0 * e 1) ∘ₗ P) ^ 2
      ≤ hilbertSchmidtNorm ((1 - e 0) ∘ₗ P) ^ 2 + hilbertSchmidtNorm ((1 - e 1) ∘ₗ P) ^ 2 :=
        hilbertSchmidtNorm_one_sub_mul_comp_sq_le h_proj (e 1) P
    _ ≤ 4 * (S.b ^ 4)⁻¹ * S.sourceDim := by linarith [h_prime 0, h_prime 1]

/-- **Good forms.** Let `S` be admissible filling data (`Filling`, `IsAdmissible`) for a unitary
group `G` over the CM field `E`, which carries Weil data (a primitive `5040`-th root of unity and a
splitting character, see `WeilData`), and let `Ḡ = S.ResidueGL` be the product of the general linear
groups over the residue fields at the chosen places above the two level primes `p₀`, `p₁`. The
source is the Euclidean space with coordinates `(c, i)`, where `c` is a class (a double coset of the
definite unitary group `U(X₀)` for the level) and `i` is a coordinate of the Bessel function `W` at
the infinite places. Let `ρ` be a unitary representation of `Ḡ` on `V` and `P` a linear map from the
source to `V`. Suppose `HasAmplitudeBlocks`: the block `(c, c')` of `P_s = P* ρ(s) P` is the
conjugate of `A(c, s, c') / ν`, where `ν = S.unipotentCovolume > 0` and `A(c, s, c')` is the sum,
over the rational `γ` in `G` such that `h_c⁻¹ γ h_c'` is integral with reduction `s`, of an integral
of `W(y) ⊗ W(γ⁻¹ y)^*` against cutoffs (`h_c` represents the class `c`). Let `g_i` be a central
idempotent (an idempotent whose coefficients form a class function; it is then self-adjoint) of the
group algebra of the factor of `Ḡ` above `p_i`, such that the coefficient of `1 - g_i` at `1` has
real part at most `b⁻⁸ / 2`, where `b = S.b ≥ 1000` is the size parameter of `S`. Let
`e₀ = piTensorElem g` be the tensor product `g₀ ⊗ g₁` in `ℂ[Ḡ]`, acting on `V` through `ρ`. Then
`e₀ P` is almost an isometry from below in mean square (`IsNearIsometry`) with error `5 b⁻⁴`:
`‖e₀ P pr_U‖² ≥ dim U - 5 b⁻⁴ D_X` in Hilbert–Schmidt norm for every subspace `U` of the source,
where `pr_U` is the orthogonal projection onto `U` and `D_X` is the dimension of the source. -/
theorem HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp [WeilData E]
    (hP : S.HasAmplitudeBlocks ρ P)
    (hρ : ∀ (s : S.ResidueGL) (x y : V), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hg : ∀ i : Fin 2, IsCentralProj (g i))
    (hg_small : ∀ i : Fin 2, ((1 - g i).coeff 1).re ≤ (S.b ^ 8)⁻¹ / 2) :
    IsNearIsometry (ρ.asAlgebraHom (piTensorElem g) ∘ₗ P) (5 * (S.b ^ 4)⁻¹) := by
  have hb : 1000 ≤ S.b := S.thousand_le_b
  -- `P` itself is almost an isometry, as `‖P* P - 1‖² ≤ b⁻¹² D_X`.
  have h_isom : IsNearIsometry P (S.b ^ 4)⁻¹ := by
    refine isNearIsometry_of_hilbertSchmidtNorm_le (by positivity)
      (hP.hilbertSchmidtNorm_sub_one_sq_le.trans ?_)
    rw [finrank_source_eq_sourceDim, inv_pow, ← pow_mul, ← div_eq_inv_mul]
    gcongr <;> linarith
  have h_bad : hilbertSchmidtNorm ((1 - ρ.asAlgebraHom (piTensorElem g)) ∘ₗ P) ^ 2 ≤
      4 * (S.b ^ 4)⁻¹ * finrank ℂ (EuclideanSpace ℂ (S.Classes × S.BesselCoord)) := by
    simpa only [finrank_source_eq_sourceDim] using
      hP.hilbertSchmidtNorm_one_sub_piTensorElem_comp_sq_le hρ hg hg_small
  have h_proj : (ρ.asAlgebraHom (piTensorElem g)).IsSymmetricProjection :=
    (IsCentralProj.piTensorElem hg).isSymmetricProjection hρ
  exact (h_isom.proj_comp h_proj h_bad).mono (le_of_eq (by ring))

end GoodForms

end New.Filling
