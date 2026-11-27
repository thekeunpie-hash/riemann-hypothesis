module

import Mathlib.Algebra.Order.Star.Real
public import New.Spanning.RemainingTerms.FrameParts
import New.Spanning.Unfolding.ReducedPoints
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.RingTheory.PicardGroup
public import Lib.General.LinearAlgebra.PartnerAlgebra
public import New.Spanning.RemainingTerms.Data
import Lib.Adelic.Reduction.DefiniteClassSums
public import New.Spanning.Unfolding.Climbing
import Mathlib.Algebra.Order.Star.Int
import New.Spanning.RemainingTerms.Gain
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
public import New.Spanning.RemainingTerms.Size

section
section
/-!
# Counting frames over a lattice of small discriminant

Modulo moves, few frames of near terms have a lattice `L_γ^M` that contains a given lattice `L` of
small discriminant (`New.Filling.IsFrameSet.encard_le`, and for the terms of one label
`New.Filling.encard_setOf_isNearTermAt_and_le_termLattice_le`). After the cell rank and the matrix
of products are fixed, the frames are sorted in three rounds: by the lift of `L`, by the part in
`X₀`, and by the part in the isotropic space.

Notions from other files:

* `New.frameImage γ`: the frame `γ f` of `γ`, the image of the standard frame
  `f = (e₁, …, e_ϱ, z)` of `n = ϱ + 1` vectors; `S.frameProducts γ` is the matrix of products of
  `f` with `γ f`.
* `S.classUnipotent₀ c`: the group of moves for the class `c`.
* `S.HasCellRank j γ`: the element `γ` has cell rank `j ≤ ϱ + 1`: from the index `j` on, the flags
  of `f` and `γ f` share vectors whose two leading coefficients have the same norm, and the leading
  minor of order `j` of the matrix of products is nonzero; a further condition singles out
  `j = ϱ + 1`.
* `S.sharedVectors j γ`: the matrix whose columns `k ≥ j` are the coordinates in the isotropic
  space of the columns of `γ f · adj Y`, the others being `0`. Here `Y` consists of the first `j`
  rows of the matrix of products completed by rows of `1`; for `γ` of cell rank `j` these columns
  lie in the spans of both frames.
* `S.termLattice c c' γ`: the lattice `L_γ^M` of the `v ∈ Λ ∩ X₀` such that some vector of
  `v + M (Λ ∩ X)` is orthogonal to `γ f`, where `Λ` is the lattice of `c` and `X` is the isotropic
  space spanned by `e₁, …, e_ϱ`.
* `New.genIndex d`: the generalised index of an idele `d`, the inverse of the factor by which `d`
  scales Haar measure.
-/

@[expose] public section

namespace New.Filling

open NumberField Matrix Module Fintype ENNReal Pointwise

/-- Colour the elements of `A` by `φ` with at most `N` colours, so that elements of one colour are
related by `R`. If every nonempty set of pairwise related elements of `A` has at most `x` elements,
then `A` has at most `N * x` elements. -/
lemma encard_le_of_encard_range_le {α β : Type} {A : Set α} {R : α → α → Prop} {N x : ℝ≥0∞}
    (φ : A → β) (h_colours : (Set.range φ).encard ≤ N) (h_rel : ∀ a b : A, φ a = φ b → R a b)
    (h_class : ∀ B : Set α, B ⊆ A → ∀ a₀ ∈ B, (∀ a ∈ B, ∀ b ∈ B, R a b) → B.encard ≤ x) :
    A.encard ≤ N * x := by
  rw [← ENNReal.tsum_set_one]
  refine tsum_le_of_encard_range_le (w := fun _ ↦ 1) φ h_colours h_rel fun B hB a ha h_pairs ↦ ?_
  rw [ENNReal.tsum_set_one]
  exact h_class B hB a ha h_pairs

/-- Let `E` be a CM field with a primitive 5040-th root of unity. Let `K` and `K'` be modules of
vectors of finite adeles over the ring `Ô E` of integral finite adeles, with `K ∩ K'` of finite
index in `K'`. Attach to each element of `A` a family `f a`, indexed by `ι`, of vectors of `K'`. If
every nonempty subset of `A` whose families are congruent modulo `K` has at most `x` elements, then
`A` has at most `[K' : K ∩ K'] ^ card ι * x` elements. -/
lemma encard_le_of_colouring {E : Type} [Field E] [CMType E]
    {α ι σ : Type} [Fintype ι] {A : Set α} (f : α → ι → σ → 𝔸f E)
    {K K' : Submodule (Ô E) (σ → 𝔸f E)} (h_index : submoduleIndex K K' ≠ 0)
    (hf : ∀ a ∈ A, ∀ i : ι, f a i ∈ K') {x : ℝ≥0∞}
    (h_class : ∀ B : Set α, B ⊆ A → ∀ a₀ ∈ B,
      (∀ a ∈ B, ∀ b ∈ B, ∀ i : ι, f a i - f b i ∈ K) → B.encard ≤ x) :
    A.encard ≤ ENNReal.ofReal (submoduleIndex K K' ^ card ι) * x := by
  rw [← ENNReal.tsum_set_one]
  refine tsum_le_relIndex_pow_mul f h_index hf (fun _ ↦ 1) x fun B hB a ha h_pairs ↦ ?_
  rw [ENNReal.tsum_set_one]
  exact h_class B hB a ha h_pairs

/-- For `b ≥ 3` we have `1 + 2 b ^ m ≤ b ^ m'` whenever `m < m'`. -/
private lemma one_add_two_mul_pow_le_pow {b : ℝ} (hb : 3 ≤ b) {m m' : ℕ} (h_lt : m < m') :
    1 + 2 * b ^ m ≤ b ^ m' := by
  calc 1 + 2 * b ^ m ≤ b ^ (m + 1) := by
        nlinarith [pow_succ b m, one_le_pow₀ (a := b) (n := m) (by linarith)]
    _ ≤ b ^ m' := pow_le_pow_right₀ (by linarith) h_lt

section FrameSets

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

section Moves

variable {c : S.Classes} {u γ : S.G E}

/-- A move fixes the standard frame. -/
private lemma mem_besselU0_of_mem_classUnipotent₀ (hu : u ∈ S.classUnipotent₀ c) : u ∈ besselU0 :=
  (Subgroup.mem_inf.1 hu).2

/-- A move for the class `c` keeps the set of terms over `(c, s, c')`. -/
private lemma mul_mem_termsOver_of_mem_classUnipotent₀ (hu : u ∈ S.classUnipotent₀ c)
    {s : S.ResidueGL}
    {c' : S.Classes} (hγ : γ ∈ S.termsOver c s c') : u * γ ∈ S.termsOver c s c' := by
  -- That `h_c⁻¹ u h_c` lies in the principal level says that `u` is a term over `(c, 1, c)`.
  have h_over : u ∈ S.termsOver c 1 c := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hu).1).2
  simpa using termsOver.mul h_over hγ

/-- A move keeps the cell rank of an element. -/
private lemma HasCellRank.mul_of_mem_classUnipotent₀ {j : Fin (𝔰.ϱ + 2)}
    (h_cellRank : S.HasCellRank j γ) (hu : u ∈ S.classUnipotent₀ c) :
    S.HasCellRank j (u * γ) := by
  have h_stable : S.HasCellRank j (u⁻¹⁻¹ * γ * 1) ↔ S.HasCellRank j γ :=
    isStable_hasCellRank j u⁻¹ (inv_mem (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hu).1).1) 1
      (one_mem _) γ
  simpa [h_cellRank] using h_stable

end Moves

variable (S) in
/-- A frame set for the class `c`: a set of near terms `(c', γ)` over blocks `(c, s, c')`, for any
`s`, whose frames are different modulo moves, the elements of the unipotent group of level `M`
that fix the standard frame. -/
structure IsFrameSet (c : S.Classes) (B : Set (S.Classes × S.G E)) : Prop where
  /-- The terms are near. -/
  near : ∀ p ∈ B, S.IsNear p.2
  /-- The terms lie over blocks with the first class `c`. -/
  mem_termsOver : ∀ p ∈ B, ∃ s : S.ResidueGL, p.2 ∈ S.termsOver c s p.1
  /-- Terms whose frames agree after moves are equal. -/
  separated : ∀ p ∈ B, ∀ q ∈ B, ∀ u ∈ S.classUnipotent₀ c, ∀ u' ∈ S.classUnipotent₀ c,
    frameImage (u * p.2).val.val = frameImage (u' * q.2).val.val → p = q

/-- A subset of a frame set is a frame set. -/
lemma IsFrameSet.mono {c : S.Classes} {B : Set (S.Classes × S.G E)} (hB : S.IsFrameSet c B)
    {D : Set (S.Classes × S.G E)} (hD : D ⊆ B) : S.IsFrameSet c D where
  near p hp := hB.near p (hD hp)
  mem_termsOver p hp := hB.mem_termsOver p (hD hp)
  separated p hp q hq := hB.separated p (hD hp) q (hD hq)

variable [S.IsAdmissible] {c : S.Classes} {B : Set (S.Classes × S.G E)}

omit [S.IsAdmissible] in
/-- The matrix of products of the standard frame with the frame of a term of a frame set has
integral entries. -/
lemma IsFrameSet.isIntegral_frameProducts (hB : S.IsFrameSet c B) {p : S.Classes × S.G E}
    (hp : p ∈ B) (a b : Fin (𝔰.ϱ + 1)) : IsIntegral ℤ (S.frameProducts p.2 a b) := by
  obtain ⟨_, h_over⟩ := hB.mem_termsOver p hp
  exact Filling.isIntegral_frameProducts h_over a b

/-- Let `E` be a CM field, `S` admissible filling data over `E`, and `c` a class. Let `B` be a frame
set for `c`: near terms over blocks with the first class `c`, whose frames differ modulo moves, the
unipotent elements of level `M` that fix the standard frame. The terms of `B` have at most
`b ^ (270 n³ f)` matrices of products of the standard frame with their frame. Here `b = S.b` is the
size parameter of `S`, `n` is the length of the frame and `f` the number of infinite places. -/
lemma IsFrameSet.encard_range_frameProducts_le (hB : S.IsFrameSet c B) :
    (Set.range fun p : B ↦ S.frameProducts p.val.2).encard ≤
      ENNReal.ofReal (S.b ^ (270 * 𝔰.n ^ 3 * numInfPlaces E)) := by
  -- The entries are integral and bounded at every infinite place.
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have h_packing : (Set.range fun p : B ↦ S.frameProducts p.val.2).encard ≤ ENNReal.ofReal
      ((1 + 2 * S.b ^ (134 * 𝔰.n)) ^ (card (Fin 𝔰.n × Fin 𝔰.n) * numInfPlaces E * 2)) := by
    refine encard_le_of_isIntegral_norm_le Function.uncurry (by positivity) ?_
      Function.uncurry_injective.injOn
    rintro _ ⟨⟨p, hp⟩, rfl⟩ ⟨a, b⟩
    exact ⟨hB.isIntegral_frameProducts hp a b,
      fun v ↦ (hB.near p hp).norm_frameProducts_le v a b⟩
  have h_radius : 1 + 2 * S.b ^ (134 * 𝔰.n) ≤ S.b ^ (135 * 𝔰.n) :=
    one_add_two_mul_pow_le_pow (by linarith) (by lia)
  grw [h_packing, h_radius, ← pow_mul, card_prod, Fintype.card_fin]
  exact le_of_eq (by ring_nf)

omit [S.IsAdmissible] in
/-- There are `ϱ + 2` cell ranks, and `ϱ + 2 ≤ b ^ (2 f)` with `f` the number of infinite places. -/
private lemma varrho_add_two_le_b_pow : ((𝔰.ϱ + 2 : ℕ) : ℝ) ≤ S.b ^ (2 * numInfPlaces E) :=
  calc ((𝔰.ϱ + 2 : ℕ) : ℝ) ≤ S.b ^ 2 := by
        have h_succ : ((𝔰.ϱ + 1 : ℕ) : ℝ) ≤ S.b := S.succ_le_b
        push_cast at h_succ ⊢
        nlinarith [S.thousand_le_b]
    _ ≤ S.b ^ (2 * numInfPlaces E) :=
      pow_le_pow_right₀ S.one_le_b (Nat.le_mul_of_pos_right 2 Fintype.card_pos)

end FrameSets

variable {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {𝔰 : Shape} {S : Filling E 𝔰}
  [S.IsAdmissible]

section Rounds

variable {j : Fin (𝔰.ϱ + 2)} {c : S.Classes} {B : Set (S.Classes × S.G E)}
  {Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E} {r l : ℕ} {y : Matrix 𝔰.κ (Fin r) E}

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible] in
/-- Let `γ` be a term over the block `(c, s, c')`: a rational element such that `h_c⁻¹ γ h_c'`, for
the representatives of the classes `c` and `c'`, is integral with reduction `s`. The entries of its
matrix of shared vectors for the index `j` are algebraic integers. -/
lemma isIntegral_sharedVectors {γ : S.G E} {s : S.ResidueGL} {c' : S.Classes}
    (h_over : γ ∈ S.termsOver c s c') (a : Fin 𝔰.ϱ) (k : Fin (𝔰.ϱ + 1)) :
    IsIntegral ℤ (S.sharedVectors j γ a k) := by
  let O : Subring E := (Ô E).comap (algebraMap E (𝔸f E))
  have hY : IsIntMatrix O (paddedLeading j (S.frameProducts γ)) :=
    isIntMatrix_paddedLeading (isIntegral_frameProducts h_over)
  have h_frame : IsIntMatrix O (frameImage γ.val.val).toRows₁ := by
    intro i b
    have h_entry : frameImage (S.translateByClassReps c c' γ).val.val (.inl i) b ∈ Ô E :=
      termsOver.isIntMatrix_translateByClassReps h_over (.inl i) (𝔰.besselFrame b)
    -- The change to the lattice basis keeps the coordinates in the isotropic space.
    rw [frameImage_translateByClassReps, classCoord_eq_fromBlocks] at h_entry
    simpa [O, Matrix.mul_apply, Matrix.one_apply] using h_entry
  rw [sharedVectors, of_apply]
  split_ifs
  · exact algebraMap_mem_Ô.1 (h_frame.mul hY.adjugate a k)
  · exact isIntegral_zero

omit [HasPrimitiveRoot5040 E] in
/-- Let `B` be a frame set whose terms all have cell rank `j`: from the index `j` on, the flags of
the standard frame `f` and of the frame `γ f` share vectors, and the leading minor of order `j` of
their matrix of products is nonzero. Then there are at most `b ^ (366 n⁴ f')` matrices
`S.sharedVectors j γ`. Here `b = S.b` is the size parameter of `S`, `n = ϱ + 1` the length of the
frame and `f'` the number of infinite places. -/
lemma IsFrameSet.encard_range_sharedVectors_le (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, S.HasCellRank j p.2) :
    (Set.range fun p : B ↦ S.sharedVectors j p.val.2).encard ≤
      ENNReal.ofReal (S.b ^ (366 * 𝔰.n ^ 4 * numInfPlaces E)) := by
  -- The entries are integral and bounded at every infinite place.
  have hb : 1000 ≤ S.b := S.thousand_le_b
  refine (encard_le_of_isIntegral_norm_le Function.uncurry
    (by positivity : 0 ≤ S.b ^ (182 * 𝔰.n ^ 2)) ?_
    Function.uncurry_injective.injOn).trans (ofReal_le_ofReal ?_)
  · rintro _ ⟨⟨p, hp⟩, rfl⟩ ⟨a, k⟩
    obtain ⟨s, h_over⟩ := hB.mem_termsOver p hp
    exact ⟨isIntegral_sharedVectors h_over a k,
      fun v ↦ (h_cellRank p hp).norm_sharedVectors_le (hB.near p hp) v a k⟩
  · grw [one_add_two_mul_pow_le_pow (m' := 183 * 𝔰.n ^ 2) (by linarith) (by lia), ← pow_mul,
      card_prod, Fintype.card_fin, Fintype.card_fin]
    exact pow_le_pow_right₀ (by linarith) (by lia)

omit [S.IsAdmissible] in
/-- Let `γ` and `γ'` have the same integral matrix of products `Z` with nonzero leading minor of
order `j`, the same shared vectors and the same part in the anisotropic space `X₀`. Let `c`, `c'`,
`c''` be any three classes, with representatives `h_c`, `h_c'`, `h_c''`. If the first `ϱ` rows of
the frames of `h_c⁻¹ γ h_c'` and `h_c⁻¹ γ' h_c''` are congruent modulo `d = S.frameModulus j Z`,
then some `u ∈ S.classUnipotent₀ c`, a move for `c`, carries the frame of `γ` to the frame of
`γ'`. -/
private lemma exists_frameImage_mul_eq_of_sub_mem {γ γ' : S.G E} {c' c'' : S.Classes}
    (hγ : S.frameProducts γ = Z) (hγ' : S.frameProducts γ' = Z)
    (hZ_int : ∀ a b : Fin (𝔰.ϱ + 1), IsIntegral ℤ (Z a b)) (h_minor : leadingMinor Z j ≠ 0)
    (h_shared : S.sharedVectors j γ' = S.sharedVectors j γ)
    (h_part : framePartX₀ γ' = framePartX₀ γ)
    {d : (𝔸f E)ˣ} (hd : d.val = ((S.frameModulus j Z : E) : 𝔸f E))
    (h_congr : ∀ i : Fin 𝔰.ϱ, (frameImage (S.translateByClassReps c c'' γ').val.val).toRows₁ i -
      (frameImage (S.translateByClassReps c c' γ).val.val).toRows₁ i ∈ d • intVectors (Ô E)
        (Fin 𝔰.n)) :
    ∃ u ∈ S.classUnipotent₀ c, frameImage (u * γ).val.val = frameImage γ'.val.val := by
  subst hγ
  have hd_ne : S.frameModulus j (S.frameProducts γ) ≠ 0 := frameModulus_ne_zero h_minor
  let ξ : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.n) E := (frameImage γ'.val.val - frameImage γ.val.val).toRows₁
  -- The change to the lattice basis keeps the coordinates in the isotropic space.
  have h_diff : (frameImage (S.translateByClassReps c c'' γ').val.val).toRows₁ -
      (frameImage (S.translateByClassReps c c' γ).val.val).toRows₁ = finAdeleMatrix ξ := by
    simp [ξ, frameImage_translateByClassReps, classCoord_eq_fromBlocks, ← ext_iff, Matrix.mul_apply,
      Matrix.one_apply]
  have hξ : IsIntMatrix ((Ô E).comap (algebraMap E (𝔸f E)))
      ((S.frameModulus j (S.frameProducts γ))⁻¹ • ξ) := by
    intro i a
    obtain ⟨v, hv, h_row⟩ : ∃ v ∈ intVectors (Ô E) (Fin 𝔰.n), d.val • v = finAdeleMatrix ξ i := by
      rw [← h_diff]
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (h_congr i)
    have h_entry : (S.frameModulus j (S.frameProducts γ) : 𝔸f E) * v a = ξ i a := by
      simpa [← hd] using congrFun h_row a
    have h_quotient : algebraMap E (𝔸f E)
        (((S.frameModulus j (S.frameProducts γ))⁻¹ • ξ) i a) = v a := by
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, ← h_entry, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hd_ne, map_one, one_mul]
    rw [Subring.mem_comap, h_quotient]
    exact hv a
  exact exists_mem_classUnipotent₀_frameImage_mul_eq c hγ' hZ_int h_minor h_shared
    (apply_inr_besselFrame_eq hγ' h_part) hξ (smul_inv_smul₀ hd_ne ξ).symm

omit [S.IsAdmissible] in
/-- Let `E` be a CM field with a primitive 5040-th root of unity and `S` admissible filling data
over `E`. Take near terms of cell rank `j` (from the index `j` on, the flags of the standard frame
and of the frame of the term share vectors, and the leading minor of order `j` of their matrix of
products is nonzero), with frames different modulo moves and one matrix of products `Z`. Let `Y` be
the first `j` rows of `Z` completed by rows of `1`. Suppose that the terms have the same matrix of
shared vectors (the coordinates in the isotropic space of the columns `k ≥ j` of `γ f · adj Y`,
which lie in the spans of both frames) and that their frames have one part in the anisotropic space
`X₀` after the moves `u`, unipotent elements of level `M` that fix the standard frame. Let
`d = M det (Y Yᴴ)`. Then there are at most `[d] ^ (n ϱ)` terms, where `[d]` is the generalised
index and `n = ϱ + 1`. -/
lemma IsFrameSet.encard_le_of_sharedVectors_eq (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, S.HasCellRank j p.2) (hZ : ∀ p ∈ B, S.frameProducts p.2 = Z)
    (h_shared : ∀ p ∈ B, ∀ q ∈ B, S.sharedVectors j p.2 = S.sharedVectors j q.2)
    {u : S.Classes × S.G E → S.G E} (hu : ∀ p ∈ B, u p ∈ S.classUnipotent₀ c)
    (h_part : ∀ p ∈ B, ∀ q ∈ B, framePartX₀ (u p * p.2) = framePartX₀ (u q * q.2))
    {d : (𝔸f E)ˣ} (hd : d.val = ((S.frameModulus j Z : E) : 𝔸f E)) :
    B.encard ≤ ENNReal.ofReal ((genIndex d.val ^ 𝔰.n) ^ 𝔰.ϱ) := by
  -- A term is determined by the first `ϱ` rows of its moved frame modulo `d`.
  obtain rfl | ⟨p₁, hp₁⟩ := B.eq_empty_or_nonempty
  · simp
  obtain rfl : S.frameProducts p₁.2 = Z := hZ p₁ hp₁
  have hZ_int (a b : Fin (𝔰.ϱ + 1)) : IsIntegral ℤ (S.frameProducts p₁.2 a b) :=
    hB.isIntegral_frameProducts hp₁ a b
  have h_fix (p : S.Classes × S.G E) (hp : p ∈ B) : u p ∈ besselU0 :=
    mem_besselU0_of_mem_classUnipotent₀ (hu p hp)
  have hZ_moved (p : S.Classes × S.G E) (hp : p ∈ B) :
      S.frameProducts (u p * p.2) = S.frameProducts p₁.2 :=
    (frameProducts_mul_of_mem_besselU0 (h_fix p hp) p.2).trans (hZ p hp)
  have hd_int : d.val ∈ Ô E := by simpa only [hd] using
                                    frameModulus_mem_integralAdeles_of_isIntegral hZ_int
  let block (p : S.Classes × S.G E) : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.n) (𝔸f E) :=
    (frameImage (S.translateByClassReps c p.1 (u p * p.2)).val.val).toRows₁
  have h_block_int (p : S.Classes × S.G E) (hp : p ∈ B) (i : Fin 𝔰.ϱ) :
      block p i ∈ intVectors (Ô E) (Fin 𝔰.n) := by
    obtain ⟨_, h_over⟩ := hB.mem_termsOver p hp
    exact fun a ↦ termsOver.isIntMatrix_translateByClassReps
      (mul_mem_termsOver_of_mem_classUnipotent₀ (hu p hp) h_over) (.inl i) (𝔰.besselFrame a)
  have h_unique (p : S.Classes × S.G E) (hp : p ∈ B) (q : S.Classes × S.G E) (hq : q ∈ B)
      (h_congr : ∀ i : Fin 𝔰.ϱ, block q i - block p i ∈ d • intVectors (Ô E) (Fin 𝔰.n)) :
      p = q := by
    have h_shared_moved : S.sharedVectors j (u q * q.2) = S.sharedVectors j (u p * p.2) := by
      rw [(h_cellRank q hq).sharedVectors_mul_of_mem_besselU0 (h_fix q hq),
        (h_cellRank p hp).sharedVectors_mul_of_mem_besselU0 (h_fix p hp), h_shared q hq p hp]
    obtain ⟨v, hv, h_frame⟩ : ∃ v ∈ S.classUnipotent₀ c,
        frameImage (v * (u p * p.2)).val.val = frameImage (u q * q.2).val.val :=
      exists_frameImage_mul_eq_of_sub_mem (hZ_moved p hp) (hZ_moved q hq) hZ_int
        (h_cellRank p₁ hp₁).leadingMinor_ne_zero h_shared_moved (h_part q hq p hp) hd h_congr
    rw [← mul_assoc] at h_frame
    exact hB.separated p hp q hq (v * u p) (mul_mem hv (hu p hp)) (u q) (hu q hq) h_frame
  calc (B.encard : ℝ≥0∞)
      ≤ ENNReal.ofReal (submoduleIndex (d • intVectors (Ô E) (Fin 𝔰.n))
          (intVectors (Ô E) (Fin 𝔰.n)) ^ card (Fin 𝔰.ϱ)) * 1 := by
        refine encard_le_of_colouring block (submoduleIndex_smul_ne_zero hd_int) h_block_int
          fun C hC _ _ h_congr ↦ ?_
        exact_mod_cast Set.encard_le_one_iff.2 fun p q hp hq ↦
          h_unique p (hC hp) q (hC hq) (h_congr q hq p hp)
    _ = ENNReal.ofReal ((genIndex d.val ^ 𝔰.n) ^ 𝔰.ϱ) := by
        rw [submoduleIndex_smul_intVectors hd_int, Fintype.card_fin, Fintype.card_fin, mul_one]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- **The part in the isotropic space.** Let `E` be a CM field with a primitive 5040-th root of
unity and `S` admissible filling data over `E`. Let `B` be a frame set for the class `c`: near terms
whose frames differ modulo moves, the unipotent elements of level `M` that fix the standard frame.
Suppose the terms of `B` all have cell rank `j`: from the index `j` on, the flags of the standard
frame and of the frame of the term share vectors, and the leading minor of order `j` of their matrix
of products is nonzero. Suppose also that they all have the matrix of products `Z`. Finally, suppose
that after moves `u` in `S.classUnipotent₀ c` their frames all have one part in the anisotropic
space `X₀`. Then `B` has at most `b ^ (366 n⁴ f) · [d] ^ (n ϱ)` terms. Here `b = S.b`, `n = ϱ + 1`
is the length of the frame and `f` the number of infinite places. `[d]` is the generalised index of
`d = S.frameModulus j Z = M det(Y Yᴴ)`, where `Y` is the first `j` rows of `Z` completed by rows of
`1`. -/
lemma IsFrameSet.encard_le_of_framePartX₀_eq (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, S.HasCellRank j p.2) (hZ : ∀ p ∈ B, S.frameProducts p.2 = Z)
    {u : S.Classes × S.G E → S.G E} (hu : ∀ p ∈ B, u p ∈ S.classUnipotent₀ c)
    (h_part : ∀ p ∈ B, ∀ q ∈ B, framePartX₀ (u p * p.2) = framePartX₀ (u q * q.2))
    {d : (𝔸f E)ˣ} (hd : d.val = ((S.frameModulus j Z : E) : 𝔸f E)) :
    B.encard ≤ ENNReal.ofReal (S.b ^ (366 * 𝔰.n ^ 4 * numInfPlaces E)) *
      ENNReal.ofReal ((genIndex d.val ^ 𝔰.n) ^ 𝔰.ϱ) := by
  refine encard_le_of_encard_range_le (fun p : B ↦ S.sharedVectors j p.val.2)
    (hB.encard_range_sharedVectors_le h_cellRank)
    (R := fun p q ↦ S.sharedVectors j p.2 = S.sharedVectors j q.2) (fun _ _ h ↦ h) ?_
  intro D hD _ _ h_shared
  exact (hB.mono hD).encard_le_of_sharedVectors_eq (fun p hp ↦ h_cellRank p (hD hp))
    (fun p hp ↦ hZ p (hD hp)) h_shared (fun p hp ↦ hu p (hD hp))
    (fun p hp q hq ↦ h_part p (hD hp) q (hD hq)) hd

/-- **The part in `X₀`, the anisotropic space.** Let `E` be a CM field with a primitive 5040-th root
of unity and `S` admissible filling data over `E`. Take near terms of cell rank `j`, with frames
different modulo moves and one matrix of products `Z`, whose leading minor of order `j` is `δ`.
Suppose that after the moves `u` the parts in `X₀` of the frames have the same products with the `r`
independent columns of `y`, and `r + l = k`, the rank of `X₀`. Then there are at most
`[d] ^ (l n) · b ^ (366 n⁴ f) · [d'] ^ (n ϱ)` terms, where `d = M δ`, `d' = S.frameModulus j Z`,
`[·]` is the generalised index, `b = S.b`, `n = ϱ + 1` the length of the frame and `f` the number of
infinite places. -/
lemma IsFrameSet.encard_le_of_conjTranspose_mul_eq (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, S.HasCellRank j p.2) (hZ : ∀ p ∈ B, S.frameProducts p.2 = Z)
    {p₀ : S.Classes × S.G E} (hp₀ : p₀ ∈ B) (hy : HasLeftInv y) (h_rank : r + l = 𝔰.k)
    {u : S.Classes × S.G E → S.G E} (hu : ∀ p ∈ B, u p ∈ S.classUnipotent₀ c)
    (h_orth : ∀ p ∈ B, (framePartX₀ (u p * p.2))ᴴ * y = (framePartX₀ (u p₀ * p₀.2))ᴴ * y)
    {d d' : (𝔸f E)ˣ} (hd : d.val = ((S.M * leadingMinor Z j : E) : 𝔸f E))
    (hd' : d'.val = ((S.frameModulus j Z : E) : 𝔸f E)) :
    B.encard ≤ ENNReal.ofReal ((genIndex d.val ^ l) ^ 𝔰.n) *
      (ENNReal.ofReal (S.b ^ (366 * 𝔰.n ^ 4 * numInfPlaces E)) *
        ENNReal.ofReal ((genIndex d'.val ^ 𝔰.n) ^ 𝔰.ϱ)) := by
  -- The parts `x p` in `X₀` differ from `x p₀` by vectors of the lattice `P` orthogonal to `y`;
  -- sort them modulo `d P`.
  let x (p : S.Classes × S.G E) : Matrix 𝔰.κ (Fin (𝔰.ϱ + 1)) E := framePartX₀ (u p * p.2)
  let P : Submodule (Ô E) (𝔰.κ → 𝔸f E) := S.complementLattice c y
  have hZ_moved (p : S.Classes × S.G E) (hp : p ∈ B) : S.frameProducts (u p * p.2) = Z :=
    (frameProducts_mul_of_mem_besselU0 (mem_besselU0_of_mem_classUnipotent₀ (hu p hp)) p.2).trans
      (hZ p hp)
  have hZ_int (a b : Fin (𝔰.ϱ + 1)) : IsIntegral ℤ (Z a b) :=
    by simpa [hZ p₀ hp₀] using hB.isIntegral_frameProducts hp₀ a b
  have hd_int : d.val ∈ Ô E := by
    rw [hd, ← det_paddedLeading]
    exact mul_mem (natCast_mem ((Ô E).comap (algebraMap E (𝔸f E))) S.M)
      (isIntMatrix_paddedLeading hZ_int).det_mem
  have h_mem (p : S.Classes × S.G E) (hp : p ∈ B) (i : Fin (𝔰.ϱ + 1)) :
      ((↑) : E → 𝔸f E) ∘ (x p - x p₀).col i ∈ P := by
    obtain ⟨s, h_over⟩ : ∃ s : S.ResidueGL, p.2 ∈ S.termsOver c s p.1 := hB.mem_termsOver p hp
    obtain ⟨s₀, h_over₀⟩ : ∃ s : S.ResidueGL, p₀.2 ∈ S.termsOver c s p₀.1 := hB.mem_termsOver p₀ hp₀
    have h_zero : yᴴ * (x p - x p₀) = 0 := by
      rw [← conjTranspose_eq_zero, conjTranspose_mul, conjTranspose_conjTranspose,
        conjTranspose_sub, Matrix.sub_mul, h_orth p hp, sub_self]
    have h_col : yᴴ *ᵥ (x p - x p₀).col i = 0 := funext fun a ↦ congrFun₂ h_zero a i
    exact coe_mem_complementLattice h_col
      (col_framePartX₀_sub_mem (mul_mem_termsOver_of_mem_classUnipotent₀ (hu p₀ hp₀) h_over₀)
        (mul_mem_termsOver_of_mem_classUnipotent₀ (hu p hp) h_over)
        ((hZ_moved p hp).trans (hZ_moved p₀ hp₀).symm) i)
  have h_index : (submoduleIndex (d • P) P : ℝ) = genIndex d.val ^ l :=
    submoduleIndex_smul_complementLattice hy h_rank hd_int
  have h_index_ne : submoduleIndex (d • P) P ≠ 0 := by
    exact_mod_cast h_index.trans_ne (pow_pos (genIndex_pos d) l).ne'
  have h_factor : ENNReal.ofReal ((genIndex d.val ^ l) ^ 𝔰.n) =
      ENNReal.ofReal ((submoduleIndex (d • P) P : ℝ) ^ card (Fin 𝔰.n)) := by
    rw [h_index, Fintype.card_fin]
  rw [h_factor]
  refine encard_le_of_colouring (fun p i ↦ ((↑) : E → 𝔸f E) ∘ (x p - x p₀).col i) h_index_ne h_mem
    fun D hD p₁ hp₁ h_congr ↦ ?_
  -- In one class `D` the parts in `X₀` are congruent modulo `d`; a move removes the difference.
  have h_join : ∀ p ∈ D, ∃ u' ∈ S.classUnipotent₀ c, framePartX₀ (u' * p.2) = x p₁ := by
    intro p hp
    have h_multiple (i : Fin (𝔰.ϱ + 1)) :
        ((↑) : E → 𝔸f E) ∘ (x p - x p₁).col i ∈ d • S.classLatticeX₀ c := by
      obtain ⟨v, hv, h_value⟩ : ∃ v ∈ P, d.val • v =
          ((↑) : E → 𝔸f E) ∘ (x p - x p₀).col i - ((↑) : E → 𝔸f E) ∘ (x p₁ - x p₀).col i :=
        (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (h_congr p hp p₁ hp₁ i)
      exact ⟨v, saturatedLattice_le _ _ hv, h_value.trans (by ext a; simp)⟩
    have h_moved_cellRank (q : S.Classes × S.G E) (hq : q ∈ B) : S.HasCellRank j (u q * q.2) :=
      (h_cellRank q hq).mul_of_mem_classUnipotent₀ (hu q hq)
    have hZ₁ : S.frameProducts (u p₁ * p₁.2) = Z := hZ_moved p₁ (hD hp₁)
    have hZ_eq : S.frameProducts (u p * p.2) = S.frameProducts (u p₁ * p₁.2) :=
      (hZ_moved p (hD hp)).trans hZ₁.symm
    obtain ⟨v, hv, h_moved⟩ : ∃ v ∈ S.classUnipotent₀ c, framePartX₀ (v * (u p * p.2)) = x p₁ :=
      (h_moved_cellRank p₁ (hD hp₁)).exists_framePartX₀_mul_eq_of_sub_mem
        (h_moved_cellRank p (hD hp)) hZ_eq (by rw [hZ₁, hd]) (by rwa [hZ₁]) h_multiple
    exact ⟨v * u p, mul_mem hv (hu p (hD hp)), by rwa [mul_assoc]⟩
  choose! u' hu' h_eq using h_join
  exact (hB.mono hD).encard_le_of_framePartX₀_eq (fun p hp ↦ h_cellRank p (hD hp))
    (fun p hp ↦ hZ p (hD hp)) hu' (fun p hp q hq ↦ (h_eq p hp).trans (h_eq q hq).symm) hd'

/-- **Lifts of `L`.** Let `E` be a CM field with a primitive 5040-th root of unity and `S`
admissible filling data over `E`. Take near terms `γ` of cell rank `j`, with frames different modulo
moves and one matrix of products `Z`, whose lattices `L_γ^M` contain the lattice `L ⊆ Λ ∩ X₀` of
corank `l` with the basis `y a`. Let `d` be `M` times the leading minor of order `j` of `Z`, and
`d' = S.frameModulus j Z`. Then there are at most `disc(L) ^ (2 ϱ) · [d] ^ (l n) · b ^ (366 n⁴
f) · [d'] ^ (n ϱ)` terms. Here `[d] = genIndex d` is the inverse of the factor by which `d` scales
Haar measure, `disc(L)` is the square root of the generalised index of the Gram determinant of a
basis of `L`, `b = S.b`, `n = ϱ + 1` and `f` is the number of infinite places. -/
lemma IsFrameSet.encard_le_of_le_termLattice (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, S.HasCellRank j p.2) (hZ : ∀ p ∈ B, S.frameProducts p.2 = Z)
    (hy : HasLeftInv y) (h_rank : r + l = 𝔰.k) {a : GL (Fin r) (𝔸f E)}
    (h_le_classLattice : colLattice (Ô E) (finAdeleMatrix y * a.val) ≤ S.classLatticeX₀ c)
    (h_le_termLattice :
      ∀ p ∈ B, colLattice (Ô E) (finAdeleMatrix y * a.val) ≤ S.termLattice c p.1 p.2)
    {d d' : (𝔸f E)ˣ} (hd : d.val = ((S.M * leadingMinor Z j : E) : 𝔸f E))
    (hd' : d'.val = ((S.frameModulus j Z : E) : 𝔸f E)) :
    B.encard ≤
      ENNReal.ofReal ((discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) ^ 2) ^ 𝔰.ϱ) *
        (ENNReal.ofReal ((genIndex d.val ^ l) ^ 𝔰.n) *
          (ENNReal.ofReal (S.b ^ (366 * 𝔰.n ^ 4 * numInfPlaces E)) *
            ENNReal.ofReal ((genIndex d'.val ^ 𝔰.n) ^ 𝔰.ϱ))) := by
  -- Sort the rows of the lifts modulo the lattice `K` spanned by the Gram matrix of the basis of
  -- `L`; its index is the square of the discriminant.
  have h_lift : ∀ p ∈ B, ∃ w : Matrix (Fin 𝔰.ϱ) (Fin r) E, IsLift p.2 y a w :=
    fun p hp ↦ exists_isLift (h_le_termLattice p hp)
  choose! w hw using h_lift
  let K : Submodule (Ô E) (Fin r → 𝔸f E) :=
    colLattice (Ô E) ((finAdeleMatrix y * a.val)ᴴ * (finAdeleMatrix y * a.val))ᵀ
  have h_index : (submoduleIndex K (intVectors (Ô E) (Fin r)) : ℝ) =
      discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) ^ 2 :=
    submoduleIndex_gram_eq_discriminant_sq hy h_le_classLattice
  have h_index_ne : submoduleIndex K (intVectors (Ô E) (Fin r)) ≠ 0 := by
    exact_mod_cast h_index.trans_ne
      (pow_pos (IsLatticeOfRank.discriminant_pos ⟨y, a, hy, rfl⟩) 2).ne'
  have h_factor :
      ENNReal.ofReal ((discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) ^ 2) ^ 𝔰.ϱ) =
        ENNReal.ofReal ((submoduleIndex K (intVectors (Ô E) (Fin r)) : ℝ) ^ card (Fin 𝔰.ϱ)) := by
    rw [h_index, Fintype.card_fin]
  rw [h_factor]
  refine encard_le_of_colouring (fun p i ↦ (finAdeleMatrix (w p) * a.val) i) h_index_ne
    (fun p hp i ↦ (hw p hp).isIntMatrix i) fun D hD p₁ hp₁ h_congr ↦ ?_
  -- In one class `D` a move gives every frame the lift of `p₁`.
  have h_join : ∀ p ∈ D, ∃ u ∈ S.classUnipotent₀ c,
      (framePartX₀ (u * p.2))ᴴ * y = -((S.M : E) • ((isotropicRows Z)ᴴ * w p₁)) := by
    intro p hp
    rw [← hZ p (hD hp)]
    exact (hw p (hD hp)).exists_conjTranspose_framePartX₀_mul_eq_neg hy h_le_classLattice
      (h_congr p₁ hp₁ p hp)
  choose! u hu h_eq using h_join
  exact (hB.mono hD).encard_le_of_conjTranspose_mul_eq (fun p hp ↦ h_cellRank p (hD hp))
    (fun p hp ↦ hZ p (hD hp)) hp₁ hy h_rank hu
    (fun p hp ↦ (h_eq p hp).trans (h_eq p₁ hp₁).symm) hd hd'

/-- The terms of a frame set with one cell rank `j` and one matrix of products `Z`, whose lattices
`L_γ^M` contain a lattice `L` of corank `l` and discriminant at most `b ^ (n³ f)`, number at most
`b ^ ((366 n⁴ + 2 n³ (ϱ + l n + n ϱ)) f)`; here `n = ϱ + 1` is the length of the frame and `f` the
number of infinite places. -/
private lemma IsFrameSet.encard_le_of_frameProducts_eq (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, S.HasCellRank j p.2) {p₀ : S.Classes × S.G E} (hp₀ : p₀ ∈ B)
    (hZ : ∀ p ∈ B, S.frameProducts p.2 = S.frameProducts p₀.2) (hy : HasLeftInv y)
    (h_rank : r + l = 𝔰.k) {a : GL (Fin r) (𝔸f E)}
    (h_le_classLattice : colLattice (Ô E) (finAdeleMatrix y * a.val) ≤ S.classLatticeX₀ c)
    (h_disc : discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) ≤ S.discriminantBound)
    (h_le_termLattice :
      ∀ p ∈ B, colLattice (Ô E) (finAdeleMatrix y * a.val) ≤ S.termLattice c p.1 p.2) :
    B.encard ≤ ENNReal.ofReal (S.b ^ ((366 * 𝔰.n ^ 4 +
      2 * 𝔰.n ^ 3 * (𝔰.ϱ + l * 𝔰.n + 𝔰.n * 𝔰.ϱ)) * numInfPlaces E)) := by
  have hb : 1 ≤ S.b := S.one_le_b
  let N : ℝ := S.b ^ (2 * 𝔰.n ^ 3 * numInfPlaces E)
  have h_pos : 0 < discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) :=
    IsLatticeOfRank.discriminant_pos ⟨y, a, hy, rfl⟩
  have h_disc_sq : discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) ^ 2 ≤ N := by
    grw [h_disc, discriminantBound, ← pow_mul]
    exact pow_le_pow_right₀ hb (by lia)
  have h_minor : leadingMinor (S.frameProducts p₀.2) j ≠ 0 :=
    (h_cellRank p₀ hp₀).leadingMinor_ne_zero
  have hM_ne : (S.M : E) ≠ 0 := by simp [S.levelPrime_prime_and_ne, Nat.Prime.ne_zero]
  let d : (𝔸f E)ˣ := principalIdele
    (Units.mk0 (S.M * leadingMinor (S.frameProducts p₀.2) j) (mul_ne_zero hM_ne h_minor))
  let d' : (𝔸f E)ˣ := principalIdele
    (Units.mk0 (S.frameModulus j (S.frameProducts p₀.2)) (S.frameModulus_ne_zero h_minor))
  have hd_pos : 0 < genIndex d.val := genIndex_pos d
  have hd'_pos : 0 < genIndex d'.val := genIndex_pos d'
  have hd_le : genIndex d.val ≤ N := (hB.near p₀ hp₀).genIndex_M_mul_leadingMinor_le j
  have hd'_le : genIndex d'.val ≤ N := (hB.near p₀ hp₀).genIndex_frameModulus_le
  -- The three rounds, with every index replaced by the common bound `N = b ^ (2 n³ f)`.
  grw [hB.encard_le_of_le_termLattice (d := d) (d' := d') h_cellRank hZ hy h_rank h_le_classLattice
    h_le_termLattice (hd := rfl) (hd' := rfl), h_disc_sq, hd_le, hd'_le]
  simp (disch := positivity) only [← ofReal_mul]
  simp only [N, ← pow_mul, ← pow_add]
  exact le_of_eq (by ring_nf)

/-- **Frames over a lattice.** Let `L ⊆ Λ ∩ X₀` be a lattice of corank `l` and discriminant at most
`b ^ (n³ f)`, and `B` a frame set for the class `c`: near terms `(c', γ)` with `γ` over some block
`(c, s, c')` (that is, `h_c⁻¹ γ h_c'` is integral with reduction `s`), whose frames are different
modulo moves. Suppose that each term has a cell rank `j` and that `L ⊆ L_γ^M`. Then `B` has at most
`b ^ (2000 n⁶ (l + 1) f)` elements. Here `L_γ^M` is the lattice of the `v ∈ Λ ∩ X₀` such that some
vector of `v + M (Λ ∩ X)` is orthogonal to the frame of `γ`, where `Λ` is the lattice of `c`, `X`
the isotropic and `X₀` the anisotropic space; `b = S.b` is the size parameter, `n` the length of the
frame and `f` the number of infinite places. -/
theorem IsFrameSet.encard_le (hB : S.IsFrameSet c B)
    (h_cellRank : ∀ p ∈ B, ∃ j : Fin (𝔰.ϱ + 2), S.HasCellRank j p.2)
    (h_rank : r + l = 𝔰.k) {L : Submodule (Ô E) (𝔰.κ → 𝔸f E)} (hL : IsLatticeOfRank r L)
    (h_le_classLattice : L ≤ S.classLatticeX₀ c) (h_disc : discriminant r L ≤ S.discriminantBound)
    (h_le_termLattice : ∀ p ∈ B, L ≤ S.termLattice c p.1 p.2) :
    B.encard ≤ ENNReal.ofReal (S.b ^ (2000 * 𝔰.n ^ 6 * (l + 1) * numInfPlaces E)) := by
  -- Fix the cell rank and the matrix of products; then sort in three rounds.
  have hb : 1 ≤ S.b := S.one_le_b
  obtain ⟨y, a, hy, rfl⟩ : ∃ (y : Matrix 𝔰.κ (Fin r) E) (a : GL (Fin r) (𝔸f E)),
      HasLeftInv y ∧ colLattice (Ô E) (finAdeleMatrix y * a.val) = L := hL
  choose! rankOf h_rankOf using h_cellRank
  have h_ranks : (Set.range fun p : B ↦ rankOf p).encard ≤
      ENNReal.ofReal (S.b ^ (2 * numInfPlaces E)) := by
    grw [Set.encard_le_card, ← varrho_add_two_le_b_pow, ofReal_natCast]
    simp
  let count : ℝ≥0∞ := ENNReal.ofReal (S.b ^ ((366 * 𝔰.n ^ 4 +
    2 * 𝔰.n ^ 3 * (𝔰.ϱ + l * 𝔰.n + 𝔰.n * 𝔰.ϱ)) * numInfPlaces E))
  have h_one_rank (j : Fin (𝔰.ϱ + 2)) (D : Set (S.Classes × S.G E)) (hD : D ⊆ B)
      (h_cellRank : ∀ p ∈ D, S.HasCellRank j p.2) :
      D.encard ≤ ENNReal.ofReal (S.b ^ (270 * 𝔰.n ^ 3 * numInfPlaces E)) * count := by
    refine encard_le_of_encard_range_le (fun p : D ↦ S.frameProducts p.val.2)
      (hB.mono hD).encard_range_frameProducts_le
      (R := fun p q ↦ S.frameProducts p.2 = S.frameProducts q.2) (fun _ _ h ↦ h) ?_
    intro C hC p₀ hp₀ hZ
    exact (hB.mono (hC.trans hD)).encard_le_of_frameProducts_eq
      (fun p hp ↦ h_cellRank p (hC hp)) hp₀ (fun p hp ↦ hZ p hp p₀ hp₀) hy h_rank
      h_le_classLattice h_disc fun p hp ↦ h_le_termLattice p (hD (hC hp))
  calc (B.encard : ℝ≥0∞)
      ≤ ENNReal.ofReal (S.b ^ (2 * numInfPlaces E)) *
          (ENNReal.ofReal (S.b ^ (270 * 𝔰.n ^ 3 * numInfPlaces E)) * count) := by
        refine encard_le_of_encard_range_le (fun p : B ↦ rankOf p) h_ranks
          (R := fun p q ↦ rankOf p = rankOf q) (fun _ _ h ↦ h) ?_
        intro D hD p₀ hp₀ h_same
        refine h_one_rank (rankOf p₀) D hD fun p hp ↦ ?_
        rw [← h_same p hp p₀ hp₀]
        exact h_rankOf p (hD hp)
    _ = ENNReal.ofReal (S.b ^ ((2 + 270 * 𝔰.n ^ 3 + (366 * 𝔰.n ^ 4 +
          2 * 𝔰.n ^ 3 * (𝔰.ϱ + l * 𝔰.n + 𝔰.n * 𝔰.ϱ))) * numInfPlaces E)) := by
        simp (disch := positivity) only [count, ← ofReal_mul, ← pow_add]
        ring_nf
    _ ≤ ENNReal.ofReal (S.b ^ (2000 * 𝔰.n ^ 6 * (l + 1) * numInfPlaces E)) :=
        ofReal_le_ofReal (pow_le_pow_right₀ hb (Nat.mul_le_mul_right _ (by lia)))

end Rounds

/-- Let `E` be a CM field with a primitive 5040-th root of unity and `S` admissible filling data
over `E`, of level `M = p₀ p₁` (`S.M`) and size parameter `b = S.b`. Let `Λ` be the lattice of the
class `c`, `X₀` the anisotropic space (of dimension `𝔰.k`), `X` the isotropic space, `n` the length
of the frame and `f` the number of infinite places. Let `L ⊆ Λ ∩ X₀` be a lattice of rank `r`, with
`r + l = 𝔰.k`, and discriminant at most `b ^ (n³ f)`. Then at most `b ^ (2000 n⁶ (l + 1) f)` pairs
`p = (c', γ)` with `S.IsNearTermAt c t p` have `L ⊆ S.termLattice c c' γ`. The condition
`S.IsNearTermAt c t p` says three things. First, `γ` is a near term from `c'` to `c` and is the
representative picked in its double coset. Second, `γ` has some cell rank `j`: from the index `j`
on, the flags of the standard frame and of `γ`'s frame share vectors, and the leading minor of order
`j` of their matrix of products is nonzero. Third, `γ` has label `t`, the position of its reduction
in its coset of `S.reducedImage besselS`, the image in `S.ResidueGL` of the integral points of the
Bessel group. -/
theorem encard_setOf_isNearTermAt_and_le_termLattice_le {c : S.Classes} {r l : ℕ}
    (t : S.reducedImage besselS)
    (h_rank : r + l = 𝔰.k) {L : Submodule (Ô E) (𝔰.κ → 𝔸f E)} (hL : IsLatticeOfRank r L)
    (h_le_classLattice : L ≤ S.classLatticeX₀ c)
    (h_disc : discriminant r L ≤ S.discriminantBound) :
    {p : S.Classes × S.G E | S.IsNearTermAt c t p ∧ L ≤ S.termLattice c p.1 p.2}.encard ≤
      ENNReal.ofReal (S.b ^ (2000 * 𝔰.n ^ 6 * (l + 1) * numInfPlaces E)) := by
  let B : Set (S.Classes × S.G E) :=
    {p : S.Classes × S.G E | S.IsNearTermAt c t p ∧ L ≤ S.termLattice c p.1 p.2}
  have h_near : ∀ p ∈ B, S.IsNear p.2 := by
    rintro p ⟨⟨⟨⟨h_near, -⟩, -⟩, -⟩, -⟩
    exact h_near
  have h_over : ∀ p ∈ B, ∃ s : S.ResidueGL, p.2 ∈ S.termsOver c s p.1 := by
    rintro p ⟨⟨-, s, h_over, -⟩, -⟩
    exact ⟨s, h_over⟩
  have h_cellRank : ∀ p ∈ B, ∃ i : Fin (𝔰.ϱ + 2), S.HasCellRank i p.2 := by
    rintro p ⟨⟨⟨-, h_cellRank⟩, -⟩, -⟩
    exact h_cellRank
  -- Terms of one label are determined by their frames modulo moves.
  have h_frames : S.IsFrameSet c B :=
    ⟨h_near, h_over, fun p hp q hq u hu u' hu' ↦ hp.1.eq_of_frameImage_eq hu hu' hq.1⟩
  exact h_frames.encard_le h_cellRank h_rank hL h_le_classLattice h_disc fun p hp ↦ hp.2

end New.Filling
end
end

section
/-!
# Sums over lattices of given corank and small discriminant

This file bounds the sum of `(disc L) ^ (-k)` over all classes and all lattices `L ⊂ Λ ∩ X₀` of
given corank and small discriminant (`sum_discriminant_inv_le`).

Notions from other files:
* `X₀ = E ^ κ` is the hermitian space with the standard form, `k` is the cardinality of `κ`, and
  `k₀ = 𝔰.k₀` is a distinguished element of `κ`. `Gf E κ` is the finite adelic unitary group of
  `X₀`, and `stdLevel E κ` is the stabiliser of the standard lattice `Ô ^ κ` in it.
* `S.piN` is the finite idele `π̄` with `π π̄ = N`, and in the bounds `f = numInfPlaces E`.
* `S.Classes` is the set of double cosets of `Gf E κ` under the rational points and the level
  `S.sourceLevel`. If `g` is the chosen representative of the class `c`, then the lattice
  `S.classLatticeX₀ c`, also written `Λ ∩ X₀`, consists of the vectors `v` for which `g⁻¹ v` is
  integral with entry `k₀` divisible by `π̄`.
* `discriminant r L` is the square root of the generalised index `genIndex` of the Gram determinant
  of a basis of the lattice `L` of rank `r`.
-/

@[expose] public section

noncomputable section

namespace New.Filling

/-! ## Means over the classes, and cosets told apart by one row -/

section ClassesAndCosets

open Matrix ENNReal Finset Fintype DoubleCoset Subgroup

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- Let `A` be finite and nonempty with elements mapped by `a` into the finite adelic unitary group
`Gf E κ`, and let `f` be a function on `S.Classes`, the double cosets of this group under the
rational points and the level. If for every `u` the sum of `f` over the classes of the translates
`u * a φ`, `φ ∈ A`, is at most `card A * b`, then the sum of `f` over all classes is at most
`card S.Classes * b` (for `b ≥ 0`). -/
lemma sum_classes_le_of_sum_translates_le {A : Type} [Fintype A] [Nonempty A] (a : A → Gf E 𝔰.κ)
    (f : S.Classes → ℝ≥0∞) {b : ℝ} (hb : 0 ≤ b)
    (h_translates : ∀ u : Gf E 𝔰.κ, ∑ φ : A, f ⟦u * a φ⟧ ≤ .ofReal (card A * b)) :
    ∑ c : S.Classes, f c ≤ .ofReal (card S.Classes * b) := by
  -- `f` is finite, since every class is a term of one of the sums.
  have f_ne_top : ∀ c : S.Classes, f c ≠ ∞ := Quotient.ind fun g ↦ by
    obtain ⟨φ⟩ : Nonempty A := inferInstance
    simpa using
      sum_ne_top.mp (ne_top_of_le_ne_top ofReal_ne_top (h_translates (g / a φ))) φ (mem_univ φ)
  lift f to S.Classes → NNReal using f_ne_top
  -- The defect `δ = b - f` is a function on the double cosets.
  let δ (g : Gf E 𝔰.κ) : ℝ := b - f ⟦g⟧
  have δ_inv : ∀ γ ∈ stdRatPoints, ∀ k ∈ S.sourceLevel, ∀ g : Gf E 𝔰.κ, δ (γ * g * k) = δ g := by
    intro γ hγ k hk g
    have same_class : (⟦g⟧ : S.Classes) = ⟦γ * g * k⟧ :=
      Quotient.sound (DoubleCoset.rel_iff.mpr ⟨γ, hγ, k, hk, rfl⟩)
    simp only [δ, same_class]
  have δ_fixed : S.sourceLevel ≤ rightStabilizer δ := fun k hk g ↦ by
    simpa using δ_inv 1 (one_mem _) k hk g
  have δ_smooth : δ ∈ smoothInvariants stdRatPoints :=
    ⟨fun γ hγ g ↦ by simpa using δ_inv γ hγ 1 (one_mem _) g,
      isOpen_mono δ_fixed S.isLevel_sourceLevel.isOpen⟩
  -- The sum of the translates of `δ` is nonnegative, and the integral is translation invariant.
  have translates_nonneg (g : Gf E 𝔰.κ) : 0 ≤ ∑ φ : A, δ (g * a φ) := by
    have h_real : ((∑ φ : A, f ⟦g * a φ⟧ : NNReal) : ℝ) ≤ card A * b :=
      (le_ofReal_iff_toReal_le coe_ne_top (by positivity)).mp
        ((ofNNReal_finsetSum _ _).trans_le (h_translates g))
    simpa [δ] using h_real
  have integral_nonneg : 0 ≤ ∑ _φ : A, classIntegral stdRatPoints S.sourceLevel δ :=
    calc 0 ≤ classIntegral stdRatPoints S.sourceLevel fun g ↦ ∑ φ : A, δ (g * a φ) := by
          -- The integral is a weighted sum of values with nonnegative weights.
          refine mul_nonneg (by simp) (finsum_nonneg fun q ↦ mul_nonneg (by simp) ?_)
          exact translates_nonneg q.out
      _ = ∑ _φ : A, classIntegral stdRatPoints S.sourceLevel δ :=
          classIntegral_sum univ (fun _ ↦ AddMonoidHom.id ℝ) a (fun _ ↦ δ_smooth) fun _ ↦ rfl
  -- As `S.sourceLevel` fixes `δ`, its integral is the sum of `b - f c` over the classes `c`.
  have integral_eq :
      classIntegral stdRatPoints S.sourceLevel δ = ∑ c : S.Classes, (b - f c : ℝ) := by
    rw [classIntegral_eq_classSum δ_fixed, classSum_sourceLevel_eq_sum]
    exact sum_congr rfl fun c _ ↦ congrArg (fun d : S.Classes ↦ b - (f d : ℝ)) c.out_eq
  have h_real : ((∑ c : S.Classes, f c : NNReal) : ℝ) ≤ card S.Classes * b := by
    simpa [integral_eq, Fintype.card_pos] using integral_nonneg
  rw [← ofNNReal_finsetSum]
  exact (le_ofReal_iff_toReal_le coe_ne_top (by positivity)).mpr h_real

variable (S) in
/-- The rows `𝔰.k₀` of the matrices of `y⁻¹` and `y'⁻¹` are congruent modulo `S.piN`: their
difference maps every integral vector into `Ô π̄`. -/
abbrev InverseRowsCongruent (y y' : stdLevel E 𝔰.κ) : Prop :=
  let Y : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := (y⁻¹ : Gf E 𝔰.κ)
  let Y' : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := (y'⁻¹ : Gf E 𝔰.κ)
  colLattice (Ô E) (replicateRow Unit (Y 𝔰.k₀) - replicateRow Unit (Y' 𝔰.k₀)) ≤
    .comap (.proj ()) (Ô E ∙ S.piN.val)

/-- Let `y`, `y'` be integral unitary matrices whose inverses have congruent rows `𝔰.k₀` modulo the
idele `S.piN` of the filling `S` (`InverseRowsCongruent`). Then `y` and `y'` lie in the same coset
of the subgroup of elements that the inclusion `S.inclHFin` of `Gf E κ` in the unitary group of the
large space maps into the subgroup `S.latticeStabilizer` of integral matrices in the lattice
basis. -/
lemma inv_mul_mem_of_inverseRowsCongruent {y y' : stdLevel E 𝔰.κ}
    (h_congr : S.InverseRowsCongruent y y') :
    y⁻¹ * y' ∈ (S.latticeStabilizer.comap S.inclHFin).subgroupOf (stdLevel E 𝔰.κ) := by
  -- It is enough that row `k₀` of `y⁻¹ y'` is congruent to that of `1`.
  refine S.inclHFin_mem_latticeStabilizer_iff.2 ⟨(y⁻¹ * y').property, fun _ j ↦ ?_⟩
  -- Apply the difference of the rows to the integral column `j` of `y'`.
  let Y : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := ((y⁻¹ : stdLevel E 𝔰.κ) : Gf E 𝔰.κ)
  let Y' : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := ((y'⁻¹ : stdLevel E 𝔰.κ) : Gf E 𝔰.κ)
  let M : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := (y' : Gf E 𝔰.κ)
  let row : Matrix Unit 𝔰.κ (𝔸f E) := replicateRow Unit (Y 𝔰.k₀) - replicateRow Unit (Y' 𝔰.k₀)
  have h_image : row *ᵥ Mᵀ j ∈ colLattice (Ô E) row :=
    ⟨Mᵀ j, y'.property.isIntMatrix.transpose j, rfl⟩
  have h_entry : ((Y - Y') * M) 𝔰.k₀ j ∈ Ô E ∙ S.piN.val := h_congr h_image
  simpa [M, Y, Y', Matrix.sub_mul] using h_entry

end ClassesAndCosets

/-!
## Lattices of given corank

The lattice of a class is the kernel of a row modulo `piN` on a unimodular lattice. One averages
over the rows and counts the rows that vanish modulo `piN` on a given lattice. One then sums over
the sublattices of finite index of a primitive lattice, and finally over the primitive lattices.
-/

section CrudeLattices

open NumberField Matrix Module Fintype ENNReal Pointwise

variable {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {𝔰 : Shape}

section Forms

variable {S : Filling E 𝔰}

variable (S) in
/-- The lattices of rank `r` in `L₀` with discriminant at most `S.discriminantBound`. -/
abbrev BoundedDiscSublattice (r : ℕ) (L₀ : Submodule (Ô E) (𝔰.κ → 𝔸f E)) : Type :=
  {L : Submodule (Ô E) (𝔰.κ → 𝔸f E) //
    IsLatticeOfRank r L ∧ L ≤ L₀ ∧ discriminant r L ≤ S.discriminantBound}

/-- The unimodular lattice `u Ô ^ κ`: the vectors `v` with `u⁻¹ v` integral. -/
abbrev unimodularLattice (u : Gf E 𝔰.κ) : Submodule (Ô E) (𝔰.κ → 𝔸f E) :=
  preimageLattice (Ô E) u.val.inv

variable (S) in
/-- The linear form "row `k₀` of `y⁻¹ u⁻¹`" on `u Ô ^ κ`, called the form of `y`, vanishes on `L`
modulo `piN`. -/
def RowVanishesModPiN (u : Gf E 𝔰.κ) (y : stdLevel E 𝔰.κ) (L : Submodule (Ô E) (𝔰.κ → 𝔸f E)) :
    Prop :=
  ∀ v ∈ L,
    (((y⁻¹ : Gf E 𝔰.κ) : Matrix 𝔰.κ 𝔰.κ (𝔸f E)) *ᵥ u.val.inv *ᵥ v) 𝔰.k₀ ∈ Ô E ∙ S.piN.val

variable (S) in
/-- The term `(disc L) ^ (-k)`, for the discriminant in rank `r`, if the form of `y` on `u Ô ^ κ`
vanishes on `L` modulo `piN`, and `0` otherwise. -/
def discWeightIfRowVanishes (u : Gf E 𝔰.κ) (y : stdLevel E 𝔰.κ) (r : ℕ) :
    Submodule (Ô E) (𝔰.κ → 𝔸f E) → ℝ≥0∞ :=
  {L : Submodule (Ô E) (𝔰.κ → 𝔸f E) | S.RowVanishesModPiN u y L}.indicator
    fun L ↦ ENNReal.ofReal (discriminant r L ^ 𝔰.k)⁻¹

variable (S) in
/-- The cosets in `stdLevel E κ` of the subgroup of elements that `inclHFin` maps into
`latticeStabilizer`: those whose row `k₀` is congruent to that of `1` modulo `piN`. They
parametrise the positions of the form modulo `piN`. -/
abbrev LatticeStabilizerCoset : Type :=
  stdLevel E 𝔰.κ ⧸ (S.latticeStabilizer.comap S.inclHFin).subgroupOf (stdLevel E 𝔰.κ)

/-! ### Unimodular lattices -/

omit [HasPrimitiveRoot5040 E] in
/-- Let the chosen representative of the class `c` be `η u y` with `η` rational and `y` integral,
and let `L` lie in the lattice `Λ ∩ X₀` of `c`, which consists of the vectors `v` for which
`(η u y)⁻¹ v` is integral with entry `k₀` divisible by `π̄ = S.piN`. Then `η⁻¹ L` lies in `u Ô ^ κ`,
and the form of `y` vanishes on it modulo `π̄`. -/
lemma map_le_and_rowVanishesModPiN_of_out_eq {c : S.Classes} {η : U (stdSpace E 𝔰.κ).J}
    {u : Gf E 𝔰.κ} {y : stdLevel E 𝔰.κ} (hc : c.out = (stdSpace E 𝔰.κ).embFin η * u * y)
    {L : Submodule (Ô E) (𝔰.κ → 𝔸f E)} (h_le : L ≤ S.classLatticeX₀ c) :
    L.map ((finAdeleMatrix (η⁻¹ : GL 𝔰.κ E).val).mulVecLin.restrictScalars (Ô E)) ≤
      unimodularLattice u ∧
    S.RowVanishesModPiN u y
      (L.map ((finAdeleMatrix (η⁻¹ : GL 𝔰.κ E).val).mulVecLin.restrictScalars (Ô E))) := by
  let Y : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := ((y⁻¹ : stdLevel E 𝔰.κ) : Gf E 𝔰.κ)
  let H : Matrix 𝔰.κ 𝔰.κ (𝔸f E) := finAdeleMatrix (η⁻¹ : GL 𝔰.κ E).val
  have hH : H = ((stdSpace E 𝔰.κ).embFin η⁻¹ : Gf E 𝔰.κ) := by simp [H, -map_inv]
  have h_coord : S.classCoordX₀ c = middleInclusionMatrix 𝔰 S.piN * (Y * (u.val.inv * H)) := by
    rw [classCoordX₀, hc, _root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, hH]
    -- The coercion to matrices respects products, and turns `u⁻¹` into `u.1.inv`.
    rfl
  -- For `v ∈ L` the vector `y⁻¹ u⁻¹ η⁻¹ v` is integral, with entry `k₀` divisible by `piN`.
  have h_vector (v : 𝔰.κ → 𝔸f E) (hv : v ∈ L) :
      Y *ᵥ u.val.inv *ᵥ H *ᵥ v ∈ intVectors (Ô E) 𝔰.κ ∧
      (Y *ᵥ u.val.inv *ᵥ H *ᵥ v) 𝔰.k₀ ∈ Ô E ∙ S.piN.val := by
    have h_int : IsIntMatrix (Ô E)
        (middleInclusionMatrix 𝔰 S.piN * replicateCol Unit (Y *ᵥ u.1.inv *ᵥ H *ᵥ v)) := fun i j ↦ by
      -- `classLatticeX₀` consists of the vectors that `classCoordX₀` makes integral.
      have h_entry : (S.classCoordX₀ c *ᵥ v) i ∈ Ô E := h_le hv i
      rwa [h_coord, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec] at h_entry
    obtain ⟨h_all, h_row⟩ := S.isIntMatrix_middleInclusionMatrix_mul_iff.1 h_int
    exact ⟨fun i ↦ h_all i (), h_row ()⟩
  constructor
  · rintro _ ⟨v, hv, rfl⟩
    exact (mulVec_mem_intVectors_iff (inv_mem y.property)).1 (h_vector v hv).left
  · rintro _ ⟨v, hv, rfl⟩
    exact (h_vector v hv).right

/-- Let `E` contain a primitive 5040th root of unity, let `S` be filling data over `E`, and let the
chosen representative of the class `c` be `η u y` with `η` rational and `y` integral. The sum of
`(disc L) ^ (-k)`, `k = #κ`, over the lattices `L` of rank `r` and discriminant at most
`S.discriminantBound` in `Λ ∩ X₀` is at most the same sum over those in `u Ô ^ κ` on which the form
"row `𝔰.k₀` of `y⁻¹ u⁻¹`" vanishes modulo `S.piN`. -/
lemma tsum_discriminant_inv_le_of_out_eq {c : S.Classes} {η : U (stdSpace E 𝔰.κ).J} {u : Gf E 𝔰.κ}
    {y : stdLevel E 𝔰.κ} (hc : c.out = (stdSpace E 𝔰.κ).embFin η * u * y) (r : ℕ) :
    ∑' L : S.BoundedDiscSublattice r (S.classLatticeX₀ c),
      ENNReal.ofReal (discriminant r L.val ^ 𝔰.k)⁻¹ ≤
      ∑' L : S.BoundedDiscSublattice r (unimodularLattice u),
        S.discWeightIfRowVanishes u y r L.val := by
  -- The rational isometry `η⁻¹` moves the lattices injectively and preserves the discriminant.
  let H : Matrix 𝔰.κ 𝔰.κ E := (η⁻¹ : GL 𝔰.κ E).val
  let P : (𝔰.κ → 𝔸f E) →ₗ[Ô E] 𝔰.κ → 𝔸f E := (finAdeleMatrix H).mulVecLin.restrictScalars (Ô E)
  have hH : Hᴴ * H = 1 := by simpa [H,
    star_eq_conjTranspose] using mem_unitaryGroupOf_iff.1 η⁻¹.property
  have h_inv : finAdeleMatrix Hᴴ * finAdeleMatrix H = 1 := by
    simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using congrArg finAdeleMatrix hH
  have hP : Function.Injective P := injective_restrictScalars_mulVecLin h_inv
  have h_map (L : S.BoundedDiscSublattice r (S.classLatticeX₀ c)) :
      (IsLatticeOfRank r (L.val.map P) ∧ L.val.map P ≤ unimodularLattice u ∧
        discriminant r (L.val.map P) ≤ S.discriminantBound) ∧
      S.RowVanishesModPiN u y (L.1.map P) ∧ discriminant r (L.1.map P) = discriminant r L.1 := by
    obtain ⟨L, hL, h_le, h_small⟩ := L
    obtain ⟨h_rank, h_disc⟩ := hL.map_of_unitary hH
    obtain ⟨h_map_le, h_kills⟩ := map_le_and_rowVanishesModPiN_of_out_eq hc h_le
    exact ⟨⟨h_rank, h_map_le, h_disc.trans_le h_small⟩, h_kills, h_disc⟩
  let move (L : S.BoundedDiscSublattice r (S.classLatticeX₀ c)) :
    S.BoundedDiscSublattice r (unimodularLattice u) :=
    ⟨L.val.map P, (h_map L).1⟩
  have h_move : Function.Injective move := fun L L' h ↦
    Subtype.ext (Submodule.map_injective_of_injective hP (congrArg Subtype.val h))
  calc _ = ∑' L : S.BoundedDiscSublattice r (S.classLatticeX₀ c),
         S.discWeightIfRowVanishes u y r (move L).val := by
        refine tsum_congr fun L ↦ ?_
        obtain ⟨-, h_kills, h_disc⟩ := h_map L
        rw [discWeightIfRowVanishes, Set.indicator_of_mem h_kills, h_disc]
    _ ≤ _ := tsum_comp_le_tsum_of_injective h_move fun L ↦ S.discWeightIfRowVanishes u y r L.val

omit [HasPrimitiveRoot5040 E] in
/-- Let `u` be in `Gf E 𝔰.κ`, and let `φ` be a coset in `stdLevel E 𝔰.κ` of the preimage under
`inclHFin` of `latticeStabilizer`, with chosen element `φ.out`. Then the chosen representative of
the class of `u * φ.out` in the double cosets `S.Classes` equals `embFin η * u * y`. Here `η` is
some rational point of the unitary group `U` of the standard form on `𝔰.κ`, and `y` is some element
of `stdLevel E 𝔰.κ` lying in the coset `φ`. Of the standing hypotheses `S.IsAdmissible`, only one is
used: the level `sourceLevel` of `S`, which defines the double cosets `S.Classes`, is the preimage
of K(M). -/
lemma exists_mk_out_eq_embFin_mul [S.IsAdmissible] (u : Gf E 𝔰.κ) (φ : S.LatticeStabilizerCoset) :
    ∃ (η : U (stdSpace E 𝔰.κ).J) (y : stdLevel E 𝔰.κ),
      (y : S.LatticeStabilizerCoset) = φ ∧
      (⟦u * φ.out⟧ : S.Classes).out = (stdSpace E 𝔰.κ).embFin η * u * y := by
  obtain ⟨_, ⟨η, rfl⟩, g, hg, h_out⟩ : ∃ γ ∈ stdRatPoints (E := E), ∃ g ∈ S.sourceLevel,
      (⟦u * φ.out⟧ : S.Classes).out = γ * (u * φ.out : Gf E 𝔰.κ) * g :=
    (DoubleCoset.eq ..).1 (DoubleCoset.out_eq' ..).symm
  have hg_level : S.inclHFin g ∈ S.principalLevel := IsAdmissible.sourceLevel_eq.le hg
  have hg_stab : S.inclHFin g ∈ S.latticeStabilizer :=
    (S.principalLevel_eq_unitaryLevel.le hg_level).1
  refine ⟨η, φ.out * ⟨g, S.isLevel_sourceLevel.le hg⟩, ?_, h_out.trans (by simp [mul_assoc])⟩
  exact (QuotientGroup.mk_mul_of_mem φ.out hg_stab).trans φ.out_eq

/-! ### Forms and sublattices -/

variable (S) in
/-- The generalised index of `S.piN` is `N ^ f`, where `N = π π̄` and `f` is the number of
infinite places of `E`. -/
lemma genIndex_piN_eq_pow : genIndex S.piN.val = S.N ^ numInfPlaces E := by
  have h_sq : genIndex S.piN.val ^ 2 = (S.N ^ numInfPlaces E) ^ 2 := by
    rw [← genIndex_natCast, ← S.piN_mul_star, map_mul, genIndex_star, sq]
  exact (pow_left_inj₀ (genIndex_pos _).le (by positivity) two_ne_zero).1 h_sq

omit [HasPrimitiveRoot5040 E] in
/-- A vector lies in `d Ô ^ ι` if and only if its multiple by `d⁻¹` is integral. -/
lemma mem_smul_intVectors_iff {ι : Type} {d : (𝔸f E)ˣ} {v : ι → 𝔸f E} :
    v ∈ d • intVectors (Ô E) ι ↔ d⁻¹ • v ∈ intVectors (Ô E) ι := by
  refine ⟨?_, fun hv ↦ ⟨d⁻¹ • v, hv, smul_inv_smul d v⟩⟩
  rintro ⟨w, hw : w ∈ intVectors (Ô E) ι, rfl⟩
  simpa [inv_smul_smul, ← Units.smul_def] using hw

omit [HasPrimitiveRoot5040 E] in
/-- Let `U` be invertible with `U` and `U⁻¹` integral, and let `m` be its first `r` columns
`firstCols e U`. Two forms `v`, `w` are congruent modulo `d` if their values on the other columns
of `U` are, and if their values on `m A`, divided by `d`, differ by a combination of the rows of
`A` with integral coefficients. -/
lemma sub_mem_smul_intVectors_of_values {π : Type} [Fintype π] [DecidableEq π] {r l : ℕ}
    {e : Fin r ⊕ Fin l ≃ π} {U : GL π (𝔸f E)} (hU : U ∈ intGL π (Ô E))
    {A : GL (Fin r) (𝔸f E)} {d : (𝔸f E)ˣ} {v w : π → 𝔸f E}
    (h_rows : d⁻¹ • v ᵥ* (firstCols e U * A.val) - d⁻¹ • w ᵥ* (firstCols e U * A.val) ∈
      colLattice (Ô E) A.valᵀ)
    (h_rest : (fun i : Fin l ↦ (v ᵥ* U.val) (e (.inr i)) - (w ᵥ* U.val) (e (.inr i))) ∈
      d • intVectors (Ô E) (Fin l)) :
    v - w ∈ d • intVectors (Ô E) π := by
  obtain ⟨s, hs_int, hs : A.valᵀ *ᵥ s =
    d⁻¹ • v ᵥ* (firstCols e U * A.val) - d⁻¹ • w ᵥ* (firstCols e U * A.val)⟩ := h_rows
  let z : π → 𝔸f E := d⁻¹ • (v - w)
  have h_first : z ᵥ* firstCols e U = s := by
    refine vecMul_injective_of_isUnit A.isUnit ?_
    change (z ᵥ* firstCols e U) ᵥ* A.val = s ᵥ* A.val
    rw [← mulVec_transpose A.val s, hs, vecMul_vecMul, smul_vecMul, sub_vecMul, smul_sub]
  have h_values : z ᵥ* U.val ∈ intVectors (Ô E) π := by
    intro p
    obtain ⟨i | i, rfl⟩ := e.surjective p
    · rw [show (z ᵥ* U.val) (e (.inl i)) = s i from congrFun h_first i]
      exact hs_int i
    · simpa only [z, smul_vecMul, sub_vecMul, Pi.smul_apply, Pi.sub_apply] using
        mem_smul_intVectors_iff.1 h_rest i
  refine mem_smul_intVectors_iff.2 ?_
  simpa only [mulVec_transpose, vecMul_vecMul, U.mul_inv, vecMul_one] using
    hU.isIntMatrix_inv.transpose.mulVec h_values

/-- **Few forms vanish on a sublattice.** Let the CM field `E` contain a primitive 5040th root of
unity. Let `m` be a basis of a primitive sublattice of rank `r` and corank `l` in `Ô ^ π`, and let
`L` be its sublattice with the basis `m A`. For `a` in a set `B` let `Y a` be integral linear forms
whose values on `L` are divisible by the integral idele `d` and which are pairwise incongruent
modulo `d`. Then `B` has at most `[det A] [d] ^ l` elements, where `[·]` is the generalised index
and `[det A]` is the index of `L` in the primitive sublattice. -/
lemma encard_le_of_vecMul_mem_smul {α π : Type} [Fintype π] {r l : ℕ} {B : Set α}
    (Y : α → π → 𝔸f E) {m : Matrix π (Fin r) (𝔸f E)} {A : GL (Fin r) (𝔸f E)} {d : (𝔸f E)ˣ}
    (hY : ∀ a ∈ B, Y a ∈ intVectors (Ô E) π) (hm : IsPrimitiveMatrix (Ô E) m)
    (h_rank : r + l = card π) (hA : IsIntMatrix (Ô E) A.val) (hd : d.val ∈ Ô E)
    (h_kills : ∀ a ∈ B, Y a ᵥ* (m * A.val) ∈ d • intVectors (Ô E) (Fin r))
    (h_incongruent : ∀ a ∈ B, ∀ b ∈ B, Y a - Y b ∈ d • intVectors (Ô E) π → a = b) :
    B.encard ≤ ENNReal.ofReal (genIndex A.val.det * genIndex d.val ^ l) := by
  classical
  -- Extend `m` to a basis `U` of `Ô ^ π`, and write the values of `Y a` on `m A` as `d W a`. The
  -- class of `W a` modulo the rows of `A` fixes the values on `m` modulo `d`, and the values on the
  -- other `l` basis vectors have `[d] ^ l` classes modulo `d`.
  let e : Fin r ⊕ Fin l ≃ π := equivOfCardEq (by simpa using h_rank)
  obtain ⟨U, hU, rfl⟩ : ∃ U ∈ intGL π (Ô E), m = firstCols e U :=
    (isValuationPair_Ô.exists_firstCols_iff e).2 hm
  let W (a : α) : Fin r → 𝔸f E := d⁻¹ • Y a ᵥ* (firstCols e U * A.val)
  let rest (a : α) (i : Fin l) : 𝔸f E := (Y a ᵥ* U.val) (e (.inr i))
  have h_rest_int (a : α) (ha : a ∈ B) : rest a ∈ intVectors (Ô E) (Fin l) := fun i ↦ by
    simpa only [mulVec_transpose] using hU.isIntMatrix.transpose.mulVec (hY a ha) (e (.inr i))
  have hW_int (a : α) (ha : a ∈ B) : W a ∈ intVectors (Ô E) (Fin r) :=
    mem_smul_intVectors_iff.1 (h_kills a ha)
  have hA_pos : 0 < genIndex A.val.det := genIndex_pos A.det
  have h_index : (submoduleIndex (colLattice (Ô E) A.valᵀ) (intVectors (Ô E) (Fin r)) : ℝ) =
      genIndex A.val.det := by
    rw [← det_transpose]
    exact submoduleIndex_colLattice_intVectors (M := transposeGL A) hA.transpose
  have h_unique (a : α) (ha : a ∈ B) (b : α) (hb : b ∈ B)
      (h_rows : W a - W b ∈ colLattice (Ô E) A.valᵀ)
      (h_rest : rest a - rest b ∈ d • intVectors (Ô E) (Fin l)) : a = b :=
    h_incongruent a ha b hb (sub_mem_smul_intVectors_of_values hU h_rows h_rest)
  -- Sort the forms by the class of `W a`, and those in one such class by the class of `rest a`.
  have h_class (C : Set α) (hC : C ⊆ B)
      (h_rows : ∀ a ∈ C, ∀ b ∈ C, W a - W b ∈ colLattice (Ô E) A.valᵀ) :
      C.encard ≤ ENNReal.ofReal (genIndex d.val ^ l) := by
    refine (encard_le_of_colouring (fun a (_ : Unit) ↦ rest a) (submoduleIndex_smul_ne_zero hd)
      (fun a ha _ ↦ h_rest_int a (hC ha)) (x := 1) fun D hD _ _ h_rest ↦ ?_).trans_eq ?_
    · have h_single : D.encard ≤ 1 := Set.encard_le_one_iff.2 fun a b ha hb ↦
        h_unique a (hC (hD ha)) b (hC (hD hb)) (h_rows a (hD ha) b (hD hb)) (h_rest a ha b hb ())
      exact_mod_cast h_single
    · rw [submoduleIndex_smul_intVectors hd, card_unit, pow_one, mul_one, Fintype.card_fin]
  have h_finite : submoduleIndex (colLattice (Ô E) A.valᵀ) (intVectors (Ô E) (Fin r)) ≠ 0 :=
    mod_cast h_index.trans_ne hA_pos.ne'
  refine (encard_le_of_colouring (fun a (_ : Unit) ↦ W a) h_finite (fun a ha _ ↦ hW_int a ha)
    fun C hC _ _ h_rows ↦ h_class C hC fun a ha b hb ↦ h_rows a ha b hb ()).trans_eq ?_
  rw [h_index, card_unit, pow_one, ofReal_mul hA_pos.le]

/-- Let `E` contain a primitive 5040th root of unity, and let `S` be filling data over `E` with
prime `N = π π̄` and `π̄ = S.piN`. The set `S.LatticeStabilizerCoset` is the quotient of `stdLevel`,
the group of integral unitary matrices on `κ`, by its subgroup of matrices whose row `𝔰.k₀` is
congruent to that of `1` modulo `π̄`. Let `y φ` be an element of each such coset `φ`,
let `V` have codimension `l`, and let `A` be invertible over the finite adeles, with integral
entries. Let `m = sublatticeBasis u.val.val_inv V` be the basis of the adelic points of `V` in
`u Ô ^ κ`. Then for at most `[det A] (N ^ f) ^ l` cosets `φ` the form "row `𝔰.k₀` of
`(y φ)⁻¹ u⁻¹`" vanishes modulo `π̄` on the lattice with basis `m A`. Here `[·]` is the generalised
index and `f` is the number of infinite places. -/
lemma encard_rowVanishesModPiN_le (u : Gf E 𝔰.κ) {y : S.LatticeStabilizerCoset → stdLevel E 𝔰.κ}
    (hy : ∀ φ : S.LatticeStabilizerCoset, (y φ : S.LatticeStabilizerCoset) = φ)
    {V : Submodule E (𝔰.κ → E)} {l : ℕ}
    (h_rank : finrank E V + l = 𝔰.k) {A : GL (Fin (finrank E V)) (𝔸f E)}
    (hA : IsIntMatrix (Ô E) A.val) :
    {φ : S.LatticeStabilizerCoset | S.RowVanishesModPiN u (y φ)
        (colLattice (Ô E) ((sublatticeBasis u.val.val_inv V).val * A.val))}.encard ≤
      ENNReal.ofReal (genIndex A.val.det * (S.N ^ numInfPlaces E) ^ l) := by
  -- Count the rows `k₀` of the `(y φ)⁻¹` modulo `piN`; congruent rows belong to one coset.
  let m : Matrix 𝔰.κ (Fin (finrank E V)) (𝔸f E) := (sublatticeBasis u.val.val_inv V).val
  let B : Set S.LatticeStabilizerCoset :=
    {φ | S.RowVanishesModPiN u (y φ) (colLattice (Ô E) (m * A.val))}
  let row (φ : S.LatticeStabilizerCoset) : 𝔰.κ → 𝔸f E :=
    (((y φ)⁻¹ : stdLevel E 𝔰.κ) : Gf E 𝔰.κ).val.val 𝔰.k₀
  have h_kills (φ : S.LatticeStabilizerCoset) (hφ : φ ∈ B) : row φ ᵥ* (u.val.inv * m * A.val) ∈
      S.piN • intVectors (Ô E) (Fin (finrank E V)) := by
    have h_entry (i : Fin (finrank E V)) : ∃ a ∈ Ô E,
        S.piN * a = (row φ ᵥ* (u.val.inv * m * A.val)) i := by
      rw [Matrix.mul_assoc]
      obtain ⟨a, ha, h_value⟩ := mem_span_singleton_iff_exists_mul.1 (hφ _ (col_mem_colLattice i))
      exact ⟨a, ha, h_value.symm⟩
    choose a ha h_value using h_entry
    exact ⟨a, ha, funext h_value⟩
  have h_apart (φ : S.LatticeStabilizerCoset) (_ : φ ∈ B) (φ' : S.LatticeStabilizerCoset)
    (_ : φ' ∈ B)
      (h_congr : row φ - row φ' ∈ S.piN • intVectors (Ô E) 𝔰.κ) : φ = φ' := by
    obtain ⟨a, ha, h_value⟩ := h_congr
    rw [← hy φ, ← hy φ']
    refine QuotientGroup.eq.2 (inv_mul_mem_of_inverseRowsCongruent (colLattice_le fun i ↦ ?_))
    -- Entry `i` of the difference of the two rows is `π̄ a i`.
    exact mem_span_singleton_iff_exists_mul.2 ⟨a i, ha i, (congrFun h_value i).symm⟩
  rw [← S.genIndex_piN_eq_pow]
  exact encard_le_of_vecMul_mem_smul row (fun φ _ ↦ (y φ).property.isIntMatrix_inv 𝔰.k₀)
    (isPrimitiveMatrix_mul_sublatticeBasis u.val.val_inv V) h_rank hA S.piN_mem h_kills h_apart

/-- Let `E` contain a primitive 5040th root of unity, and let `S` be filling data over `E` with
prime `N = π π̄` and `π̄ = S.piN`. The set `S.LatticeStabilizerCoset` is the quotient of `stdLevel`,
the group of integral unitary matrices on `κ`, by its subgroup of matrices whose row `𝔰.k₀` is
congruent to that of `1` modulo `π̄`. Let `y φ` be an element of each such coset `φ`, and let
`L ⊂ u Ô ^ κ` be a lattice of rank `r` and corank `l`. There is a subspace `V` of dimension `r` such
that `L` has a finite index `i` in the lattice `saturatedLattice` of adelic points of `V` in
`u Ô ^ κ`, `disc L` is `i` times the discriminant of that lattice, and for at most `i (N ^ f) ^ l`
of the `φ` the form "row `𝔰.k₀` of `(y φ)⁻¹ u⁻¹`" takes values divisible by `π̄` on `L`
(`RowVanishesModPiN`). -/
lemma exists_saturatedLattice_encard_rowVanishesModPiN_le (u : Gf E 𝔰.κ)
    {y : S.LatticeStabilizerCoset → stdLevel E 𝔰.κ}
    (hy : ∀ φ : S.LatticeStabilizerCoset, (y φ : S.LatticeStabilizerCoset) = φ) {r l : ℕ}
    (h_rank : r + l = 𝔰.k)
    {L : Submodule (Ô E) (𝔰.κ → 𝔸f E)} (hL : IsLatticeOfRank r L) (h_le : L ≤ unimodularLattice u) :
    ∃ V : Submodule E (𝔰.κ → E),
      finrank E V = r ∧
      L ≤ saturatedLattice u.val.val_inv V ∧
      submoduleIndex L (saturatedLattice u.val.val_inv V) ≠ 0 ∧
      discriminant r L = sublatticeDiscriminant u.val.val_inv V *
        submoduleIndex L (saturatedLattice u.val.val_inv V) ∧
      {φ : S.LatticeStabilizerCoset | S.RowVanishesModPiN u (y φ) L}.encard ≤ ENNReal.ofReal
        (submoduleIndex L (saturatedLattice u.val.val_inv V) * (S.N ^ numInfPlaces E) ^ l) := by
  -- `L` has a basis `m A`, with `m` a basis of the saturated lattice; the index is `[det A]`.
  obtain ⟨V, A, rfl, hA, rfl, h_disc⟩ :
      ∃ (V : Submodule E (𝔰.κ → E)) (A : GL (Fin (finrank E V)) (𝔸f E)),
        finrank E V = r ∧ IsIntMatrix (Ô E) A.val ∧
        colLattice (Ô E) ((sublatticeBasis u.val.val_inv V).val * A.val) = L ∧
        discriminant r L = sublatticeDiscriminant u.val.val_inv V * genIndex A.val.det :=
    hL.exists_eq_colLattice_sublatticeBasis_mul u.val.val_inv h_le
  let m : Matrix 𝔰.κ (Fin (finrank E V)) (𝔸f E) := (sublatticeBasis u.val.val_inv V).val
  have hm : IsPrimitiveMatrix (Ô E) (u.val.inv * m) :=
    isPrimitiveMatrix_mul_sublatticeBasis u.val.val_inv V
  have h_inv : HasLeftInv m := by
    obtain ⟨p, -, hp⟩ := hm.right
    exact ⟨p * u.val.inv, by rw [Matrix.mul_assoc, hp]⟩
  have h_index : submoduleIndex (colLattice (Ô E) (m * A.val)) (saturatedLattice u.val.val_inv V) =
      genIndex A.val.det := submoduleIndex_colLattice_mul h_inv hA
  refine ⟨V, rfl, colLattice_mul_le m hA, ?_, by rw [h_index, h_disc], ?_⟩
  · exact Nat.cast_ne_zero.1 (h_index.trans_ne (genIndex_pos A.det).ne')
  · rw [h_index]
    exact encard_rowVanishesModPiN_le u hy h_rank hA

/-- Let `d, i ≥ 1` be real numbers with `d i ≤ H`, and let `r ≤ k`. Then `i (d i) ^ (-k)` is at most
`H ^ (μ + 2) d ^ (-k-1) i ^ (-r-μ)` for every `μ`. -/
lemma mul_inv_pow_le_of_mul_le {d i H : ℝ} (hd : 1 ≤ d) (hi : 1 ≤ i) (hH : d * i ≤ H) {r k : ℕ}
    (hr : r ≤ k) (μ : ℕ) :
    i * ((d * i) ^ k)⁻¹ ≤ H ^ (μ + 2) * ((d ^ (k + 1))⁻¹ * i⁻¹ ^ (r + μ)) := by
  have hi_le : i ≤ H := (le_mul_of_one_le_left (by positivity) hd).trans hH
  have hH_pos : 0 < H := by linarith
  calc i * ((d * i) ^ k)⁻¹
    _ = i * (d * i) ^ (μ + 1) * (d ^ (k + μ + 1) * i ^ (k + μ + 1))⁻¹ := by
      field
    _ ≤ H * H ^ (μ + 1) * (d ^ (k + 1) * i ^ (r + μ))⁻¹ := by
      have hd_pow : d ^ (k + 1) ≤ d ^ (k + μ + 1) := pow_le_pow_right₀ hd (by lia)
      have hi_pow : i ^ (r + μ) ≤ i ^ (k + μ + 1) := pow_le_pow_right₀ hi (by lia)
      gcongr
    _ = H ^ (μ + 2) * ((d ^ (k + 1))⁻¹ * i⁻¹ ^ (r + μ)) := by ring

/-- For a finite adelic unitary `u` and a subspace `V` of `E ^ κ`, the lattice of the adelic points
of `V` in `u Ô ^ κ` has discriminant at least `1`. -/
lemma one_le_sublatticeDiscriminant_unimodular (u : Gf E 𝔰.κ) (V : Submodule E (𝔰.κ → E)) :
    1 ≤ sublatticeDiscriminant u.val.val_inv V := by
  refine one_le_sublatticeDiscriminant u.val.val_inv V fun m hm ↦ ?_
  -- As `u⁻¹` is unitary, the Gram matrix of `m` is that of the integral matrix `u⁻¹ m`.
  have h_unitary : (u.val.inv)ᴴ * u.val.inv = 1 := by
    simpa [star_eq_conjTranspose] using mem_unitaryGroupOf_iff.1 u⁻¹.property
  have h_gram : (u.val.inv * m)ᴴ * (u.val.inv * m) = mᴴ * m := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ u.val.inv, h_unitary,
      Matrix.one_mul]
  rw [← h_gram]
  exact hm.conjTranspose.mul hm

/-- The weight of the subspace `V` of `E ^ κ`: it is `d ^ (-k-1)` if `V` has codimension `l`, with
`d` the discriminant of the lattice of the adelic points of `V` in `u Ô ^ κ`, and `0` otherwise. -/
abbrev subspaceDiscWeight (u : Gf E 𝔰.κ) (l : ℕ) (V : Submodule E (𝔰.κ → E)) : ℝ≥0∞ :=
  if finrank E V + l = 𝔰.k then ENNReal.ofReal (sublatticeDiscriminant u.1.val_inv V ^ (𝔰.k + 1))⁻¹
    else 0

omit [HasPrimitiveRoot5040 E] in
/-- Let `u` be in `Gf E 𝔰.κ`, let `y` assign an element `y φ` of `stdLevel E 𝔰.κ` to each coset `φ`
in `S.LatticeStabilizerCoset`, and let `L` be an `Ô`-submodule of `𝔸f E ^ 𝔰.κ`. The sum over these
cosets `φ` of the weights `S.discWeightIfRowVanishes u (y φ) r L` equals the number of cosets `φ`
for which the form of `y φ` vanishes on `L` modulo `piN`, times `(discriminant r L ^ 𝔰.k)⁻¹`. -/
lemma sum_discWeightIfRowVanishes_eq_encard_mul [Fintype S.LatticeStabilizerCoset] (u : Gf E 𝔰.κ)
    (y : S.LatticeStabilizerCoset → stdLevel E 𝔰.κ) (r : ℕ) (L : Submodule (Ô E) (𝔰.κ → 𝔸f E)) :
    ∑ φ : S.LatticeStabilizerCoset, S.discWeightIfRowVanishes u (y φ) r L =
      {φ : S.LatticeStabilizerCoset | S.RowVanishesModPiN u (y φ) L}.encard *
        ENNReal.ofReal (discriminant r L ^ 𝔰.k)⁻¹ := by
  rw [← tsum_set_const,
    _root_.tsum_subtype _ fun _ : S.LatticeStabilizerCoset ↦
      ENNReal.ofReal (discriminant r L ^ 𝔰.k)⁻¹,
    tsum_fintype]
  refine Finset.sum_congr rfl fun φ _ ↦ ?_
  by_cases h_kills : S.RowVanishesModPiN u (y φ) L <;> simp [discWeightIfRowVanishes, h_kills]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `S` be filling data over `E` with shape `𝔰`, and let `u` be in `Gf E 𝔰.κ`. The set
`S.LatticeStabilizerCoset` is the quotient of `stdLevel`, the group of integral unitary matrices on
`κ`, by its subgroup of matrices whose row `k₀` is congruent to that of `1` modulo `S.piN`. Let
`y φ` be an element of each such coset `φ`, and call row `k₀` of `(y φ)⁻¹ u⁻¹` the form of `φ`. Let
`k = #κ`, let `r + l = k`, and let `L` be a lattice of rank `r` in `u Ô ^ κ` with discriminant at
most `H`. Then `L` has a finite index `i` in the lattice of the adelic points in `u Ô ^ κ` of some
subspace `V`. Moreover, the sum of `(disc L) ^ (-k)` over the `φ` whose form vanishes on `L` modulo
`S.piN` is at most `(N ^ f) ^ l H ^ (μ + 2) * subspaceDiscWeight u l V * i ^ (-dim V - μ)`, for any
natural number `μ`. Here `subspaceDiscWeight u l V` is `d ^ (-k-1)` if `V` has codimension `l`, with
`d` the discriminant of that lattice of `V`, and `0` otherwise. `N` is the prime of `S`, `H` is
`discriminantBound` and `f` is the number of infinite places. -/
lemma exists_sum_discWeightIfRowVanishes_le [Fintype S.LatticeStabilizerCoset] (u : Gf E 𝔰.κ)
    {y : S.LatticeStabilizerCoset → stdLevel E 𝔰.κ}
    (hy : ∀ φ : S.LatticeStabilizerCoset, (y φ : S.LatticeStabilizerCoset) = φ)
    {r l : ℕ} (h_rank : r + l = 𝔰.k) (μ : ℕ) (L : S.BoundedDiscSublattice r (unimodularLattice u)) :
    ∃ V : Submodule E (𝔰.κ → E),
      (L.val ≤ saturatedLattice u.val.val_inv V ∧
        submoduleIndex L.val (saturatedLattice u.val.val_inv V) ≠ 0) ∧
      ∑ φ : S.LatticeStabilizerCoset, S.discWeightIfRowVanishes u (y φ) r L.val ≤
        ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (μ + 2)) *
          (subspaceDiscWeight u l V *
            (submoduleIndex L.val (saturatedLattice u.val.val_inv V) : ℝ≥0∞)⁻¹ ^
              (finrank E V + μ)) := by
  obtain ⟨L, hL, h_le, h_small⟩ := L
  -- At most `i (N ^ f) ^ l` forms vanish on `L`, and each of them contributes `(d i) ^ (-k)`.
  obtain ⟨V, rfl, h_sat, h_index, h_disc, h_forms⟩ :=
    exists_saturatedLattice_encard_rowVanishesModPiN_le u hy h_rank hL h_le
  refine ⟨V, ⟨h_sat, h_index⟩, ?_⟩
  set d : ℝ := sublatticeDiscriminant u.val.val_inv V
  set i : ℕ := submoduleIndex L (saturatedLattice u.val.val_inv V)
  have hd : 1 ≤ d := one_le_sublatticeDiscriminant_unimodular u V
  have hi : (1 : ℝ) ≤ i := Nat.one_le_cast.2 h_index.pos
  have hi_pos : (0 : ℝ) < i := one_pos.trans_le hi
  have h_di : d * i ≤ S.discriminantBound := h_disc.ge.trans h_small
  have h_exponents : i * ((d * i) ^ 𝔰.k)⁻¹ ≤
      S.discriminantBound ^ (μ + 2) * ((d ^ (𝔰.k + 1))⁻¹ * (i : ℝ)⁻¹ ^ (finrank E V + μ)) :=
    mul_inv_pow_le_of_mul_le hd hi h_di (Nat.le.intro h_rank) μ
  have discriminantBound_nonneg : 0 ≤ S.discriminantBound :=
    (hL.discriminant_pos.trans_le h_small).le
  calc ∑ φ : S.LatticeStabilizerCoset, S.discWeightIfRowVanishes u (y φ) (finrank E V) L
    _ = {φ : S.LatticeStabilizerCoset | S.RowVanishesModPiN u (y φ) L}.encard *
          ENNReal.ofReal ((d * i) ^ 𝔰.k)⁻¹ := by
      rw [sum_discWeightIfRowVanishes_eq_encard_mul, h_disc]
    _ ≤ ENNReal.ofReal (i * (S.N ^ numInfPlaces E) ^ l) * ENNReal.ofReal ((d * i) ^ 𝔰.k)⁻¹ := by
      gcongr
    _ = ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * (i * ((d * i) ^ 𝔰.k)⁻¹)) := by
      rw [← ENNReal.ofReal_mul (by positivity), mul_comm (i : ℝ), mul_assoc]
    _ ≤ ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (μ + 2) *
          ((d ^ (𝔰.k + 1))⁻¹ * (i : ℝ)⁻¹ ^ (finrank E V + μ))) := by
      grw [h_exponents, mul_assoc]
    _ = ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (μ + 2)) *
          (ENNReal.ofReal (d ^ (𝔰.k + 1))⁻¹ * ENNReal.ofReal (i : ℝ)⁻¹ ^ (finrank E V + μ)) := by
      rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (inv_pos.2 hi_pos).le,
        ← ENNReal.ofReal_mul (p := (d ^ (𝔰.k + 1))⁻¹) (by positivity)]
    _ = ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (μ + 2)) *
          (subspaceDiscWeight u l V * (i : ℝ≥0∞)⁻¹ ^ (finrank E V + μ)) := by
      rw [subspaceDiscWeight, ite_eq_left h_rank, ENNReal.ofReal_inv_of_pos hi_pos,
        ENNReal.ofReal_natCast]

/-- Let `u` be in the finite adelic unitary group `Gf E 𝔰.κ`, let `V` be a subspace of `E ^ 𝔰.κ`,
and let `Λ = saturatedLattice u.1.val_inv V` be the lattice of adelic points of `V` in `u Ô ^ 𝔰.κ`.
Here `𝔰.k = #𝔰.κ` is the size of the index set of the shape `𝔰`, and `𝔰.ϱ` is its number of
hyperbolic planes. The sum of `[Λ : M] ^ (-dim V - 2 𝔰.ϱ - 4)` over the sublattices `M` of finite
index in `Λ` is at most `2 ^ 𝔰.k`. The filling data `S : Filling E 𝔰` are used only for a bound on
the degree of `E` in terms of `𝔰.ϱ`. -/
lemma tsum_index_saturatedLattice_le (S : Filling E 𝔰) (u : Gf E 𝔰.κ) (V : Submodule E (𝔰.κ → E)) :
    ∑' M : {M : Submodule (Ô E) (𝔰.κ → 𝔸f E) // M ≤ saturatedLattice u.val.val_inv V ∧
        submoduleIndex M (saturatedLattice u.val.val_inv V) ≠ 0},
      (submoduleIndex M.val (saturatedLattice u.val.val_inv V) : ℝ≥0∞)⁻¹ ^
        (finrank E V + (2 * 𝔰.ϱ + 4)) ≤ 2 ^ 𝔰.k := by
  -- The sum is bounded by a power of the ideal zeta sum at `2 ϱ + 4`, which is at most `2`.
  have h_zeta_pow : idealZeta (Ô E) (2 * 𝔰.ϱ + 4) ^ (𝔰.ϱ + 1) ≤ ENNReal.ofReal (1 + 2⁻¹ ^ 0) := by
    simpa only [zero_add] using idealZeta_intAdeles_pow_le 0 S.mul_finrank_le_pow
  have h_zeta : idealZeta (Ô E) (2 * 𝔰.ϱ + 4) ≤ 2 := le_two_of_pow_le_ofReal h_zeta_pow
  have h_rank : finrank E V ≤ 𝔰.k := V.finrank_le.trans_eq (finrank_fintype_fun_eq_card E)
  calc _ ≤ idealZeta (Ô E) (2 * 𝔰.ϱ + 4) ^ finrank E V :=
      (isLatticeOfRank_saturatedLattice u.val.val_inv V).tsum_submoduleIndex_inv_pow_le _
    _ ≤ 2 ^ finrank E V := by gcongr
    _ ≤ 2 ^ 𝔰.k := pow_le_pow_right₀ one_le_two h_rank

/-! ### The sum over the forms and the lattices in a unimodular lattice -/

/-- Let `S` be filling data over the CM field `E` with shape `𝔰`, and let `u` be in the finite
adelic unitary group `Gf E 𝔰.κ`. The set `S.LatticeStabilizerCoset` is the quotient of `stdLevel`,
the group of integral unitary matrices on `κ`, by its subgroup of matrices whose row `k₀` is
congruent to that of `1` modulo `S.piN`. Let `y φ` be an element of each such coset `φ`, and call
row `k₀` of `(y φ)⁻¹ u⁻¹` the form of `φ`. Let `r + l = k = #κ`. Take the sum of `(disc L) ^ (-k)`
over the pairs of a coset `φ` and a lattice `L` of rank `r` in `u Ô ^ κ` with discriminant at most
`H` on which the form of `φ` vanishes modulo `S.piN`. This sum is at most `(N ^ f) ^ l H ^ (2 ϱ + 6)
(200 f k rd) ^ (f (k + 1) l) 2 ^ k`. Here `N` is the prime of `S`, `H` is `discriminantBound`, `ϱ`
is the number of hyperbolic planes of `𝔰`, `f` is the number of infinite places and `rd` is the root
discriminant of `E`. -/
lemma sum_tsum_discWeightIfRowVanishes_le [Fintype S.LatticeStabilizerCoset] (u : Gf E 𝔰.κ)
    {y : S.LatticeStabilizerCoset → stdLevel E 𝔰.κ}
    (hy : ∀ φ : S.LatticeStabilizerCoset, (y φ : S.LatticeStabilizerCoset) = φ)
    {r l : ℕ} (h_rank : r + l = 𝔰.k) :
    ∑ φ : S.LatticeStabilizerCoset, ∑' L : S.BoundedDiscSublattice r (unimodularLattice u),
        S.discWeightIfRowVanishes u (y φ) r L.val ≤
      ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2)) *
        (ENNReal.ofReal ((200 * (numInfPlaces E * 𝔰.k) * rootDiscr E) ^
          (numInfPlaces E * (𝔰.k + 1) * l)) * 2 ^ 𝔰.k) := by
  -- Each `L` is a sublattice of finite index in the saturated lattice of some subspace `V`. Sort
  -- the `L` by `V`, and sum first over the sublattices and then over the subspaces.
  set C : ℝ≥0∞ :=
    ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2))
  let Sub (V : Submodule E (𝔰.κ → E)) : Type :=
    {M : Submodule (Ô E) (𝔰.κ → 𝔸f E) // M ≤ saturatedLattice u.val.val_inv V ∧
      submoduleIndex M (saturatedLattice u.val.val_inv V) ≠ 0}
  let w (V : Submodule E (𝔰.κ → E)) (M : Sub V) : ℝ≥0∞ :=
    (submoduleIndex M.1 (saturatedLattice u.1.val_inv V) : ℝ≥0∞)⁻¹ ^ (finrank E V + (2 * 𝔰.ϱ + 4))
  have h_span (L : S.BoundedDiscSublattice r (unimodularLattice u)) :
      ∃ (V : Submodule E (𝔰.κ → E)) (M : Sub V), M.val = L.val ∧
        ∑ φ : S.LatticeStabilizerCoset, S.discWeightIfRowVanishes u (y φ) r L.val ≤ C *
          (subspaceDiscWeight u l V * w V M) := by
    obtain ⟨V, h_sub, h_term⟩ := exists_sum_discWeightIfRowVanishes_le u hy h_rank (2 * 𝔰.ϱ + 4) L
    exact ⟨V, ⟨L.val, h_sub⟩, rfl, h_term⟩
  choose span M hM h_term using h_span
  let sort (L : S.BoundedDiscSublattice r (unimodularLattice u)) : Σ V : Submodule E (𝔰.κ → E),
    Sub V :=
    ⟨span L, M L⟩
  have h_sort : Function.Injective sort := by
    intro L L' h
    have h_eq : (sort L).snd.val = (sort L').snd.val := by rw [h]
    exact Subtype.ext (by rwa [← hM L, ← hM L'])
  calc _ = ∑' L : S.BoundedDiscSublattice r (unimodularLattice u), ∑ φ : S.LatticeStabilizerCoset,
          S.discWeightIfRowVanishes u (y φ) r L.val :=
      (Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable).symm
    _ ≤ ∑' L : S.BoundedDiscSublattice r (unimodularLattice u),
          C * (subspaceDiscWeight u l (span L) * w (span L) (M L)) := tsum_le_tsum h_term
    _ ≤ ∑' p : Σ V : Submodule E (𝔰.κ → E), Sub V, C * (subspaceDiscWeight u l p.1 * w p.1 p.2) :=
      tsum_comp_le_tsum_of_injective h_sort fun p ↦ C * (subspaceDiscWeight u l p.1 * w p.1 p.2)
    _ = C * ∑' V : Submodule E (𝔰.κ → E), subspaceDiscWeight u l V * ∑' M : Sub V, w V M := by
      simp only [tsum_sigma', ENNReal.tsum_mul_left]
    _ ≤ C * ((∑' V : Submodule E (𝔰.κ → E), subspaceDiscWeight u l V) * 2 ^ 𝔰.k) := by
      rw [← ENNReal.tsum_mul_right]
      gcongr with V
      exact S.tsum_index_saturatedLattice_le u V
    _ ≤ _ := by
      gcongr
      -- The weight vanishes off the subspaces of codimension `l`.
      have h_support : Function.support (subspaceDiscWeight u l) ⊆
          {V : Submodule E (𝔰.κ → E) | finrank E V + l = Fintype.card 𝔰.κ} :=
        fun V hV ↦ of_not_not fun h_codim ↦ hV (ite_eq_right h_codim)
      have h_weight (V : {V : Submodule E (𝔰.κ → E) // finrank E V + l = Fintype.card 𝔰.κ}) :
          subspaceDiscWeight u l V.val = ENNReal.ofReal
            (sublatticeDiscriminant u.val.val_inv V.val ^ (𝔰.k + 1))⁻¹ :=
        ite_eq_left V.property
      rw [← tsum_subtype_eq_of_support_subset h_support]
      exact (tsum_congr h_weight).trans_le (tsum_sublatticeDiscriminant_inv_le u l)

end Forms

/-! ### The constants and the sum over all classes -/

omit [HasPrimitiveRoot5040 E] in
/-- The number `S.tailScale = b ^ (k f / 4)` is nonnegative, as the size parameter `b` is. Here
`k = |κ|` and `f` is the number of infinite places of `E`. -/
lemma tailScale_nonneg (S : Filling E 𝔰) : 0 ≤ S.tailScale := by
  have hb : 0 < S.b := by linarith [S.thousand_le_b]
  rw [tailScale]
  positivity

/-- For every natural number `ϱ`, with `n = ϱ + 1`, the number `1 + n ^ 3 (2 ϱ + 6) + 1` is at
most `10 ^ 5 n ^ 9`. This bounds an exponent of the size parameter in
`pow_mul_discriminantBound_pow_le`. -/
lemma add_mul_succ_pow_three_le (ϱ : ℕ) :
    1 + (ϱ + 1) ^ 3 * (2 * ϱ + 4 + 2) + 1 ≤ 10 ^ 5 * (ϱ + 1) ^ 9 := by
  have h_one : 1 ≤ (ϱ + 1) ^ 9 := Nat.one_le_pow _ _ ϱ.succ_pos
  have h_linear : 2 * ϱ + 4 + 2 ≤ 6 * (ϱ + 1) := by lia
  have h_cube : (ϱ + 1) ^ 3 ≤ (ϱ + 1) ^ 8 := by gcongr; lia
  calc 1 + (ϱ + 1) ^ 3 * (2 * ϱ + 4 + 2) + 1
    _ ≤ (ϱ + 1) ^ 9 + (ϱ + 1) ^ 8 * (6 * (ϱ + 1)) + (ϱ + 1) ^ 9 := by gcongr
    _ = 8 * (ϱ + 1) ^ 9 := by ring
    _ ≤ 10 ^ 5 * (ϱ + 1) ^ 9 := Nat.mul_le_mul_right _ (by norm_num)

section

omit [HasPrimitiveRoot5040 E]

/-- Let `S` be filling data that satisfy the standing hypotheses `IsAdmissible`. The product
`b ^ f H ^ (2 ϱ + 6) 2 ^ k` is at most `tailScale = b ^ (k f / 4)`. Here `b` is the size parameter
of `S`, `k = #κ`, `f` is the number of infinite places of `E`, and
`H = discriminantBound = b ^ (n ^ 3 f)` with `n = ϱ + 1`. -/
lemma pow_mul_discriminantBound_pow_le (S : Filling E 𝔰) :
    S.b ^ numInfPlaces E * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2) * 2 ^ 𝔰.k ≤ S.tailScale := by
  have hb : 2 ≤ S.b := by linarith [S.thousand_le_b]
  have discriminantBound_nonneg : 0 ≤ S.discriminantBound := pow_nonneg (zero_le_two.trans hb) _
  have h_two : (2 : ℝ) ^ 𝔰.k ≤ S.b ^ numInfPlaces E :=
    (by gcongr : (2 : ℝ) ^ 𝔰.k ≤ S.b ^ 𝔰.k).trans (pow_le_pow_right₀ S.one_le_b S.k_le_f)
  have h_exponent : 1 + 𝔰.n ^ 3 * (2 * 𝔰.ϱ + 4 + 2) + 1 ≤ 10 ^ 5 * 𝔰.n ^ 9 :=
    add_mul_succ_pow_three_le 𝔰.ϱ
  calc S.b ^ numInfPlaces E * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2) * 2 ^ 𝔰.k
    _ ≤ S.b ^ numInfPlaces E * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2) * S.b ^ numInfPlaces E := by
      gcongr
    _ = S.b ^ ((1 + 𝔰.n ^ 3 * (2 * 𝔰.ϱ + 4 + 2) + 1) * numInfPlaces E) := by
      rw [discriminantBound]
      ring
    _ ≤ S.tailScale := pow_le_tailScale (Nat.mul_le_mul_right _ h_exponent)

/-- Let `S` be filling data that satisfy the standing hypotheses `IsAdmissible`, among them
`N ≤ b ^ (60 (ϱ + 1))`. The product `N ^ f (200 f k rd) ^ (f (k + 1))` is at most
`tailScale = b ^ (k f / 4)`. Here `N` is the prime and `b` the size parameter of `S`, `k = #κ`, `f`
is the number of infinite places and `rd` the root discriminant of `E`. -/
lemma pow_mul_mul_rootDiscr_pow_le_tailScale (S : Filling E 𝔰) [S.IsAdmissible] :
    S.N ^ numInfPlaces E *
      (200 * (numInfPlaces E * 𝔰.k) * rootDiscr E) ^ (numInfPlaces E * (𝔰.k + 1)) ≤
      S.tailScale := by
  -- Compare the thousandth powers, which are bounded by powers of `b`.
  have hb : 0 < S.b := by linarith [S.thousand_le_b]
  have h_exponent : 60 * 𝔰.n * 1000 + (𝔰.k + 1) ≤ 250 * 𝔰.k := by
    have hk : 1000 * (2 * 𝔰.ϱ + 2) ≤ 𝔰.k := S.thousand_mul_le_k
    lia
  refine le_of_pow_le_pow_left₀ (n := 1000) (by norm_num) S.tailScale_nonneg ?_
  set X : ℝ := 200 * (numInfPlaces E * 𝔰.k) * rootDiscr E
  calc (S.N ^ numInfPlaces E * X ^ (numInfPlaces E * (𝔰.k + 1))) ^ 1000
    _ = (S.N ^ 1000 * (X ^ 1000) ^ (𝔰.k + 1)) ^ numInfPlaces E := by
      simp only [mul_pow, ← pow_mul]
      ring
    _ ≤ ((S.b ^ (60 * 𝔰.n)) ^ 1000 * S.b ^ (𝔰.k + 1)) ^ numInfPlaces E := by
      gcongr
      exacts [IsAdmissible.N_le, S.mul_rootDiscr_pow_le]
    _ ≤ (S.b ^ (250 * 𝔰.k)) ^ numInfPlaces E := by
      rw [← pow_mul, ← pow_add]
      gcongr
      exact S.one_le_b
    _ = (S.b ^ (𝔰.k * numInfPlaces E)) ^ 250 := by ring
    _ = S.tailScale ^ 1000 := by rw [← tailScale_pow_four, ← pow_mul]

/-- Let `S` be filling data that satisfy the standing hypotheses `IsAdmissible`, among them
`N ≤ b ^ (60 (ϱ + 1))`. For every `l`, the constant `(N ^ f) ^ l H ^ (2 ϱ + 6) (200 f
k rd) ^ (f (k + 1) l) 2 ^ k` of `sum_tsum_discWeightIfRowVanishes_le` is at most
`tailScale ^ (l + 1) / b ^ f`. Here `N` is the prime and `b` the size parameter of `S`, `k = #κ`,
`f` is the number of infinite places and `rd` the root discriminant of `E`,
`H = discriminantBound = b ^ ((ϱ + 1) ^ 3 f)` and `tailScale = b ^ (k f / 4)`. -/
lemma mul_rootDiscr_pow_le_tailScale_pow_div (S : Filling E 𝔰) [S.IsAdmissible] (l : ℕ) :
    (S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2) *
        ((200 * (numInfPlaces E * 𝔰.k) * rootDiscr E) ^ (numInfPlaces E * (𝔰.k + 1) * l) *
          2 ^ 𝔰.k) ≤
      S.tailScale ^ (l + 1) / S.b ^ numInfPlaces E := by
  have hb : 0 < S.b := by linarith [S.thousand_le_b]
  have h_rd : 0 < rootDiscr E := rootDiscr_pos E
  have hτ : 0 ≤ S.tailScale := S.tailScale_nonneg
  rw [le_div_iff₀ (by positivity)]
  calc _ = S.b ^ numInfPlaces E * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2) * 2 ^ 𝔰.k *
        (S.N ^ numInfPlaces E *
          (200 * (numInfPlaces E * 𝔰.k) * rootDiscr E) ^ (numInfPlaces E * (𝔰.k + 1))) ^ l := by
        rw [pow_mul _ _ l]
        ring
    _ ≤ S.tailScale * S.tailScale ^ l := by
      gcongr
      · exact S.pow_mul_discriminantBound_pow_le
      · exact S.pow_mul_mul_rootDiscr_pow_le_tailScale
    _ = S.tailScale ^ (l + 1) := by ring

end

/-- **Lattices of given corank.** Let `S` be filling data, with prime `N = π π̄` and size parameter
`b`, that satisfy the standing hypotheses `IsAdmissible`; those used are the form of the level,
`N ≤ b ^ (60 (ϱ + 1))`, the lower bounds `1000 ≤ b` and `5 ≤ N`, and a lower bound for an index. Let
`k₀ = 𝔰.k₀` be the distinguished index in `κ` given by the shape `𝔰`, and let `r + l = k = #κ`. For
a class `c` in the double coset space `S.Classes` of `U(X₀)`, with chosen representative `g`, the
lattice `classLatticeX₀ c` consists of the adelic vectors `v` such that `g⁻¹ v` is integral with
entry `k₀` divisible by `π̄`. Take the sum of `(disc L) ^ (-k)` over all `c` and all lattices `L` of
rank `r` in that lattice with `disc L ≤ discriminantBound = b ^ ((ϱ + 1) ^ 3 f)`. This sum is at
most `tailScale ^ (l + 1)` times the number of classes divided by `N ^ (k f)`. -/
theorem sum_discriminant_inv_le {S : Filling E 𝔰} [S.IsAdmissible] {r l : ℕ}
    (h_rank : r + l = 𝔰.k) :
    ∑ c : S.Classes, ∑' L : {L : Submodule (Ô E) (𝔰.κ → 𝔸f E) // IsLatticeOfRank r L ∧
        L ≤ S.classLatticeX₀ c ∧ discriminant r L ≤ S.discriminantBound},
      ENNReal.ofReal (discriminant r L.val ^ 𝔰.k)⁻¹ ≤
      .ofReal (card S.Classes / S.N ^ (𝔰.k * numInfPlaces E) * S.tailScale ^ (l + 1)) := by
  -- The mean over the classes is a mean over `u` of the mean over the lattice stabilizer cosets
  -- `φ`, of which there are at least `(N ^ k / b) ^ f`.
  have hb : 0 < S.b := by linarith [S.thousand_le_b]
  have hN : (0 : ℝ) < S.N := by linarith [S.five_le_N]
  have hτ : 0 ≤ S.tailScale := S.tailScale_nonneg
  have discriminantBound_nonneg : 0 ≤ S.discriminantBound := pow_nonneg hb.le _
  have h_rd : 0 < rootDiscr E := rootDiscr_pos E
  have h_card : (S.N ^ 𝔰.k / S.b) ^ numInfPlaces E ≤ (Nat.card S.LatticeStabilizerCoset : ℝ) :=
    IsAdmissible.le_relIndex
  have h_card_pos : (0 : ℝ) < Nat.card S.LatticeStabilizerCoset := h_card.trans_lt' (by positivity)
  let : Fintype S.LatticeStabilizerCoset :=
    Subgroup.fintypeOfIndexNeZero (Nat.cast_pos.1 h_card_pos).ne'
  rw [mul_comm_div]
  refine sum_classes_le_of_sum_translates_le (fun φ : S.LatticeStabilizerCoset ↦ φ.out.val) _
    (by positivity) fun u ↦ ?_
  have h_rep : ∀ φ : S.LatticeStabilizerCoset, ∃ (η : U (stdSpace E 𝔰.κ).J) (y : stdLevel E 𝔰.κ),
      (y : S.LatticeStabilizerCoset) = φ ∧
        (⟦u * φ.out⟧ : S.Classes).out = (stdSpace E 𝔰.κ).embFin η * u * y :=
    exists_mk_out_eq_embFin_mul u
  choose η y hy h_out using h_rep
  calc ∑ φ : S.LatticeStabilizerCoset, ∑' L :
         S.BoundedDiscSublattice r (S.classLatticeX₀ ⟦u * φ.out⟧),
        ENNReal.ofReal (discriminant r L.val ^ 𝔰.k)⁻¹
    _ ≤ ∑ φ : S.LatticeStabilizerCoset, ∑' L : S.BoundedDiscSublattice r (unimodularLattice u),
          S.discWeightIfRowVanishes u (y φ) r L.val :=
      Finset.sum_le_sum fun φ _ ↦ tsum_discriminant_inv_le_of_out_eq (h_out φ) r
    _ ≤ ENNReal.ofReal ((S.N ^ numInfPlaces E) ^ l * S.discriminantBound ^ (2 * 𝔰.ϱ + 4 + 2) *
          ((200 * (numInfPlaces E * 𝔰.k) * rootDiscr E) ^ (numInfPlaces E * (𝔰.k + 1) * l) *
            2 ^ 𝔰.k)) := by
      refine (sum_tsum_discWeightIfRowVanishes_le u hy h_rank).trans_eq ?_
      simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow two_pos.le,
        ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (S.tailScale ^ (l + 1) / S.b ^ numInfPlaces E) :=
      ENNReal.ofReal_le_ofReal (S.mul_rootDiscr_pow_le_tailScale_pow_div l)
    _ = ENNReal.ofReal ((S.N ^ 𝔰.k / S.b) ^ numInfPlaces E *
          (S.tailScale ^ (l + 1) / S.N ^ (𝔰.k * numInfPlaces E))) := by
      congr 1
      rw [div_pow, ← pow_mul]
      field_simp
    _ ≤ ENNReal.ofReal
          (card S.LatticeStabilizerCoset *
            (S.tailScale ^ (l + 1) / S.N ^ (𝔰.k * numInfPlaces E))) := by
      grw [h_card, Nat.card_eq_fintype_card]

end CrudeLattices

end New.Filling

end
end
end

/-!
# The sum over pairs of near terms

For a fixed class `c`, a pair of near terms over a block `(c, s, c')` is sorted by its label, a
component of `s` in the reduced image of the Bessel subgroup, and by its common lattice. Over a
given lattice and label there are few terms, and the sum over the lattices is bounded.

The main notions used in the statements:
* a class `c : S.Classes` is a double coset of the unitary group of the definite space `X₀` at the
  finite adeles, with representative `h_c`;
* a block is a triple `(c, s, c')`, with `s` in the finite group `S.ResidueGL`. A rational isometry
  `γ` is a term over it if `h_c⁻¹ γ h_c'` is integral with reduction `s`;
* `S.IsNearPairOverAgreeingBlock c c' q`: the two terms in `q` are near, are the chosen
  representatives of their double cosets, have a cell rank, and lie over one block `(c, s, c')`
  whose `s` agrees (`S.Agrees s`);
* `commonLink γ γ'`: the subspace of `X₀` that two terms have in common; its dimension is the rank
  of their common lattice `L₁₂ = S.pairLattice c c' γ γ'`, which has corank `l` if this dimension is
  `k - l`;
* `S.termLattice c c' γ`: the lattice `L_γ ⊆ Λ ∩ X₀` of a term, where `Λ` is the adelic lattice of
  the class `c` and `Λ ∩ X₀` is `S.classLatticeX₀ c`.

The main result is `New.Filling.sum_pairDiscriminant_inv_le`.
-/

@[expose] public section

namespace New.Filling

open NumberField Matrix Module Fintype ENNReal Pointwise

variable {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- If every index `i` is related by `R` to some `y` of the same weight, and at most `x` indices are
related to each `y`, then the sum over the indices is at most `x` times the sum over the `y`. -/
lemma tsum_le_tsum_mul_of_encard_le {I Y : Type} {v : I → ℝ≥0∞} {w : Y → ℝ≥0∞} {x : ℝ≥0∞}
    (R : I → Y → Prop) (h_cover : ∀ i : I, ∃ y : Y, R i y ∧ v i = w y)
    (h_fibre : ∀ y : Y, {i : I | R i y}.encard ≤ x) : ∑' i : I, v i ≤ (∑' y : Y, w y) * x := by
  choose chosenY h_over h_weight using h_cover
  calc ∑' i, v i = ∑' y, ∑' i : chosenY ⁻¹' {y}, v i := (tsum_fiberwise v chosenY).symm
    _ ≤ ∑' y, w y * x := tsum_le_tsum fun y ↦ by
      have h_const (i : chosenY ⁻¹' {y}) : v i = w y := by
        rw [h_weight i, show chosenY i = y from i.property]
      have h_subset : chosenY ⁻¹' {y} ⊆ {i : I | R i y} :=
        fun i (hi : chosenY i = y) ↦ by simpa [hi] using h_over i
      rw [tsum_congr h_const, tsum_set_const, mul_comm]
      grw [h_subset, h_fibre]
    _ = (∑' y, w y) * x := ENNReal.tsum_mul_right

/-- For positive `n` and `l ≤ n ^ 3`, twice the exponent `2000 n ^ 6 (l + 1) f` in the
count of the terms over a lattice is at most `10 ^ 5 n ^ 9 f`. -/
lemma two_mul_count_exponent_le {n f l : ℕ} (hn : 0 < n) (hl : l ≤ n ^ 3) :
    2 * (2000 * n ^ 6 * (l + 1) * f) ≤ 10 ^ 5 * n ^ 9 * f := by
  have h_cube : 1 ≤ n ^ 3 := Nat.pow_pos hn
  have h_corank : n ^ 6 * (l + 1) * f ≤ n ^ 6 * (n ^ 3 + n ^ 3) * f := by gcongr
  linarith [Nat.zero_le (n ^ 9 * f)]

variable (S) in
/-- The terms `γ` and `γ'` from the class `c'` to the class `c` both have the label `t`
(`S.IsNearTermAt`), and their common lattice `S.pairLattice c c' γ γ'` is a lattice in `Λ ∩ X₀` that
lies in the lattices `S.termLattice` of both terms and whose rank is the dimension of
`commonLink γ γ'`, the subspace of `X₀` that the terms share. -/
structure IsLabelledPair (c c' : S.Classes) (t : S.reducedImage besselS) (γ γ' : S.G E) : Prop where
  /-- The first term is near and has the label `t`. -/
  isNearTermAt_left : S.IsNearTermAt c t (c', γ)
  /-- The second term is near and has the label `t`. -/
  isNearTermAt_right : S.IsNearTermAt c t (c', γ')
  /-- The common lattice lies in the lattice of the first term. -/
  le_termLattice_left : S.pairLattice c c' γ γ' ≤ S.termLattice c c' γ
  /-- The common lattice lies in the lattice of the second term. -/
  le_termLattice_right : S.pairLattice c c' γ γ' ≤ S.termLattice c c' γ'
  /-- The common lattice lies in `Λ ∩ X₀`. -/
  le_classLatticeX₀ : S.pairLattice c c' γ γ' ≤ S.classLatticeX₀ c
  /-- The rank of the common lattice is the dimension of the subspace that the terms share. -/
  isLatticeOfRank : IsLatticeOfRank (finrank E (commonLink γ γ')) (S.pairLattice c c' γ γ')

/-- Let `E` be a CM field with a primitive 5040th root of unity, `S` admissible filling data of
shape `𝔰` over `E`, and `c`, `c'` classes. A near pair consists of two rational isometries `γ`, `γ'`
that are near, chosen in their double cosets and of some cell rank, and lie over one block
`(c, s, c')`: both `h_c⁻¹ γ h_c'` and `h_c⁻¹ γ' h_c'` are integral with the same reduction `s`,
which agrees (`S.Agrees s`). Such a pair has a common label `t`, and the lattices `S.termLattice` of
both terms contain their common lattice `S.pairLattice c c' γ γ'`. This is a lattice in
`Λ ∩ X₀ = S.classLatticeX₀ c`. -/
lemma exists_isLabelledPair_of_isNearPairOverAgreeingBlock {c c' : S.Classes}
    {γ γ' : S.G E} (h_pair : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) :
    ∃ t : S.reducedImage besselS, S.IsLabelledPair c c' t γ γ' := by
  obtain ⟨⟨h_near, h_level⟩, ⟨h_near', h_level'⟩, s, hs, h_over, h_over'⟩ := h_pair
  -- The label is that of the block `(c, s, c')` over which both terms lie. The common lattice is
  -- cut out of the intersection of the lattices of the two terms, each of which lies in `Λ ∩ X₀`.
  have h_le_inf : S.pairLattice c c' γ γ' ≤ S.termLattice c c' γ ⊓ S.termLattice c c' γ' :=
    inf_le_right
  exact ⟨(Subgroup.groupEquivQuotientProdSubgroup s).2,
    { isNearTermAt_left := ⟨⟨h_near, _, h_level⟩, s, h_over, rfl⟩
      isNearTermAt_right := ⟨⟨h_near', _, h_level'⟩, s, h_over', rfl⟩
      le_termLattice_left := h_le_inf.trans inf_le_left
      le_termLattice_right := h_le_inf.trans inf_le_right
      le_classLatticeX₀ := (h_le_inf.trans inf_le_left).trans inf_le_left
      isLatticeOfRank := isLatticeOfRank_pairLattice hs h_over h_over' h_level h_level' }⟩

variable (S) in
/-- The lattices `L ⊆ Λ ∩ X₀` of rank `r` with discriminant at most `S.discriminantBound`. -/
abbrev ClassBoundedDiscLattice (c : S.Classes) (r : ℕ) : Type :=
  {L : Submodule (Ô E) (𝔰.κ → 𝔸f E) // IsLatticeOfRank r L ∧
    L ≤ S.classLatticeX₀ c ∧ discriminant r L ≤ S.discriminantBound}

variable (S) in
/-- The near pairs over a block `(c, s, c')` with agreeing `s`
(`S.IsNearPairOverAgreeingBlock c c'`) whose common lattice has corank `l` and discriminant at most
`S.discriminantBound`. -/
def boundedDiscNearPairs (l : ℕ) (c c' : S.Classes) : Set (S.G E × S.G E) :=
  {q : S.G E × S.G E | S.IsNearPairOverAgreeingBlock c c' q ∧
    finrank E (commonLink q.1 q.2) + l = 𝔰.k ∧
    S.pairDiscriminant c c' q.1 q.2 ≤ S.discriminantBound}

/-- Let `E` be a CM field with a primitive 5040th root of unity and `f` infinite places, `S`
admissible filling data of shape `𝔰` over `E` with size parameter `b = S.b`, and `c` a class, with
adelic lattice `Λ`. Let `n = 𝔰.n`, let `k = 𝔰.k` be the dimension of the definite space `X₀`, and
let `l ≤ n³`, `r + l = k`. A near pair over `(c, c')` is two near, chosen terms over one block
`(c, s, c')` with `s` agreeing; its common lattice `L₁₂ ⊆ Λ ∩ X₀` has rank the dimension of the
subspace of `X₀` that the terms share, and corank `l` if this rank is `r`. The sum of
`(disc L₁₂) ^ (-k)` over all classes `c'` and all such pairs with corank `l` and discriminant at
most `S.discriminantBound = b ^ (n³ f)` is at most the number of labels, times the sum of
`(disc L) ^ (-k)` over the lattices `L ⊆ Λ ∩ X₀` of rank `r` with the same bound on the
discriminant, times `S.tailScale = b ^ (k f / 4)`. -/
lemma sum_pairDiscriminant_inv_le_tsum [S.IsAdmissible] {c : S.Classes} {r l : ℕ}
    (hl_le : l ≤ 𝔰.n ^ 3) (h_rank : r + l = 𝔰.k) :
    ∑ c' : S.Classes, ∑' q : S.boundedDiscNearPairs l c c',
        ENNReal.ofReal (S.pairDiscriminant c c' q.val.fst q.val.snd ^ 𝔰.k)⁻¹ ≤
      Nat.card (S.reducedImage besselS) *
        (∑' L : S.ClassBoundedDiscLattice c r,
          ENNReal.ofReal (discriminant r (L : Submodule (Ô E) (𝔰.κ → 𝔸f E)) ^ 𝔰.k)⁻¹) *
        ENNReal.ofReal S.tailScale := by
  -- Send a pair to its label and common lattice. Both of its terms then lie in the set `terms` of
  -- this label and lattice, so each fibre has at most as many elements as the square of that set.
  let terms : S.reducedImage besselS × S.ClassBoundedDiscLattice c r → Set (S.Classes × S.G E) :=
    fun (t, L) ↦ {p | S.IsNearTermAt c t p ∧ L.val ≤ S.termLattice c p.1 p.2}
  let termPair : (Σ c' : S.Classes, S.boundedDiscNearPairs l c c') →
      (S.Classes × S.G E) × S.Classes × S.G E
    | ⟨c', (γ, γ'), _⟩ => ((c', γ), (c', γ'))
  have h_inj : Function.Injective termPair := by
    rintro ⟨c', ⟨γ, γ'⟩, h_mem⟩ ⟨c'', ⟨δ, δ'⟩, h_mem'⟩ h_eq
    obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ : (c' = c'' ∧ γ = δ) ∧ c' = c'' ∧ γ' = δ' := by
      simpa only [termPair, Prod.mk.injEq] using h_eq
    rfl
  rw [← tsum_fintype (L := .unconditional _), ← tsum_sigma]
  refine (tsum_le_tsum_mul_of_encard_le (x := .ofReal S.tailScale)
    (w := fun (_, L) ↦ .ofReal (discriminant r L.val ^ 𝔰.k)⁻¹)
    (fun i y ↦ termPair i ∈ terms y ×ˢ terms y) ?_ ?_).trans_eq ?_
  · -- Both terms of a pair have the label of its block, and their lattices contain the common one.
    rintro ⟨c', ⟨γ, γ'⟩, h_pair, h_link, h_disc⟩
    obtain rfl : r = finrank E (commonLink γ γ') := Nat.add_right_cancel (h_rank.trans h_link.symm)
    obtain ⟨t, ht⟩ : ∃ t : S.reducedImage besselS, S.IsLabelledPair c c' t γ γ' :=
      exists_isLabelledPair_of_isNearPairOverAgreeingBlock h_pair
    let L : S.ClassBoundedDiscLattice c (finrank E (commonLink γ γ')) :=
      ⟨S.pairLattice c c' γ γ', ht.isLatticeOfRank, ht.le_classLatticeX₀, h_disc⟩
    have h_left : (c', γ) ∈ terms (t, L) := ⟨ht.isNearTermAt_left, ht.le_termLattice_left⟩
    have h_right : (c', γ') ∈ terms (t, L) := ⟨ht.isNearTermAt_right, ht.le_termLattice_right⟩
    exact ⟨(t, L), Set.mk_mem_prod h_left h_right, rfl⟩
  · -- The number of choices for both terms is at most the square of the count over a lattice.
    rintro ⟨t, L, hL, h_le, h_disc⟩
    let termsOverL : Set (S.Classes × S.G E) := terms (t, ⟨L, hL, h_le, h_disc⟩)
    let exponent : ℕ := 2000 * 𝔰.n ^ 6 * (l + 1) * numInfPlaces E
    have h_exponent : 2 * exponent ≤ 10 ^ 5 * 𝔰.n ^ 9 * numInfPlaces E :=
      two_mul_count_exponent_le 𝔰.ϱ.succ_pos hl_le
    have h_terms : termsOverL.encard ≤ ENNReal.ofReal (S.b ^ exponent) :=
      encard_setOf_isNearTermAt_and_le_termLattice_le t h_rank hL h_le h_disc
    calc ((termPair ⁻¹' (termsOverL ×ˢ termsOverL)).encard : ℝ≥0∞)
        ≤ (termsOverL ×ˢ termsOverL).encard := mod_cast Set.encard_le_encard_of_injOn
          (Set.mapsTo_preimage termPair (termsOverL ×ˢ termsOverL)) h_inj.injOn
      _ ≤ .ofReal (S.b ^ exponent) * .ofReal (S.b ^ exponent) := by
          grw [Set.encard_prod, ENat.toENNReal_mul, h_terms]
      _ = .ofReal (S.b ^ (2 * exponent)) := by
          rw [← ofReal_mul (pow_nonneg (zero_le_one.trans S.one_le_b) exponent), ← pow_add, two_mul]
      _ ≤ .ofReal S.tailScale := ofReal_le_ofReal (pow_le_tailScale h_exponent)
  · simp [tsum_prod', ENat.card_eq_coe_natCard]

/-- **Count.** Let `E` be a CM field with a primitive 5040th root of unity and `f` infinite places,
and let `S` be admissible filling data of shape `𝔰` over `E`, with size parameter `b = S.b` and
prime `N = S.N`. Let `n = 𝔰.n`, let `k = 𝔰.k` be the dimension of the definite space `X₀`, and let
`l ≤ n³`. For classes `c`, `c'` a near pair is two near, chosen terms over one block `(c, s, c')`
with `s` agreeing; its common lattice `L₁₂` is a lattice in `X₀` of rank the dimension of the
subspace that the terms share, and has corank `l` if this rank is `k - l`. The sum of
`(disc L₁₂) ^ (-k)` over all `c`, `c'` and all such pairs with corank `l` and discriminant at most
`S.discriminantBound = b ^ (n³ f)` is at most `tailScale ^ (l + 2) * pairCountScale`. Here
`tailScale = b ^ (k f / 4)`, and `pairCountScale` is the number of labels times the number of
classes, divided by `N ^ (k f)`. -/
theorem sum_pairDiscriminant_inv_le [S.IsAdmissible] {l : ℕ} (hl_le : l ≤ 𝔰.n ^ 3) :
    ∑ c : S.Classes, ∑ c' : S.Classes, ∑' q : S.boundedDiscNearPairs l c c',
        ENNReal.ofReal (S.pairDiscriminant c c' q.val.fst q.val.snd ^ 𝔰.k)⁻¹ ≤
      ENNReal.ofReal (S.tailScale ^ (l + 2) * S.pairCountScale) := by
  obtain h_corank_gt | h_corank_le := lt_or_ge 𝔰.k l
  · -- No lattice has corank above `k`, so the sum is empty.
    have h_empty (c c' : S.Classes) : IsEmpty (S.boundedDiscNearPairs l c c') := by
      refine ⟨fun ⟨q, h_pair, h_link, h_disc⟩ ↦ ?_⟩
      have h_le : l ≤ 𝔰.k := Nat.le_of_add_left_le h_link.le
      exact h_corank_gt.not_ge h_le
    simp only [tsum_empty, Finset.sum_const_zero, zero_le]
  obtain ⟨r, h_rank⟩ : ∃ r : ℕ, r + l = 𝔰.k := ⟨𝔰.k - l, Nat.sub_add_cancel h_corank_le⟩
  have h_tailScale_nonneg : 0 ≤ S.tailScale := Real.rpow_nonneg (zero_le_one.trans S.one_le_b) _
  let ratio : ℝ := card S.Classes / S.N ^ (𝔰.k * numInfPlaces E)
  calc _ ≤ ∑ c : S.Classes, Nat.card (S.reducedImage besselS) *
         (∑' L : S.ClassBoundedDiscLattice c r,
          ENNReal.ofReal (discriminant r L.val ^ 𝔰.k)⁻¹) * .ofReal S.tailScale :=
        Finset.sum_le_sum fun c _ ↦ sum_pairDiscriminant_inv_le_tsum hl_le h_rank
    _ ≤ Nat.card (S.reducedImage besselS) * .ofReal (ratio * S.tailScale ^ (l + 1)) *
          .ofReal S.tailScale := by
        grw [← Finset.sum_mul, ← Finset.mul_sum, sum_discriminant_inv_le h_rank]
    _ = .ofReal (S.tailScale ^ (l + 2) * S.pairCountScale) := by
        rw [← ofReal_natCast, ← ofReal_mul (by positivity), ← ofReal_mul (by positivity),
          pairCountScale]
        congr 1
        ring

end New.Filling
end
end

/-!
# The remaining terms: a bound for their sum

Size, gain and count are combined: pairs of terms that do not lie in the same link class contribute
at most `b ^ (-k f) 𝒟_id`, and pairs in the same link class gain the norm of the places at which the
block meets.

* `New.Filling.sum_termSize_mul_le`: sets of near pairs, one for each two classes, with
  `τ ^ (l + 6) D η ^ (-k) ≤ B` contribute at most `τ B` in all. Here `l` is the corank of the common
  lattice, the gain `η` is such that `(d η)²` is at most the product of the two gauges for the
  discriminant `d` of that lattice, and `D` bounds the second moments of both cell ranks.
* `New.Filling.sum_termSize_mul_not_inSameLinkClass_le`: pairs with different links, or with equal
  links and `𝗀 = 0`, contribute at most `b ^ (-k f) 𝒟_id`.
* `New.Filling.sum_termSize_mul_inSameLinkClass_le`: pairs with equal links and `𝗀 ≠ 0` over blocks
  that meet at places of total norm at least `z` contribute at most `(b ^ (2 f) / z) ^ k 𝒟_main`.
* `New.Filling.secondMoment_remainingTerms_le`, `New.Filling.linkSecondMoment_le_of_le_meetNorm`:
  the resulting bounds for the second moment of the remaining terms.

Here `b = S.b` is the scale, `M = S.M` the congruence level, `k = 𝔰.k` and `n = 𝔰.n` are sizes of
the shape, `f` is the number of infinite places, `τ = S.tailScale = b ^ (k f / 4)` is the number
whose powers may be lost, `𝗀 = S.termDisc`, `𝒟_id = S.identitySecondMoment` and
`𝒟_main = S.mainSecondMoment`.

Notions from other files:
* `S.cellRank γ`: the cell rank of a rational element `γ`, the index of its cell.
* `S.termsOver c s c'`: the rational elements that are integral in the position given by the classes
  `c`, `c'` and have reduction `s`; the triple `(c, s, c')` is called a block.
* `S.IsNearPairOverAgreeingBlock c c' q`: both terms of `q` are near, are the chosen elements of
  their orbits, have a cell rank, and lie over one block `(c, s, c')` whose `s` agrees
  (`S.Agrees s`).
* `S.pairDiscriminant c c' γ γ'`: the discriminant of the common lattice `L₁₂` of two terms, a
  lattice in `commonLink γ γ'`; its corank is `k - finrank E (commonLink γ γ')`.
* `S.termSize c c' γ`: the bound `τ² (D_j / (n_p G ^ k)) ^ (1 / 2)` for the orbit of `γ`, with the
  second moment `D_j = S.cellRankSecondMoment j`, the gauge `G = S.levelGauge j c c' γ` and
  `n_p = S.pairCountScale`.

## Relation to the literature

The second moment of the Poincaré series expands over pairs of rational elements congruent mod `M`.
Discriminant gains, lattice counts and a weighted Schur test show that degenerate terms and pairs
with different links are negligible, and that the remaining terms shrink where frames meet mod `M`,
which isolates the main term. Discarding small cells and off-diagonal terms of Petersson-type and
relative trace formulas by congruences and counts is known in the literature. Related work:
Michel–Ramakrishnan–Yang, Bessel periods on U(2,1)×U(1,1), 2023; Kowalski–Saha–Tsimerman, Local
spectral equidistribution for Siegel modular forms, 2012; Blomer, Density theorems for GL(n), 2023.
-/

@[expose] public section

open ENNReal Fin Finset Module

namespace New.Filling

/-- A term `γ` over the classes `c`, `c'` determines the reduction `s` of its block `(c, s, c')`. -/
lemma eq_of_mem_termsOver {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    {c c' : S.Classes} {γ : S.G E} {s s' : S.ResidueGL}
    (h : γ ∈ S.termsOver c s c') (h' : γ ∈ S.termsOver c s' c') : s = s' := by
  obtain ⟨k : S.latticeStabilizer, rfl, hk : k.val = S.translateByClassReps c c' γ⟩ := h
  obtain ⟨k' : S.latticeStabilizer, rfl, hk' : k'.val = S.translateByClassReps c c' γ⟩ := h'
  rw [Subtype.ext (hk.trans hk'.symm)]

/-- The common lattice of a near pair (two near representative terms over one block whose `s`
agrees) has discriminant at least `1`. -/
lemma IsNearPairOverAgreeingBlock.one_le_pairDiscriminant {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] {c c' : S.Classes} {q : S.G E × S.G E}
    (hq : S.IsNearPairOverAgreeingBlock c c' q) : 1 ≤ S.pairDiscriminant c c' q.1 q.2 := by
  obtain ⟨⟨-, h_cell⟩, ⟨-, h_cell'⟩, s, h_agrees, h_over, h_over'⟩ := hq
  exact Filling.one_le_pairDiscriminant h_agrees h_over h_over' h_cell h_cell'

/-- For a near pair `(γ, γ')`, the square of the discriminant of the common lattice is at most
`(2 / M) ^ (2 i f)` times the product of the two gauges, where `i` is the codimension in each link
(`New.link`) of the intersection of the links, `M = S.M` is the congruence level and `f` is the
number of infinite places. -/
lemma IsNearPairOverAgreeingBlock.pairDiscriminant_sq_le {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E]
    {c c' : S.Classes} {γ γ' : S.G E} (hq : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) :
    S.pairDiscriminant c c' γ γ' ^ 2 ≤
      (2 / S.M) ^ (2 * S.linkCorank γ γ' * numInfPlaces E) *
        (S.levelGauge (S.cellRank γ) c c' γ * S.levelGauge (S.cellRank γ') c c' γ') := by
  obtain ⟨⟨-, h_cell⟩, ⟨-, h_cell'⟩, s, h_agrees, h_over, h_over'⟩ := hq
  simpa only [ite_self, Nat.cast_one, mul_one] using
    Filling.pairDiscriminant_sq_le h_agrees (one_le_meetNorm s) h_over h_over' h_cell h_cell'

-- Absorb the congruence gain into the discriminant before comparing the two gauges.
private lemma IsNearPairOverAgreeingBlock.scaled_pairDiscriminant_sq_le
    {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E]
    {c c' : S.Classes} {γ γ' : S.G E}
    (hq : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) :
    (S.pairDiscriminant c c' γ γ' * ((S.M : ℝ) / 2) ^ (S.linkCorank γ γ' * numInfPlaces E)) ^ 2 ≤
      S.levelGauge (S.cellRank γ) c c' γ * S.levelGauge (S.cellRank γ') c c' γ' := by
  have hM : 2 ≤ S.M := two_le_M
  rw [mul_pow, ← pow_mul, ← le_div_iff₀ (by positivity), div_eq_mul_inv, ← inv_pow, inv_div,
    mul_comm, Nat.mul_comm (_ * _) 2, ← Nat.mul_assoc]
  exact hq.pairDiscriminant_sq_le

/-- Let `S` be data of the filling theorem that satisfy the standing hypotheses `S.IsAdmissible`.
Let `(γ, γ')` be a near pair over the classes `c`, `c'`. Its common lattice has corank at most `n³`
and discriminant at most `S.discriminantBound = b ^ (n³ f)`. -/
lemma IsNearPairOverAgreeingBlock.corank_le_and_pairDiscriminant_le {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {c c' : S.Classes} {γ γ' : S.G E} (hq : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) :
    𝔰.k - finrank E (commonLink γ γ') ≤ 𝔰.n ^ 3 ∧
    S.pairDiscriminant c c' γ γ' ≤ S.discriminantBound := by
  -- With `i` the corank of the links and `d` the discriminant, the gain and the bound for the
  -- gauges give `(M / 2) ^ (i f) * d ≤ b ^ (n³ f)`, where `d ≥ 1` and `M / 2 ≥ b ^ 18`.
  set j : Fin (𝔰.ϱ + 2) := S.cellRank γ
  set j' : Fin (𝔰.ϱ + 2) := S.cellRank γ'
  set i : ℕ := S.linkCorank γ γ'
  set d : ℝ := S.pairDiscriminant c c' γ γ'
  have h_one_le_d : 1 ≤ d := hq.one_le_pairDiscriminant
  have h_gain := hq.scaled_pairDiscriminant_sq_le
  obtain ⟨⟨⟨h_near, -⟩, h_cell⟩, ⟨⟨h_near', -⟩, h_cell'⟩, s, -, h_over, h_over'⟩ := hq
  have h_corank : 𝔰.k ≤ finrank E (commonLink γ γ') + i + (j - 𝔰.ϱ) :=
    le_finrank_commonLink_add h_cell γ'
  have h_bound := (levelGauge_pos h_over' h_cell').le.trans (h_near'.levelGauge_le h_over' h_cell')
  have hb₂ : 2 ≤ S.b := two_le_b
  have h_ratio : S.b ^ 18 ≤ (S.M : ℝ) / 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc
      S.b ^ 18 * 2 ≤ S.b ^ 19 := by grw [hb₂, ← pow_succ]
      _ ≤ (S.M : ℝ) := S.le_M
  have h_pow_mul_disc_le : S.b ^ (18 * i * numInfPlaces E) * d ≤ S.discriminantBound := by
    rw [Nat.mul_assoc, pow_mul, mul_comm]
    grw [h_ratio]
    apply le_of_sq_le_sq _ h_bound
    rw [sq S.discriminantBound]
    exact h_gain.trans (mul_le_mul (h_near.levelGauge_le h_over h_cell)
      (h_near'.levelGauge_le h_over' h_cell') (levelGauge_pos h_over' h_cell').le h_bound)
  refine ⟨?_,
    (le_mul_of_one_le_left (by positivity) (one_le_pow₀ S.one_le_b)).trans h_pow_mul_disc_le⟩
  have h_exp : 18 * i * numInfPlaces E ≤ 𝔰.n ^ 3 * numInfPlaces E :=
    (pow_le_pow_iff_right₀ (by linarith : 1 < S.b)).1
      ((le_mul_of_one_le_right (by positivity) h_one_le_d).trans h_pow_mul_disc_le)
  have h_codim : 18 * i ≤ 𝔰.n ^ 3 := Nat.le_of_mul_le_mul_right h_exp NeZero.one_le
  lia

/-- A near pair (two near representative terms over one block whose `s` agrees) lies in
`S.boundedDiscNearPairs l c c'`, the set of near pairs of corank `l` and bounded discriminant, for
`l` the corank of its common lattice. -/
lemma IsNearPairOverAgreeingBlock.mem_boundedDiscNearPairs {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] [S.IsAdmissible] {c c' : S.Classes}
    {γ γ' : S.G E} (hq : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) :
    (γ, γ') ∈ S.boundedDiscNearPairs (𝔰.k - finrank E (commonLink γ γ')) c c' :=
  have h_rank : finrank E (commonLink γ γ') ≤ 𝔰.k :=
    (Submodule.finrank_le _).trans (by simp)
  ⟨hq, Nat.add_sub_cancel' h_rank, hq.corank_le_and_pairDiscriminant_le.right⟩

/-- Let `S` be data of the filling theorem and let `c`, `c'` be classes and `γ` a rational point of
cell rank `j = S.cellRank γ` whose gauge `G = S.levelGauge j c c' γ` is positive. If the constant
`S.cellRankSecondMoment j` is at most `D`, then the square of the size `S.termSize c c' γ` is at
most `τ⁴ D / (n_p G ^ k)`. -/
lemma termSize_sq_le {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    {c c' : S.Classes} {γ : S.G E} {D : ℝ}
    (h_gauge_pos : 0 < S.levelGauge (S.cellRank γ) c c' γ)
    (hD : S.cellRankSecondMoment (S.cellRank γ) ≤ D) :
    S.termSize c c' γ ^ 2 ≤
      S.tailScale ^ 4 * D / (S.pairCountScale * S.levelGauge (S.cellRank γ) c c' γ ^ 𝔰.k) := by
  have h_pairCountScale_pos : 0 < S.pairCountScale := pairCountScale_pos
  have h_moment_nonneg : 0 ≤ S.cellRankSecondMoment (S.cellRank γ) :=
    cellRankSecondMoment_nonneg _
  rw [termSize, orbitBound, ← levelGauge, mul_pow, Real.sq_sqrt (by positivity)]
  grw [hD]
  exact le_of_eq (by ring)

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `S` be data of the filling theorem.
Let `(γ, γ')` be a near pair over the classes `c`, `c'` and `d` the discriminant of its common
lattice `S.pairLattice`. Let `η > 0`. If `(d η)²` is at most the product of the two gauges and the
constants `S.cellRankSecondMoment` of both cell ranks are at most `D`, then the product of the sizes
`S.termSize` is at most `τ⁴ D η ^ (-k) d ^ (-k) / n_p`. -/
lemma IsNearPairOverAgreeingBlock.termSize_mul_le {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] {c c' : S.Classes}
    {γ γ' : S.G E} (hq : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) {η D : ℝ} (hη : 0 < η)
    (h_gain : (S.pairDiscriminant c c' γ γ' * η) ^ 2 ≤
      S.levelGauge (S.cellRank γ) c c' γ * S.levelGauge (S.cellRank γ') c c' γ')
    (hD : S.cellRankSecondMoment (S.cellRank γ) ≤ D)
    (hD' : S.cellRankSecondMoment (S.cellRank γ') ≤ D) :
    S.termSize c c' γ * S.termSize c c' γ' ≤
      S.tailScale ^ 4 * D / η ^ 𝔰.k / S.pairCountScale *
        (S.pairDiscriminant c c' γ γ' ^ 𝔰.k)⁻¹ := by
  set d : ℝ := S.pairDiscriminant c c' γ γ'
  set G : ℝ := S.levelGauge (S.cellRank γ) c c' γ
  set G' : ℝ := S.levelGauge (S.cellRank γ') c c' γ'
  have h_one_le_d : 1 ≤ d := hq.one_le_pairDiscriminant
  obtain ⟨⟨-, h_cell⟩, ⟨-, h_cell'⟩, s, -, h_over, h_over'⟩ := hq
  have hD₀ : 0 ≤ D := (cellRankSecondMoment_nonneg _).trans hD
  have h_pairCountScale_pos : 0 < S.pairCountScale := pairCountScale_pos
  have hG : 0 < G := levelGauge_pos h_over h_cell
  have hG' : 0 < G' := levelGauge_pos h_over' h_cell'
  refine le_of_sq_le_sq ?_ (by positivity)
  calc
    _ = S.termSize c c' γ ^ 2 * S.termSize c c' γ' ^ 2 := mul_pow ..
    _ ≤ S.tailScale ^ 4 * D / (S.pairCountScale * G ^ 𝔰.k) *
        (S.tailScale ^ 4 * D / (S.pairCountScale * G' ^ 𝔰.k)) := by
      grw [termSize_sq_le hG hD, termSize_sq_le hG' hD']
    _ = (S.tailScale ^ 4 * D / S.pairCountScale) ^ 2 / (G * G') ^ 𝔰.k := by ring
    _ ≤ (S.tailScale ^ 4 * D / S.pairCountScale) ^ 2 / ((d * η) ^ 2) ^ 𝔰.k := by gcongr
    _ = _ := by ring

/-- Let `S` be data of the filling theorem.
Let `(γ, γ')` be a near pair over the classes `c`, `c'`, whose common lattice `S.pairLattice` has
corank `l = k - finrank E (commonLink γ γ')` and discriminant `d = S.pairDiscriminant c c' γ γ'`.
Let `η > 0`. Suppose that `(d η)²` is at most the product of the two gauges, `D` bounds the
constants `S.cellRankSecondMoment` of both cell ranks, and `τ ^ (l + 6) D η ^ (-k) ≤ B`. Then the
product of the sizes `S.termSize` is at most `B d ^ (-k) / (τ ^ (l + 2) n_p)`. -/
lemma IsNearPairOverAgreeingBlock.ofReal_termSize_mul_le {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] {c c' : S.Classes}
    {γ γ' : S.G E} (hq : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) {η D B : ℝ} (hη : 0 < η)
    (h_gain : (S.pairDiscriminant c c' γ γ' * η) ^ 2 ≤
      S.levelGauge (S.cellRank γ) c c' γ * S.levelGauge (S.cellRank γ') c c' γ')
    (hD : S.cellRankSecondMoment (S.cellRank γ) ≤ D)
    (hD' : S.cellRankSecondMoment (S.cellRank γ') ≤ D)
    (h_budget : S.tailScale ^ (𝔰.k - finrank E (commonLink γ γ') + 6) * D / η ^ 𝔰.k ≤ B) :
    ENNReal.ofReal (S.termSize c c' γ * S.termSize c c' γ') ≤
      .ofReal (B / (S.tailScale ^ (𝔰.k - finrank E (commonLink γ γ') + 2) * S.pairCountScale)) *
        .ofReal (S.pairDiscriminant c c' γ γ' ^ 𝔰.k)⁻¹ := by
  set l : ℕ := 𝔰.k - finrank E (commonLink γ γ')
  have hτ : 0 < S.tailScale := zero_lt_one.trans_le one_le_tailScale
  have h_pairCountScale_pos : 0 < S.pairCountScale := pairCountScale_pos
  have h_one_le_disc : 1 ≤ S.pairDiscriminant c c' γ γ' := hq.one_le_pairDiscriminant
  have h_const : S.tailScale ^ 4 * D / η ^ 𝔰.k / S.pairCountScale ≤
      B / (S.tailScale ^ (l + 2) * S.pairCountScale) :=
    calc
      _ = S.tailScale ^ (l + 6) * D / η ^ 𝔰.k / (S.tailScale ^ (l + 2) * S.pairCountScale) := by
        field
      _ ≤ _ := by gcongr
  grw [← ofReal_mul' (by positivity), hq.termSize_mul_le hη h_gain hD hD', h_const]

/-- The number `n³ + 1` of possible coranks is at most `τ = S.tailScale`. -/
lemma cube_add_one_le_tailScale {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰) :
    ((𝔰.n ^ 3 + 1 : ℕ) : ℝ) ≤ S.tailScale := by
  have hb : 2 ≤ S.b := two_le_b
  calc
    _ = (𝔰.n : ℝ) ^ 3 + 1 := by norm_cast
    _ ≤ S.b ^ 3 + S.b ^ 3 := by grw [S.succ_le_b, one_le_pow₀ (n := 3) S.one_le_b]
    _ ≤ S.b ^ 4 := by grw [← two_mul, hb, ← pow_succ']
    _ ≤ S.tailScale := pow_le_tailScale (le_mul_of_le_of_one_le (by lia) NeZero.one_le)

/-- Let `S` be data of the filling theorem that satisfy the standing hypotheses `S.IsAdmissible`.
For all classes `c`, `c'` let `P c c'` be a set of near pairs over `c`, `c'`. Suppose that for each
pair, with a common lattice of corank `l` and discriminant `d`, there are `η > 0` and `D` such that
`(d η)²` is at most the product of the two gauges, `D` bounds the constants `S.cellRankSecondMoment`
of both cell ranks, and `τ ^ (l + 6) D η ^ (-k) ≤ B`, where `τ = S.tailScale`, `k = 𝔰.k` and
`B ≥ 0`. Then the products of the sizes `S.termSize` of the two terms add up to at most `τ B`. -/
lemma sum_termSize_mul_le {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [HasPrimitiveRoot5040 E] [S.IsAdmissible] (P : S.Classes → S.Classes → Set (S.G E × S.G E))
    (h_nearPair : ∀ c c' : S.Classes, ∀ q ∈ P c c', S.IsNearPairOverAgreeingBlock c c' q)
    {B : ℝ} (hB : 0 ≤ B)
    (h_gain : ∀ (c c' : S.Classes) (γ γ' : S.G E), (γ, γ') ∈ P c c' → ∃ η D : ℝ, 0 < η ∧
      (S.pairDiscriminant c c' γ γ' * η) ^ 2 ≤
        S.levelGauge (S.cellRank γ) c c' γ * S.levelGauge (S.cellRank γ') c c' γ' ∧
      S.cellRankSecondMoment (S.cellRank γ) ≤ D ∧
      S.cellRankSecondMoment (S.cellRank γ') ≤ D ∧
      S.tailScale ^ (𝔰.k - finrank E (commonLink γ γ') + 6) * D / η ^ 𝔰.k ≤ B) :
    ∑ c : S.Classes, ∑ c' : S.Classes, ∑' q : P c c', ENNReal.ofReal
        (S.termSize c c' (q : S.G E × S.G E).1 * S.termSize c c' (q : S.G E × S.G E).2) ≤
      .ofReal (S.tailScale * B) := by
  -- Sort the pairs by the corank `l ≤ n³`. By the count each value of `l` contributes at most `B`.
  have hτ : 0 < S.tailScale := zero_lt_one.trans_le one_le_tailScale
  have h_pairCountScale_pos : 0 < S.pairCountScale := pairCountScale_pos
  let weight (l : ℕ) (c c' : S.Classes) (q : S.G E × S.G E) : ℝ≥0∞ :=
    .ofReal (B / (S.tailScale ^ (l + 2) * S.pairCountScale)) *
      .ofReal (S.pairDiscriminant c c' q.1 q.2 ^ 𝔰.k)⁻¹
  have h_pair (c c' : S.Classes) (q : S.G E × S.G E) (hq : q ∈ P c c') :
      ENNReal.ofReal (S.termSize c c' q.1 * S.termSize c c' q.2) ≤
        ∑ l ∈ range (𝔰.n ^ 3 + 1), (S.boundedDiscNearPairs l c c').indicator (weight l c c') q := by
    obtain ⟨η, D, hη, h_sq, hD, hD', h_budget⟩ := h_gain c c' q.1 q.2 hq
    have hq_near : S.IsNearPairOverAgreeingBlock c c' (q.1, q.2) := h_nearPair c c' q hq
    set l : ℕ := 𝔰.k - finrank E (commonLink q.1 q.2)
    have hl : l ≤ 𝔰.n ^ 3 := hq_near.corank_le_and_pairDiscriminant_le.left
    calc
      _ ≤ weight l c c' q := hq_near.ofReal_termSize_mul_le hη h_sq hD hD' h_budget
      _ = (S.boundedDiscNearPairs l c c').indicator (weight l c c') q :=
        (Set.indicator_of_mem hq_near.mem_boundedDiscNearPairs _).symm
      _ ≤ _ := single_le_sum (f := fun l ↦
        (S.boundedDiscNearPairs l c c').indicator (weight l c c') q)
        (fun _ _ ↦ zero_le) (mem_range_succ_iff.2 hl)
  have h_corank (l : ℕ) (hl : l ∈ range (𝔰.n ^ 3 + 1)) :
      ∑ c, ∑ c', ∑' q : S.boundedDiscNearPairs l c c', weight l c c' q ≤ .ofReal B := by
    simp only [weight, ENNReal.tsum_mul_left, ← mul_sum]
    calc
      _ ≤ ENNReal.ofReal (B / (S.tailScale ^ (l + 2) * S.pairCountScale)) *
          .ofReal (S.tailScale ^ (l + 2) * S.pairCountScale) := by
        grw [sum_pairDiscriminant_inv_le (mem_range_succ_iff.1 hl)]
      _ = .ofReal B := by rw [← ofReal_mul (by positivity), div_mul_cancel₀ _ (by positivity)]
  calc
    _ ≤ ∑ c, ∑ c', ∑ l ∈ range (𝔰.n ^ 3 + 1),
        ∑' q : S.boundedDiscNearPairs l c c', weight l c c' q := by
      gcongr with c _ c' _
      -- Bound each pair by its weights, then extend the sum from `P c c'` to all pairs.
      simp only [_root_.tsum_subtype]
      rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
      refine (tsum_le_tsum fun q : P c c' ↦ h_pair c c' q q.property).trans ?_
      exact tsum_comp_le_tsum_of_injective Subtype.val_injective fun q ↦
        ∑ l ∈ range (𝔰.n ^ 3 + 1), (S.boundedDiscNearPairs l c c').indicator (weight l c c') q
    _ = ∑ l ∈ range (𝔰.n ^ 3 + 1), ∑ c, ∑ c',
        ∑' q : S.boundedDiscNearPairs l c c', weight l c c' q := by
          simp only [sum_comm (t := range _)]
    _ ≤ ∑ _l ∈ range (𝔰.n ^ 3 + 1), .ofReal B := sum_le_sum h_corank
    _ = .ofReal ((𝔰.n ^ 3 + 1 : ℕ) * B) := by
      rw [Finset.sum_const, card_range, nsmul_eq_mul, ofReal_mul (Nat.cast_nonneg _),
        ofReal_natCast]
    _ ≤ .ofReal (S.tailScale * B) := by grw [S.cube_add_one_le_tailScale]

/-- Two terms lie in the same link class if `𝗀 = S.termDisc` vanishes for neither and their links
(`New.link`) are equal. -/
def InSameLinkClass {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰)
    (γ γ' : S.G E) : Prop :=
  S.termDisc γ ≠ 0 ∧ S.termDisc γ' ≠ 0 ∧ link γ = link γ'

/-- Let `S` be data of the filling theorem that satisfy the standing hypotheses `S.IsAdmissible`.
The second moment `S.cellRankSecondMoment j` of every cell rank `j` is at most `S.mainSecondMoment`,
the second moment of the top cell rank `ϱ + 1`. -/
lemma cellRankSecondMoment_le_mainSecondMoment {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [S.IsAdmissible] (j : Fin (𝔰.ϱ + 2)) :
    S.cellRankSecondMoment j ≤ S.mainSecondMoment := by
  have h_id : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have hτ : 1 ≤ S.tailScale := one_le_tailScale
  unfold cellRankSecondMoment
  split_ifs
  · rfl
  · calc
      S.identitySecondMoment / S.tailScale ^ 16 ≤ S.identitySecondMoment :=
        div_le_self h_id (one_le_pow₀ hτ)
      _ ≤ S.tailScale ^ 44 * S.identitySecondMoment := le_mul_of_one_le_left h_id (one_le_pow₀ hτ)
      _ ≤ S.mainSecondMoment := tailScale_pow_mul_identitySecondMoment_le

/-- Let `E` be a CM field, and let `S` be data of the filling theorem over `E` that satisfy the
standing hypotheses `S.IsAdmissible`. For `i ≥ 1` and `l ≤ i + 1` we have `τ ^ (l + 6) 𝒟_main
(M / 2) ^ (-i f k) ≤ τ ^ (-10) 𝒟_id`. This serves pairs whose links intersect in codimension `i` and
whose common lattice has corank `l`. -/
lemma pow_mul_mainSecondMoment_div_le {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [ok : S.IsAdmissible] {i l : ℕ} (hi : i ≠ 0) (hl : l ≤ i + 1) :
    S.tailScale ^ (l + 6) * S.mainSecondMoment / ((S.M / 2) ^ (i * numInfPlaces E)) ^ 𝔰.k ≤
      S.identitySecondMoment / S.tailScale ^ 10 := by
  -- Each unit of `i` gives the factor `x = τ (2 / M) ^ (k f) ≤ 1`; one such factor and the upper
  -- bound for `𝒟_main / 𝒟_id` give `τ ^ 7 x 𝒟_main ≤ τ ^ 8 (2 / b ^ 6) ^ (k f) 𝒟_id`.
  have hb : 2 ≤ S.b := two_le_b
  have hτ : 1 ≤ S.tailScale := one_le_tailScale
  have hM : 2 ≤ S.M := two_le_M
  have h_main : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  have h_id : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  set m : ℕ := 𝔰.k * numInfPlaces E
  set x : ℝ := S.tailScale * (2 / S.M) ^ m with hx
  have h_ratio : 2 * S.b ≤ S.M :=
    calc
      2 * S.b ≤ S.b ^ 2 := by grw [hb, ← sq]
      _ ≤ S.b ^ 19 := pow_le_pow_right₀ S.one_le_b (by norm_num)
      _ ≤ (S.M : ℝ) := S.le_M
  have hx_le : x ≤ 1 :=
    calc x ≤ S.tailScale ^ 4 * (2 / S.M) ^ m := by grw [hx, ← le_self_pow₀ hτ four_ne_zero]
      _ = (2 * S.b / S.M) ^ m := by
        rw [tailScale_pow_four]
        ring
      _ ≤ 1 := pow_le_one₀ (by positivity) (div_le_one_of_le₀ h_ratio (by positivity))
  calc
    _ ≤ S.tailScale ^ (i + 1 + 6) * S.mainSecondMoment / ((S.M / 2) ^ (i * numInfPlaces E)) ^
      𝔰.k := by
      gcongr
    _ = S.tailScale ^ 7 * x ^ i * S.mainSecondMoment := by
      rw [hx, ← inv_div 2 (S.M : ℝ), inv_pow, inv_pow, div_inv_eq_mul]
      ring
    _ ≤ S.tailScale ^ 7 * x * ((S.M / S.b ^ 6) ^ m * S.identitySecondMoment) := by
      grw [pow_le_of_le_one (by positivity) hx_le hi, ok.mainSecondMoment_le]
    _ = (S.tailScale ^ 4) ^ 2 * (2 / S.b ^ 6) ^ m * S.identitySecondMoment := by
      simp only [hx, div_pow]
      field_simp
    _ ≤ (S.tailScale ^ 4) ^ 2 * (S.b / S.b ^ 6) ^ m * S.identitySecondMoment := by gcongr
    _ = S.identitySecondMoment / (S.tailScale ^ 4) ^ 3 := by
      rw [tailScale_pow_four, div_pow]
      field
    _ ≤ S.identitySecondMoment / S.tailScale ^ 10 := by
      grw [← pow_mul, pow_le_pow_right₀ hτ (by norm_num : 10 ≤ 4 * 3)]

/-- **Remaining terms, pairs that do not lie in the same link class.** Let `E` be a CM field with a
primitive root of unity of order 5040, and let `S` be data of the filling theorem over `E` that
satisfy the standing hypotheses `S.IsAdmissible`. Sum over all classes `c`, `c'` and all near pairs
over them whose links (`New.link`) differ or for one of which `𝗀 = S.termDisc` vanishes. The
products of the sizes of the two terms add up to at most `b ^ (-k f) 𝒟_id`. -/
theorem sum_termSize_mul_not_inSameLinkClass_le {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] [S.IsAdmissible] :
    ∑ c : S.Classes, ∑ c' : S.Classes,
      ∑' q : {q : S.G E × S.G E |
        S.IsNearPairOverAgreeingBlock c c' q ∧ ¬S.InSameLinkClass q.1 q.2},
        ENNReal.ofReal
          (S.termSize c c' (q : S.G E × S.G E).1 * S.termSize c c' (q : S.G E × S.G E).2) ≤
      .ofReal (S.identitySecondMoment / S.b ^ (𝔰.k * numInfPlaces E)) := by
  -- Apply `sum_termSize_mul_le` with `B = τ ^ (-10) 𝒟_id`, according to the corank of the links.
  have hM : 2 ≤ S.M := two_le_M
  have hτ : 1 ≤ S.tailScale := one_le_tailScale
  have h_id : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_const : S.tailScale * (S.identitySecondMoment / S.tailScale ^ 10) ≤
      S.identitySecondMoment / S.b ^ (𝔰.k * numInfPlaces E) :=
    calc
      _ = S.identitySecondMoment / S.tailScale ^ 9 := by field_simp
      _ ≤ S.identitySecondMoment / S.tailScale ^ 4 := by
        grw [pow_le_pow_right₀ hτ (by norm_num : 4 ≤ 9)]
      _ = _ := by rw [tailScale_pow_four]
  have hB : 0 ≤ S.identitySecondMoment / S.tailScale ^ 10 := by positivity
  refine (sum_termSize_mul_le (fun c c' ↦ {q : S.G E × S.G E |
      S.IsNearPairOverAgreeingBlock c c' q ∧ ¬S.InSameLinkClass q.1 q.2})
    (fun c c' q hq ↦ hq.left) hB ?_).trans (ofReal_le_ofReal h_const)
  rintro c c' γ γ' ⟨hq, h_class : ¬S.InSameLinkClass γ γ'⟩
  set j : Fin (𝔰.ϱ + 2) := S.cellRank γ
  set j' : Fin (𝔰.ϱ + 2) := S.cellRank γ'
  set i : ℕ := S.linkCorank γ γ'
  have h_gain := hq.scaled_pairDiscriminant_sq_le
  obtain ⟨⟨-, h_cell : S.HasCellRank j γ⟩, ⟨-, h_cell' : S.HasCellRank j' γ'⟩, -⟩ := hq
  have h_corank : 𝔰.k ≤ finrank E (commonLink γ γ') + i + (j - 𝔰.ϱ) :=
    le_finrank_commonLink_add h_cell γ'
  rcases eq_or_ne i 0 with hi | hi
  · -- Equal links: `𝗀` vanishes for both terms, so both lie below the top cell rank, corank `0`.
    have h_link : link γ = link γ' := linkCorank_eq_zero_iff.1 hi
    have h_both : S.termDisc γ = 0 ↔ S.termDisc γ' = 0 :=
      termDisc_eq_zero_iff_of_link_eq h_cell h_cell' h_link
    have h_disc : S.termDisc γ = 0 :=
      by_contra fun h_ne ↦ h_class ⟨h_ne, mt h_both.2 h_ne, h_link⟩
    have h_low : ¬𝔰.ϱ < j := fun h_top ↦ h_cell.lt_iff_termDisc_ne_zero.1 h_top h_disc
    have h_low' : ¬𝔰.ϱ < j' := fun h_top ↦
      h_cell'.lt_iff_termDisc_ne_zero.1 h_top (h_both.1 h_disc)
    have h_full : 𝔰.k - finrank E (commonLink γ γ') = 0 := by lia
    have h_one : (S.pairDiscriminant c c' γ γ' * 1) ^ 2 ≤
        S.levelGauge j c c' γ * S.levelGauge j' c c' γ' := by
      simpa [show S.linkCorank γ γ' = 0 from hi] using h_gain
    have h_moment : S.cellRankSecondMoment j = S.identitySecondMoment / S.tailScale ^ 16 :=
      ite_eq_right h_low
    have h_moment' : S.cellRankSecondMoment j' = S.identitySecondMoment / S.tailScale ^ 16 :=
      ite_eq_right h_low'
    refine ⟨1, S.identitySecondMoment / S.tailScale ^ 16, one_pos, h_one, h_moment.le, h_moment'.le,
      le_of_eq ?_⟩
    rw [h_full, one_pow, zero_add]
    field_simp
  · -- Different links: the gain is `(M / 2) ^ (i f)`, and the corank is at most `i + 1`.
    have h_corank_le : 𝔰.k - finrank E (commonLink γ γ') ≤ i + 1 := by lia
    exact ⟨(S.M / 2) ^ (i * numInfPlaces E), S.mainSecondMoment, by positivity, h_gain,
      cellRankSecondMoment_le_mainSecondMoment j, cellRankSecondMoment_le_mainSecondMoment j',
      pow_mul_mainSecondMoment_div_le hi h_corank_le⟩

/-- **Remaining terms, pairs in the same link class.** Let `E` be a CM field with a primitive root
of unity of order 5040, and let `S` be data of the filling theorem over `E` that satisfy the
standing hypotheses `S.IsAdmissible`. Let `z ≠ 0`. Sum over all classes `c`, `c'` and all near pairs
over them with equal links (`New.link`), with `𝗀 = S.termDisc ≠ 0` for both terms, and whose
reduction `s` has `z ≤ S.meetNorm s`. The products of the sizes `S.termSize` of the two terms add up
to at most `(b ^ (2 f) / z) ^ k 𝒟_main`. -/
theorem sum_termSize_mul_inSameLinkClass_le {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] [S.IsAdmissible] {z : ℕ} (hz : z ≠ 0) :
    ∑ c : S.Classes, ∑ c' : S.Classes,
      ∑' q : {q : S.G E × S.G E | S.IsNearPairOverAgreeingBlock c c' q ∧
        S.InSameLinkClass q.1 q.2 ∧ ∃ s : S.ResidueGL, z ≤ S.meetNorm s ∧ q.1 ∈ S.termsOver c s c'},
        ENNReal.ofReal
          (S.termSize c c' (q : S.G E × S.G E).1 * S.termSize c c' (q : S.G E × S.G E).2) ≤
      .ofReal ((S.b ^ (2 * numInfPlaces E) / z) ^ 𝔰.k * S.mainSecondMoment) := by
  have hτ : 1 ≤ S.tailScale := one_le_tailScale
  have h_main : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  have h_const : S.tailScale * (S.tailScale ^ 7 * S.mainSecondMoment / z ^ 𝔰.k) =
      (S.b ^ (2 * numInfPlaces E) / z) ^ 𝔰.k * S.mainSecondMoment := by
    rw [div_pow, ← pow_mul, mul_assoc, mul_comm _ 𝔰.k, pow_mul', ← tailScale_pow_four]
    ring
  rw [← h_const]
  refine sum_termSize_mul_le (fun c c' ↦ {q : S.G E × S.G E | S.IsNearPairOverAgreeingBlock c c' q ∧
      S.InSameLinkClass q.1 q.2 ∧ ∃ s : S.ResidueGL, z ≤ S.meetNorm s ∧ q.1 ∈ S.termsOver c s c'})
    (fun c c' q hq ↦ hq.left) (by positivity) ?_
  rintro c c' γ γ' ⟨⟨⟨-, h_cell⟩, ⟨-, h_cell'⟩, s, h_agrees, h_over, h_over'⟩,
    ⟨h_disc, -, h_link⟩, s', h_meet, h_over_s'⟩
  obtain rfl : s' = s := eq_of_mem_termsOver h_over_s' h_over
  -- The links are equal and the cell rank is the top one: the gain is `z`, the corank `≤ 1`.
  have h_zero : S.linkCorank γ γ' = 0 := linkCorank_eq_zero_iff.2 h_link
  have h_top : 𝔰.ϱ < S.cellRank γ := h_cell.lt_iff_termDisc_ne_zero.2 h_disc
  have h_gain : (S.pairDiscriminant c c' γ γ' * z) ^ 2 ≤
      S.levelGauge (S.cellRank γ) c c' γ * S.levelGauge (S.cellRank γ') c c' γ' := by
    simpa [h_zero, h_top] using
      pairDiscriminant_sq_le h_agrees h_meet h_over h_over' h_cell h_cell'
  have h_corank : 𝔰.k - finrank E (commonLink γ γ') ≤ 1 := by
    have h_rank : 𝔰.k ≤ finrank E (commonLink γ γ') + S.linkCorank γ γ' +
        (S.cellRank γ - 𝔰.ϱ) := le_finrank_commonLink_add h_cell γ'
    lia
  have h_pow : S.tailScale ^ (𝔰.k - finrank E (commonLink γ γ') + 6) * S.mainSecondMoment /
      (z : ℝ) ^ 𝔰.k ≤ S.tailScale ^ 7 * S.mainSecondMoment / (z : ℝ) ^ 𝔰.k := by
    gcongr
    lia
  exact ⟨z, S.mainSecondMoment, by positivity, h_gain, cellRankSecondMoment_le_mainSecondMoment _,
    cellRankSecondMoment_le_mainSecondMoment _, h_pow⟩

/-- The pieces into which a block is split: one for each link, and one for `𝗀 = 0`. -/
abbrev Piece (E : Type) [Field E] (𝔰 : Shape) : Type :=
  Option (Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E))

open scoped Classical in
/-- The piece of a term `γ`: its link if `𝗀(γ) = S.termDisc γ ≠ 0`; the terms with `𝗀 = 0` form one
further piece. -/
noncomputable def piece {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰)
    (γ : S.G E) : Piece E 𝔰 :=
  if S.termDisc γ = 0 then none else some (link γ)

/-- The piece of `γ` is the submodule `Λ` if and only if `𝗀(γ) = S.termDisc γ` is not zero and the
link of `γ` is `Λ`. -/
lemma piece_eq_some_iff {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    {γ : S.G E} {Λ : Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E)} :
    S.piece γ = some Λ ↔ S.termDisc γ ≠ 0 ∧ link γ = Λ := by
  by_cases h_disc : S.termDisc γ = 0 <;> simp [piece, h_disc]

/-- The part `T ∩ S.piece ⁻¹' {κ}` of a stable set `T` in one piece `κ` is stable. A stable set is
one invariant on both sides under the rational points of the Bessel unipotent group. This holds
because `S.termDisc` and the link are invariant. -/
lemma IsStable.inter_piece {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    {T : Set (S.G E)} (hT : S.IsStable T) (κ : Piece E 𝔰) :
    S.IsStable (T ∩ S.piece ⁻¹' {κ}) := by
  classical
  intro u hu u' hu' γ
  have h_piece : S.piece (u⁻¹ * γ * u') = S.piece γ := by
    simp [piece, frameDisc_frameGram_inv_mul_mul_of_mem_besselU hu hu',
      link_inv_mul_mul_of_mem_besselU hu hu']
  simp [hT u hu u' hu' γ, h_piece]

/-- A near representative of `T` over a block `(c, s, c')` (a chosen near term, that has a cell
rank, where `s` agrees) belongs to `T`. -/
lemma mem_of_mem_nearRepresentativesOver {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} {c c' : S.Classes} {T : Set (S.G E)} {s : S.ResidueGL}
    {p : S.G E} (hp : p ∈ S.nearRepresentativesOver T c s c') : p ∈ T :=
  hp.left.left

/-- A near representative of `T` over the block `(c, s, c')` is a term over this block. -/
lemma mem_termsOver_of_mem_nearRepresentativesOver {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} {c c' : S.Classes} {T : Set (S.G E)}
    {s : S.ResidueGL} {p : S.G E} (hp : p ∈ S.nearRepresentativesOver T c s c') :
    p ∈ S.termsOver c s c' :=
  hp.left.right

/-- Two near representatives over the same block `(c, s, c')` form a near pair over an agreeing
block, that is, two near representatives over one block whose reduction `s` agrees. -/
lemma isNearPairOverAgreeingBlock_of_mem_nearRepresentativesOver {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} {c c' : S.Classes}
    {T T' : Set (S.G E)} {s : S.ResidueGL} {p p' : S.G E}
    (hp : p ∈ S.nearRepresentativesOver T c s c')
    (hp' : p' ∈ S.nearRepresentativesOver T' c s c') :
    S.IsNearPairOverAgreeingBlock c c' (p, p') := by
  obtain ⟨⟨-, h_over⟩, h_agrees, h_near⟩ := hp
  obtain ⟨⟨-, h_over'⟩, -, h_near'⟩ := hp'
  exact ⟨h_near, h_near', s, h_agrees, h_over, h_over'⟩

/-- Let `E` be a CM field with a primitive root of unity of order 5040, and let `S` be data of the
filling theorem over `E` that satisfy the standing hypotheses `S.IsAdmissible`. Let `T`, `T'` be
subsets of `Γ* = S.remainingTerms` that are stable, that is, invariant on both sides under the
rational points of the Bessel unipotent group. The product of the norms of the sums of the
amplitudes of their terms over `(c, s, c')` is at most the sum, over a near representative of `T`
and one of `T'`, of the square of the covolume `S.unipotentCovolume` times the product of the two
sizes.

A rational point `γ` lies over `(c, s, c')` if `h_c⁻¹ γ h_c'` (`h_c = S.classRep c`) is integral
with reduction `s`. Its amplitude is the integral over the archimedean points `y` of
`β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^*`, where `β_c = S.classCutoff c` and `W` is the cut Bessel
function, the Bessel function times a cutoff in the length `besselLength` at each infinite place. A
near representative of `T` over `(c, s, c')` is a `γ ∈ T` over `(c, s, c')` that is near (some
archimedean point `y` and `γ⁻¹ y` are both reduced and of bounded size, `S.boxedPoints`), is the
chosen element of its double coset under the groups `S.classUnipotent₀` and has a cell rank; there
are none unless `S.Agrees s`. The size `S.termSize c c' γ` is `τ² (D_j / (n_p G ^ k)) ^ (1 / 2)`,
where `j = S.cellRank γ` is the index of the cell of `γ`, `D_j = S.cellRankSecondMoment j`,
`G = S.levelGauge j c c' γ` is its gauge, `n_p = S.pairCountScale` and `τ = S.tailScale`. -/
lemma enorm_amplitudeSum_mul_le {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [HasPrimitiveRoot5040 E] [S.IsAdmissible] {c c' : S.Classes} {T T' : Set (S.G E)}
    (hT : S.IsStable T) (hT' : S.IsStable T')
    (h_sub : T ⊆ S.remainingTerms) (h_sub' : T' ⊆ S.remainingTerms) {s : S.ResidueGL} :
    ‖S.amplitudeSum .cut T c s c'‖ₑ * ‖S.amplitudeSum .cut T' c s c'‖ₑ ≤
      ∑' q : S.nearRepresentativesOver T c s c' × S.nearRepresentativesOver T' c s c',
        .ofReal (S.unipotentCovolume ^ 2) *
        .ofReal (S.termSize c c' q.1 * S.termSize c c' q.2) := by
  grw [enorm_amplitudeSum_le_tsum_termSize hT h_sub,
    enorm_amplitudeSum_le_tsum_termSize hT' h_sub']
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, ← tsum_prod]
  refine tsum_le_tsum fun ⟨p, p'⟩ ↦ le_of_eq ?_
  have h_size : 0 ≤ S.termSize c c' p := by
    unfold termSize orbitBound
    positivity
  simp only [ofReal_mul S.unipotentCovolume_pos.le, ofReal_pow S.unipotentCovolume_pos.le,
    ofReal_mul h_size]
  ring

/-- Sum block estimates over pairs in `T` when each pair determines its block. -/
private lemma tsum_le_of_pair_blocks {ι α : Type*} {A B : ι → Set α} {T : Set (α × α)}
    {g : ι → ℝ≥0∞} {k : ℝ≥0∞} (w : α × α → ℝ≥0∞)
    (mem : ∀ i (a : A i) (b : B i), (a.val, b.val) ∈ T)
    (unique : ∀ i j (a b : α), a ∈ A i → b ∈ B i → a ∈ A j → b ∈ B j → i = j)
    (bound : ∀ i, g i ≤ ∑' q : A i × B i, k * w (q.1, q.2)) :
    ∑' i, g i ≤ k * ∑' q : T, w q := by
  let pair (x : Σ i, A i × B i) : T := ⟨(x.2.1, x.2.2), mem x.1 x.2.1 x.2.2⟩
  have inj : pair.Injective := by
    rintro ⟨i, ⟨a, ha⟩, b, hb⟩ ⟨j, ⟨_, ha'⟩, _, hb'⟩ ⟨⟩
    cases unique i j a b ha hb ha' hb'
    rfl
  exact (tsum_le_tsum bound).trans <| (tsum_sigma' fun x ↦ k * w (pair x)).symm.trans_le <|
    (tsum_comp_le_tsum_of_injective inj fun q : T ↦ k * w q).trans_eq ENNReal.tsum_mul_left

/-- Let `E` be a CM field with a primitive root of unity of order 5040, and let `S` be data of the
filling theorem over `E` that satisfy the standing hypotheses `S.IsAdmissible`. Let
`T ⊆ Γ* = S.remainingTerms` be stable (invariant on both sides under the rational points of the
Bessel unipotent group). The squared norm of the sum of the amplitudes of the terms of `T` over
`(c, s, c')` is at most the sum over submodules `Λ` of the same squared norms for the terms of `T`
with `𝗀 = S.termDisc ≠ 0` and link `Λ`, plus `S.unipotentCovolume ^ 2` times the sum of the products
of the sizes over the pairs of near representatives of `T` whose links differ or for one of which
`𝗀` vanishes.

The link `link γ` is the module of pairs (class of `t`, class of `γ⁻¹ t`) in `X^⊥/X`,
`X = ⟨e₁, …, e_ϱ⟩`, `t ⊥ X, γ X`. A rational point `γ` lies over `(c, s, c')` if `h_c⁻¹ γ h_c'`
(`h_c = S.classRep c`) is integral with reduction `s`. Its amplitude is the integral over the
archimedean points `y` of `β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^*`, where `β_c = S.classCutoff c` and
`W` is the cut Bessel function, the Bessel function times a cutoff in the length `besselLength` at
each infinite place. A near representative of `T` over `(c, s, c')` is a `γ ∈ T` over `(c, s, c')`
that is near (some archimedean point `y` and `γ⁻¹ y` are both reduced and of bounded size,
`S.boxedPoints`), is the chosen element of its double coset under the groups `S.classUnipotent₀` and
has a cell rank; there are none unless `S.Agrees s`. The size `S.termSize c c' γ` is
`τ² (D_j / (n_p G ^ k)) ^ (1 / 2)`, where `j = S.cellRank γ` is the index of the cell of `γ`,
`D_j = S.cellRankSecondMoment j`, `G = S.levelGauge j c c' γ` is its gauge, `n_p = S.pairCountScale`
and `τ = S.tailScale`. -/
lemma enorm_amplitudeSum_sq_le {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [HasPrimitiveRoot5040 E] [S.IsAdmissible] {c c' : S.Classes} {T : Set (S.G E)}
    (hT : S.IsStable T) (h_sub : T ⊆ S.remainingTerms) (s : S.ResidueGL) :
    ‖S.amplitudeSum .cut T c s c'‖ₑ ^ 2 ≤
      ∑' Λ : Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E),
        ‖S.amplitudeSum .cut (T ∩ {γ : S.G E | S.termDisc γ ≠ 0} ∩ link ⁻¹' {Λ}) c s c'‖ₑ ^ 2 +
      .ofReal (S.unipotentCovolume ^ 2) *
        ∑' q : {q ∈ S.nearRepresentativesOver T c s c' ×ˢ S.nearRepresentativesOver T c s c' |
            ¬S.InSameLinkClass q.1 q.2},
          .ofReal
            (S.termSize c c' (q : S.G E × S.G E).1 * S.termSize c c' (q : S.G E × S.G E).2) := by
  -- Expand the square into pairs of pieces. The squares of the pieces with `𝗀 ≠ 0` stay; every
  -- other product is bounded by the sizes of pairs of near representatives that do not lie in the
  -- same link class.
  let part (κ : Piece E 𝔰) : ℝ≥0∞ := ‖S.amplitudeSum .cut (T ∩ S.piece ⁻¹' {κ}) c s c'‖ₑ
  let product (p : Piece E 𝔰 × Piece E 𝔰) : ℝ≥0∞ := part p.1 * part p.2
  let diagonal : Set (Piece E 𝔰 × Piece E 𝔰) := Set.range fun Λ ↦ (some Λ, some Λ)
  have h_diagonal : ∑' p : diagonal, product p =
      ∑' Λ, ‖S.amplitudeSum .cut (T ∩ {γ | S.termDisc γ ≠ 0} ∩ link ⁻¹' {Λ}) c s c'‖ₑ ^ 2 := by
    refine (tsum_range product fun Λ Λ' h ↦ by simpa using h).trans (tsum_congr fun Λ ↦ ?_)
    have h_set : T ∩ S.piece ⁻¹' {some Λ} = T ∩ {γ | S.termDisc γ ≠ 0} ∩ link ⁻¹' {Λ} :=
      Set.ext fun γ ↦ by simp [piece_eq_some_iff, and_assoc]
    simp only [product, part, h_set, sq]
  let nearRepsOfPiece (κ : Piece E 𝔰) : Set (S.G E) :=
    S.nearRepresentativesOver (T ∩ S.piece ⁻¹' {κ}) c s c'
  let apart : Set (S.G E × S.G E) :=
    {q ∈ S.nearRepresentativesOver T c s c' ×ˢ S.nearRepresentativesOver T c s c' |
      ¬S.InSameLinkClass q.1 q.2}
  have h_nearReps_subset {κ : Piece E 𝔰} :
      nearRepsOfPiece κ ⊆ S.nearRepresentativesOver T c s c' :=
    fun q ⟨⟨⟨hγ, _⟩, h_over⟩, h_rest⟩ ↦ ⟨⟨hγ, h_over⟩, h_rest⟩
  have h_piece {κ : Piece E 𝔰} {q : S.G E} (hq : q ∈ nearRepsOfPiece κ) : S.piece q = κ :=
    (mem_of_mem_nearRepresentativesOver hq).right
  have h_mem (p : ↥diagonalᶜ) (q : nearRepsOfPiece p.val.1) (q' : nearRepsOfPiece p.val.2) :
      (q.val, q'.val) ∈ apart := by
    refine ⟨⟨h_nearReps_subset q.prop, h_nearReps_subset q'.prop⟩,
      fun ⟨h_disc, h_disc', h_link⟩ ↦ p.prop ?_⟩
    exact ⟨link q.val, by simp [Prod.ext_iff, ← h_piece q.prop, ← h_piece q'.prop, piece,
      h_disc, h_disc', h_link]⟩
  have h_others : ∑' p : ↥diagonalᶜ, product p ≤
      .ofReal (S.unipotentCovolume ^ 2) * ∑' q : apart, .ofReal
        (S.termSize c c' (q : S.G E × S.G E).1 * S.termSize c c' (q : S.G E × S.G E).2) := by
    apply tsum_le_of_pair_blocks (fun q ↦ .ofReal (S.termSize c c' q.1 * S.termSize c c' q.2)) h_mem
    · intro i j a b ha hb ha' hb'
      exact Subtype.ext (Prod.ext ((h_piece ha).symm.trans (h_piece ha'))
        ((h_piece hb).symm.trans (h_piece hb')))
    · exact fun p ↦ enorm_amplitudeSum_mul_le (hT.inter_piece p.val.1) (hT.inter_piece p.val.2)
        (Set.inter_subset_left.trans h_sub) (Set.inter_subset_left.trans h_sub)
  calc
    _ ≤ (∑' κ, part κ) ^ 2 := by grw [enorm_amplitudeSum_le_tsum_fibre S.piece]
    _ = ∑' p : Piece E 𝔰 × Piece E 𝔰, product p := by
      simp_rw [product, sq, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, ← tsum_prod]
    _ = ∑' p : diagonal, product p + ∑' p : ↥diagonalᶜ, product p :=
      (CompleteLattice.summable.tsum_add_tsum_compl (s := diagonal) CompleteLattice.summable).symm
    _ ≤ _ := add_le_add h_diagonal.le h_others

/-- **Remaining terms, reduction to one link.** Let `E` be a CM field with a primitive root of unity
of order 5040, and let `S` be data of the filling theorem over `E` that satisfy the standing
hypotheses `S.IsAdmissible`. Let `Ω` be a set of reductions, `w ≥ 0` and `ν = S.unipotentCovolume`.
Suppose that the terms with `𝗀 = S.termDisc ≠ 0`, taken link by link, have sum of squared norms of
amplitude sums (`linkSecondMoment`) at most `w ν²` over `Ω`. Then the second moment over `Ω` of
`Γ* = S.remainingTerms`, for the cut Bessel function, is at most `w + b ^ (-k f) 𝒟_id`. -/
theorem secondMoment_remainingTerms_le {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [HasPrimitiveRoot5040 E] [S.IsAdmissible] {w : ℝ} {Ω : Set S.ResidueGL} (hw : 0 ≤ w)
    (h_linkMoment : linkSecondMoment {γ : S.G E | S.termDisc γ ≠ 0} Ω ≤
      ENNReal.ofReal (w * S.unipotentCovolume ^ 2)) :
    secondMoment (S.amplitudeSum .cut S.remainingTerms) Ω ≤
      w + S.identitySecondMoment / S.b ^ (𝔰.k * numInfPlaces E) := by
  -- Bound each block by `enorm_amplitudeSum_sq_le`, and sum over the pairs that do not satisfy
  -- `InSameLinkClass` by `sum_termSize_mul_not_inSameLinkClass_le`.
  classical
  set T : Set (S.G E) := S.remainingTerms with hT
  have h_inter : T ∩ {γ | S.termDisc γ ≠ 0} = {γ | S.termDisc γ ≠ 0} :=
    Set.inter_eq_right.2 fun γ hγ ↦ .inl hγ
  rw [← h_inter] at h_linkMoment
  have h_id : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have hν : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb_pos : 0 < S.b := b_pos
  let size (c c' : S.Classes) (q : S.G E × S.G E) : ℝ≥0∞ :=
    .ofReal (S.termSize c c' q.1 * S.termSize c c' q.2)
  let apartOver (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) : Set (S.G E × S.G E) :=
    {q ∈ S.nearRepresentativesOver T c s c' ×ˢ S.nearRepresentativesOver T c s c' |
      ¬S.InSameLinkClass q.1 q.2}
  let apart (c c' : S.Classes) : Set (S.G E × S.G E) :=
    {q | S.IsNearPairOverAgreeingBlock c c' q ∧ ¬S.InSameLinkClass q.1 q.2}
  have h_mem {c c' : S.Classes} {s : S.ResidueGL} : apartOver c s c' ⊆ apart c c' :=
    fun q ⟨⟨hq, hq'⟩, h_class⟩ ↦ ⟨isNearPairOverAgreeingBlock_of_mem_nearRepresentativesOver hq hq',
      h_class⟩
  -- A pair of terms determines its `s`.
  have h_blocks (c c' : S.Classes) :
      ∑' s : Ω, ∑' q : apartOver c s c', size c c' q ≤ ∑' q : apart c c', size c c' q := by
    let pair (x : Σ s : Ω, apartOver c s c') : apart c c' := ⟨x.2, h_mem x.2.prop⟩
    have h_injective : pair.Injective := by
      rintro ⟨⟨s, _⟩, q, ⟨hq, _⟩, _⟩ ⟨⟨s', _⟩, q', ⟨hq', _⟩, _⟩ ⟨⟩
      obtain rfl : s = s' := eq_of_mem_termsOver (mem_termsOver_of_mem_nearRepresentativesOver hq)
        (mem_termsOver_of_mem_nearRepresentativesOver hq')
      rfl
    exact (tsum_sigma' fun x ↦ size c c' (pair x)).symm.trans_le
      (tsum_comp_le_tsum_of_injective h_injective fun q ↦ size c c' q)
  have h_block (c c' : S.Classes) (s : Ω) : ‖S.amplitudeSum .cut T c s c'‖ₑ ^ 2 ≤
      ∑' Λ, ‖S.amplitudeSum .cut (T ∩ {γ | S.termDisc γ ≠ 0} ∩ link ⁻¹' {Λ}) c s c'‖ₑ ^ 2 +
        .ofReal (S.unipotentCovolume ^ 2) * ∑' q : apartOver c s c', size c c' q :=
    enorm_amplitudeSum_sq_le isStable_remainingTerms hT.subset s
  suffices ENNReal.ofReal (∑ c, ∑ c', ∑ s with s ∈ Ω, ‖S.amplitudeSum .cut T c s c'‖ ^ 2) ≤
      .ofReal ((w + S.identitySecondMoment / S.b ^ (𝔰.k * numInfPlaces E)) * S.unipotentCovolume ^
        2) by
    simp_rw [secondMoment, ← Finset.sum_div]
    rwa [div_le_iff₀ (by positivity), ← ofReal_le_ofReal_iff (by positivity)]
  calc
    _ = ∑ c, ∑ c', ∑' s : Ω, ‖S.amplitudeSum .cut T c s c'‖ₑ ^ 2 := by
      simp (disch := (intros; positivity)) [← sum_subtype_eq_sum_filter, ofReal_sum_of_nonneg]
    _ ≤ linkSecondMoment (T ∩ {γ | S.termDisc γ ≠ 0}) Ω + .ofReal (S.unipotentCovolume ^ 2) *
        ∑ c, ∑ c', ∑' s : Ω, ∑' q : apartOver c s c', size c c' q := by
      grw [h_block]
      simp [linkSecondMoment, sum_add_distrib, mul_sum]
    _ ≤ .ofReal (w * S.unipotentCovolume ^ 2) + .ofReal (S.unipotentCovolume ^ 2) *
        .ofReal (S.identitySecondMoment / S.b ^ (𝔰.k * numInfPlaces E)) := by
      grw [h_blocks, h_linkMoment]
      gcongr
      exact sum_termSize_mul_not_inSameLinkClass_le
    _ = _ := by
      rw [add_mul, ofReal_add (by positivity) (by positivity),
        mul_comm (S.identitySecondMoment / _), ofReal_mul (sq_nonneg S.unipotentCovolume)]

/-- **Remaining terms, one link at a time.** Let `E` be a CM field with a primitive root of unity of
order 5040, and let `S` be data of the filling theorem over `E` that satisfy the standing hypotheses
`S.IsAdmissible`. Let `Ω` be a set of reductions, that is, of elements of `S.ResidueGL`, the product
of the general linear groups over the residue fields at the chosen places above the level `M = S.M`.
A reduction `s` meets at a place above `M` if, modulo that place, the span of the frame and its
image under `s` share a nonzero vector; `S.meetNorm s` is the norm of the product of the places at
which `s` meets. Let `z ≠ 0` be a natural number with `z ≤ S.meetNorm s` for every `s ∈ Ω`.

Let `T` be the set of rational points `γ` of the unitary group with `S.termDisc γ ≠ 0`. For classes
`c`, `c'`, a reduction `s` and a submodule `Λ`, take the sum of the amplitudes of the `γ ∈ T` that
lie over `(c, s, c')` and have link `Λ`. The squared norms of these sums, added over all `c`, `c'`,
`s ∈ Ω` and `Λ`, give `linkSecondMoment T Ω`, and this is at most `(b ^ (2 f) / z) ^ k 𝒟_main ν²`.
Here `b = S.b` is the size parameter, `k = 𝔰.k` is the dimension of the definite space, `f` is the
number of infinite places of `E`, and `𝒟_main = S.mainSecondMoment` and the covolume
`ν = S.unipotentCovolume` are real constants attached to `S`. -/
theorem linkSecondMoment_le_of_le_meetNorm {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {Ω : Set S.ResidueGL} {z : ℕ} (hz : z ≠ 0)
    (h_meet : ∀ s ∈ Ω, z ≤ S.meetNorm s) :
    linkSecondMoment {γ : S.G E | S.termDisc γ ≠ 0} Ω ≤
      ENNReal.ofReal ((S.b ^ (2 * numInfPlaces E) / z) ^ 𝔰.k * S.mainSecondMoment *
        S.unipotentCovolume ^ 2) := by
  -- The square of the block of one link is bounded by pairs of near representatives in the same
  -- link class.
  let Link : Type := Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E)
  let terms (Λ : Link) : Set (S.G E) := {γ : S.G E | S.termDisc γ ≠ 0} ∩ link ⁻¹' {Λ}
  have h_stable (Λ : Link) : S.IsStable (terms Λ) := by
    intro u hu u' hu' γ
    simp [terms, frameDisc_frameGram_inv_mul_mul_of_mem_besselU hu hu',
      link_inv_mul_mul_of_mem_besselU hu hu']
  have h_sub (Λ : Link) : terms Λ ⊆ S.remainingTerms := fun γ ⟨h_disc, _⟩ ↦ .inl h_disc
  let nearRepsInLink (c c' : S.Classes) (p : Ω × Link) : Set (S.G E) :=
    S.nearRepresentativesOver (terms p.2) c p.1 c'
  let sameLinkPairs (c c' : S.Classes) : Set (S.G E × S.G E) :=
    {q : S.G E × S.G E | S.IsNearPairOverAgreeingBlock c c' q ∧ S.InSameLinkClass q.1 q.2 ∧
      ∃ s : S.ResidueGL, z ≤ S.meetNorm s ∧ q.1 ∈ S.termsOver c s c'}
  let size (c c' : S.Classes) (q : S.G E × S.G E) : ℝ≥0∞ :=
    .ofReal (S.termSize c c' q.1 * S.termSize c c' q.2)
  have h_mem {c c' : S.Classes} (p : Ω × Link) (q q' : nearRepsInLink c c' p) :
      (q.val, q'.val) ∈ sameLinkPairs c c' := by
    obtain ⟨⟨s, hs⟩, Λ⟩ := p
    obtain ⟨γ, hγ⟩ := q
    obtain ⟨γ', hγ'⟩ := q'
    obtain ⟨h_disc : S.termDisc γ ≠ 0, h_link : link γ = Λ⟩ := mem_of_mem_nearRepresentativesOver hγ
    obtain ⟨h_disc' : S.termDisc γ' ≠ 0, h_link' : link γ' = Λ⟩ :=
      mem_of_mem_nearRepresentativesOver hγ'
    have h_pair : S.IsNearPairOverAgreeingBlock c c' (γ, γ') :=
      isNearPairOverAgreeingBlock_of_mem_nearRepresentativesOver hγ hγ'
    have h_class : S.InSameLinkClass γ γ' := ⟨h_disc, h_disc', h_link.trans h_link'.symm⟩
    exact ⟨h_pair, h_class, s, h_meet s hs, mem_termsOver_of_mem_nearRepresentativesOver hγ⟩
  have h_blocks (c c' : S.Classes) :
      ∑' (s : Ω) (Λ : Link), ‖S.amplitudeSum .cut (terms Λ) c s c'‖ₑ ^ 2 ≤
        .ofReal (S.unipotentCovolume ^ 2) * ∑' q : sameLinkPairs c c', size c c' q := by
    rw [← tsum_prod]
    apply tsum_le_of_pair_blocks (size c c') (h_mem (c := c) (c' := c'))
    · rintro ⟨s, Λ⟩ ⟨s', Λ'⟩ q _ hq _ hq' _
      refine Prod.ext
        (Subtype.ext (eq_of_mem_termsOver (mem_termsOver_of_mem_nearRepresentativesOver hq)
        (mem_termsOver_of_mem_nearRepresentativesOver hq'))) ?_
      exact ((mem_of_mem_nearRepresentativesOver hq).2 : link q = Λ).symm.trans
        (mem_of_mem_nearRepresentativesOver hq').2
    · intro p
      rw [sq]
      exact enorm_amplitudeSum_mul_le (h_stable p.2) (h_stable p.2) (h_sub p.2) (h_sub p.2)
  calc
    _ = ∑ c : S.Classes, ∑ c' : S.Classes,
        ∑' (s : Ω) (Λ : Link), ‖S.amplitudeSum .cut (terms Λ) c s c'‖ₑ ^ 2 := by
      simp only [linkSecondMoment, tsum_fintype (β := S.Classes), terms, Link]
    _ ≤ .ofReal (S.unipotentCovolume ^ 2) *
        ∑ c : S.Classes, ∑ c' : S.Classes, ∑' q : sameLinkPairs c c', size c c' q := by
      grw [h_blocks]
      simp only [mul_sum, le_refl]
    _ ≤ .ofReal (S.unipotentCovolume ^ 2) *
        .ofReal ((S.b ^ (2 * numInfPlaces E) / z) ^ 𝔰.k * S.mainSecondMoment) := by
      gcongr
      exact sum_termSize_mul_inSameLinkClass_le hz
    _ = _ := by rw [mul_comm _ (S.unipotentCovolume ^ 2), ofReal_mul (sq_nonneg _)]

end New.Filling
