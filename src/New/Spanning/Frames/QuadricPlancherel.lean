module

import Mathlib.Algebra.Order.Star.Int
public import New.Spanning.Frames.Lengths
import Mathlib.CategoryTheory.Countable
import Mathlib.Topology.Algebra.Group.Units
public import New.Spanning.Frames.Correlations
public import Lib.DiscreteSeries.Bruhat.QuadricBlocks
public import Lib.DiscreteSeries.Bruhat.FourierKernels
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Topology.Separation.CompletelyRegular
import Lib.Base
import Lib.General.Measure.IntegralOperators

section
/-!
# Comparing the lengths at two points; minors and heads

Each isometry g of the form `T.splitGram` gives a gauge, the size of g⁻¹ y, on vectors y. The
gauges at two points differ little on Y^(l-1) if they differ little on Y^(l), the frame vector
e_(l-1) has short lifts at both points, and it has a short dual that looks nearly the same from both
points. Over a head, such duals come from determinants of blocks of the isometries (Cramer's rule).

Notions from other files:
* `S.ofSize i`, `S.vecsOfSize i`, `S.HasMatrixSize i`: the numbers x of size i (|x| ≤ L^i at a real
  place, L^i x integral at the finite places, for a fixed scale L), and the vectors and matrices all
  of whose entries have size i.
* Y^(l): the vectors orthogonal to e_0, …, e_(l-1) (`IsOrthogonalBelow l`) modulo the span of these
  (`CongrBelow l`). The basis vectors e_a and e*_a have the indices `inl a` and `eStar a`.
* `S.GaugesDifferLe r g g' l t`: for each ω orthogonal to e_0, …, e_(l-1) with g⁻¹ ω of size i, the
  class of ω in Y^(l) has a lift ω' such that (g⁻¹ ω - g'⁻¹ ω') / r has size i + t.
* R^(l) = `partialUnitriangularGroup l`: the isometries that change each frame vector of index below
  l by a combination of the earlier ones. U_(<l) = `unipotentBelow l`: the isometries that are
  unitriangular when all basis vectors other than e_a, e*_a (a < l) are put on one middle level.
* `S.IsHead j p`: the inverses of the products p₀ ⋯ p_(l-1), l ≤ j, have size 1. The Weyl element
  w_p = `weylElem j p` sends e_a to p_a e*_a for a < j.

## Main definitions and results

* `New.Floors.Size.GaugesDifferLe.of_succ`,
  `New.Floors.Size.GaugesDifferLe.on_whole_space_of_hasShortDual`: the recursion down the quotients.
* `New.Floors.Size.GaugesDifferLe.hasMatrixSize_sub_one`: a bound on the whole space bounds the
  matrix `(x - 1) / r`.
* `New.Floors.Size.leadingMinor_mem_ofSize`, `New.Floors.Size.head_products_mem_ofSize`: the leading
  minors have bounded size.
* `New.Floors.Size.dual_mem_vecsOfSize`, `New.Floors.Size.hasMatrixSize_of_isHead`: short duals over
  a head, and bounds for the sizes of g and w_p⁻¹ g.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

@[expose] public section

noncomputable section

namespace New.Floors

section Size

open Matrix BesselIndex Sum Fintype FloorGroups Finset Fin

variable {A : Type} [CommRing A] [StarRing A] {𝔰 : Shape} {T : 𝔰.Form A}

variable {c i j : ℕ} [IsHermitianUnit T.splitGram] {s g x : T.G} {a : Fin 𝔰.ϱ} {p : ℕ → Aˣ}
  {r : Aˣ} {S : Size T}

namespace Size

/-- Let the isometries `ξ` and `ξ'` change each frame vector of index below `l` by a combination of
the earlier ones (`partialUnitriangularGroup l`). If all entries of `ξ g` and `ξ' γ⁻¹ g` have size 1
(size i: in `S.ofSize i`), then the leading minors of order `j ≤ l` of `T.frameGram γ`, the matrix
of the products ⟨f_a, γ f_b⟩ of the `𝔰.n = ϱ + 1` frame vectors f_a, have size `9 * 𝔰.n`. -/
theorem leadingMinor_mem_ofSize {l : ℕ} {γ g ξ ξ' : T.G} (hξ : ξ ∈ partialUnitriangularGroup l)
    (hξ' : ξ' ∈ partialUnitriangularGroup l)
    (hg : S.HasMatrixSize 1 (↑(ξ * g) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hγg : S.HasMatrixSize 1 (↑(ξ' * (γ⁻¹ * g)) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    {j : Fin (𝔰.n + 1)} (hj : j.val ≤ l) :
    leadingMinor (T.frameGram γ) j ∈ S.ofSize (9 * 𝔰.n) := by
  -- The element `x = (ξ g) (ξ' γ⁻¹ g)⁻¹ = ξ γ ξ'⁻¹` has size 7, and `T.frameGram x` has the same
  -- leading minors of order at most `l` as `T.frameGram γ`.
  let x : T.G := ξ * g * (ξ' * (γ⁻¹ * g))⁻¹
  let X : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := x
  have h_size : S.HasMatrixSize 7 X := hg.mul hγg.inv
  have h_minor : leadingMinor (T.frameGram γ) j = leadingMinor (T.frameGram X) j := by
    have hx : ξ⁻¹ * x * ξ' = γ := by simp [x, mul_assoc]
    rw [← leadingMinor_frameGram_partialUnitriangularGroup_mul hξ hξ' x hj, hx]
  -- In `J x`, with `J = T.splitGram`, the row of `e_a` is the row of `e*_a` in `x`.
  have h_row (i k : 𝔰.BesselIndex) (hi : floorOf i < 𝔰.ϱ) :
      (T.splitGram * X) i k = X (oppositeIndex i) k :=
    splitGram_mulVec_apply (e := fun m ↦ X m k) i hi
  have h_all : S.HasMatrixSize 9 (T.splitGram * X) := hasMatrixSize_splitGram.mul h_size
  rw [h_minor, leadingMinor]
  obtain ⟨_ | j, hj_lt⟩ := j
  · rw [det_isEmpty]
    exact (S.zero_one_mem_ofSize _).right
  -- All rows of the minor but the last belong to vectors `e_a`, `a < ϱ`.
  have hj_le : j ≤ 𝔰.ϱ := by lia
  refine mem_ofSize_mono (i := 9 * (j + 1)) ?_ (by lia)
  refine det_mem_ofSize_of_last_row _ hj_le (fun a b ↦ ?_) fun b ↦ h_all _ _
  rw [submatrix_apply, submatrix_apply, frameGram, submatrix_apply,
    h_row _ _ (floorOf_besselFrame.trans_lt (a.is_lt.trans_le hj_le))]
  exact h_size _ _

omit [IsHermitianUnit T.splitGram] in
/-- Let g, g' be isometries and r a self-adjoint unit of size 1. Write Y^(l) for the vectors
orthogonal to e_0, …, e_(l-1) modulo the span of these. Assume that the class of
e_a = `Pi.single (inl a) 1` in Y^(a) has lifts f, f' with g⁻¹ f and g'⁻¹ f' of size c. Assume also
that e_a has a short dual ζ in Y^(a): ⟨e_a, ζ⟩ = 1, and g⁻¹ ζ and (g⁻¹ ζ - g'⁻¹ ζ') / r have size c
for some lift ζ' of ζ. Suppose the lengths at g and g' differ by at most L^t modulo r on Y^(a+1):
each class [ω] with g⁻¹ ω of size i has a lift ω' with (g⁻¹ ω - g'⁻¹ ω') / r of size i + t. Then
they differ by at most L^(t + 4 c + 12) modulo r on Y^(a). -/
lemma GaugesDifferLe.of_succ {g' : T.G} {t : ℕ} (hr_star : star r.val = r)
    (hr_size : ↑r ∈ S.ofSize 1) (hg : S.InducedLengthLe g a c (Pi.single (inl a) 1))
    (hg' : S.InducedLengthLe g' a c (Pi.single (inl a) 1)) (h_dual : S.HasShortDual r g g' a c)
    (h : S.GaugesDifferLe r g g' (a + 1) t) : S.GaugesDifferLe r g g' a (t + (4 * c + 12)) := by
  -- Write ω = α ζ + ω₀ with α = ⟨e_a, ω⟩, so that ω₀ is orthogonal to e_a. The class of ω₀ in
  -- Y^(a+1) has a lift ω₀' with g'⁻¹ ω₀' close to g⁻¹ ω₀ modulo r. Pairing with the dual ζ bounds
  -- μ / r, where μ is the coefficient of e_a in ω₀' - ω₀, and α ζ' + ω₀' - μ f' is the lift of ω,
  -- where f' is the short lift of e_a at g'.
  intro i ω hω hω_len
  obtain ⟨f, hf, hf_len⟩ : ∃ f, CongrBelow a (Pi.single (inl a) 1) f ∧ S.LengthLeAt g c f := hg
  obtain ⟨f', hf', hf'_len⟩ :
      ∃ f', CongrBelow a (Pi.single (inl a) 1) f' ∧ S.LengthLeAt g' c f' := hg'
  obtain ⟨ζ, hζ, hζ_one, hζ_len, ζ', hζ', hζ_agree⟩ : ∃ ζ, IsOrthogonalBelow a ζ ∧ ζ (eStar a) = 1 ∧
      S.LengthLeAt g c ζ ∧ S.AgreesModulo r g g' a c ζ := h_dual
  set α : A := ω (eStar a) with hα
  have hα_size : α ∈ S.ofSize (c + i + 3) := by
    have h_form : star (g⁻¹.val.val *ᵥ f) ⬝ᵥ T.splitGram *ᵥ g⁻¹.val.val *ᵥ ω = α := by
      rw [U.form_mulVec_mulVec, hf.form_eq_left hω a.is_lt.le]
      simp [hα]
    rw [← h_form]
    exact form_mem_ofSize hf_len hω_len
  set ω₀ : 𝔰.BesselIndex → A := ω - α • ζ with hω₀
  have hω₀_orth : IsOrthogonalBelow (a + 1) ω₀ := fun b hb ↦ by
    obtain hb | hb := Nat.lt_succ_iff_lt_or_eq.1 hb
    · simp [hω₀, hω b hb, hζ b hb]
    · simp [hω₀, hα, Fin.ext hb, hζ_one]
  have hω₀_len : S.LengthLeAt g (c + i + 3 + c + 1) ω₀ := by
    simpa only [LengthLeAt, hω₀, mulVec_sub, mulVec_smul] using
      sub_mem_vecsOfSize (mem_vecsOfSize_mono hω_len) (smul_mem_vecsOfSize hα_size hζ_len)
  obtain ⟨ω₀', hω₀', hω₀_agree⟩ : S.AgreesModulo r g g' (a + 1) (c + i + 3 + c + 1 + t) ω₀ :=
    h _ ω₀ hω₀_orth hω₀_len
  set μ : A := ω₀' (inl a) - ω₀ (inl a) with hμ
  have hμ_size : r⁻¹.val * μ ∈ S.ofSize (c + (c + i + 3 + c + 1 + t) + 6) := by
    rw [hμ, ← hω₀'.form_sub_form (T := T) hω₀_orth hζ hζ_one hζ', ← U.form_mulVec_mulVec g'⁻¹,
      ← U.form_mulVec_mulVec g⁻¹ ζ]
    exact form_sub_form_mem_ofSize hr_star hr_size hζ_len hζ_agree (mem_vecsOfSize_mono hω₀_len)
      hω₀_agree
  refine ⟨α • ζ' + (ω₀' - μ • f'), fun k hk ↦ ?_, ?_⟩
  · rw [Pi.add_apply, hω₀'.sub_smul hf' k hk]
    simp [hω₀, hζ' k hk]
  · set M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := g⁻¹.val.val
    set M' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := g'⁻¹.val.val
    have h_terms : r⁻¹.val • (M *ᵥ ω - M' *ᵥ (α • ζ' + (ω₀' - μ • f'))) =
        r⁻¹.val • (M *ᵥ ω₀ - M' *ᵥ ω₀') -
          (-α • r⁻¹.val • (M *ᵥ ζ - M' *ᵥ ζ') - (r⁻¹.val * μ) • M' *ᵥ f') := by
      simp only [hω₀, mulVec_add, mulVec_sub, mulVec_smul]
      module
    have h_dual_term : -α • r⁻¹.val • (M *ᵥ ζ - M' *ᵥ ζ') ∈ S.vecsOfSize (c + i + 3 + c) :=
      smul_mem_vecsOfSize (neg_mem_ofSize hα_size) hζ_agree
    have h_frame_term :
        (r⁻¹.val * μ) • M' *ᵥ f' ∈ S.vecsOfSize (c + (c + i + 3 + c + 1 + t) + 6 + c) :=
      smul_mem_vecsOfSize hμ_size hf'_len
    rw [h_terms]
    exact mem_vecsOfSize_mono (sub_mem_vecsOfSize (mem_vecsOfSize_mono hω₀_agree)
      (sub_mem_vecsOfSize (mem_vecsOfSize_mono h_dual_term) h_frame_term))

omit [IsHermitianUnit T.splitGram] in
/-- Let g, g' be isometries, r a self-adjoint unit of size 1 and j ≤ ϱ. For each a < j, let the
class of e_a = `Pi.single (inl a) 1` in Y^(a) have lifts f, f' with g⁻¹ f and g'⁻¹ f' of size c. Let
e_a also have a short dual ζ in Y^(a): ⟨e_a, ζ⟩ = 1, and g⁻¹ ζ and (g⁻¹ ζ - g'⁻¹ ζ') / r have size c
for some lift ζ' of ζ. Suppose the lengths at g and g' differ by at most L^t modulo r on Y^(j): each
class [ω] with g⁻¹ ω of size i has a lift ω' with (g⁻¹ ω - g'⁻¹ ω') / r of size i + t. Then they
differ by at most L^(t + (4 c + 12) j) modulo r on Y^(0), the whole space. -/
lemma GaugesDifferLe.on_whole_space_of_hasShortDual {g' : T.G} {t : ℕ} (hr_star : star r.val = r)
    (hr_size : ↑r ∈ S.ofSize 1) (hj : j ≤ 𝔰.ϱ)
    (hg : ∀ a : Fin 𝔰.ϱ, a.val < j → S.InducedLengthLe g a c (Pi.single (inl a) 1))
    (hg' : ∀ a : Fin 𝔰.ϱ, a.val < j → S.InducedLengthLe g' a c (Pi.single (inl a) 1))
    (h_dual : ∀ a : Fin 𝔰.ϱ, a.val < j → S.HasShortDual r g g' a c)
    (h : S.GaugesDifferLe r g g' j t) : S.GaugesDifferLe r g g' 0 (t + (4 * c + 12) * j) := by
  induction j generalizing t with
  | zero => simpa using h
  | succ j ih =>
    lift j to Fin 𝔰.ϱ using hj
    have hj_lt : j.val < j.val + 1 := j.val.lt_succ_self
    have h_step : S.GaugesDifferLe r g g' j (t + (4 * c + 12)) :=
      h.of_succ hr_star hr_size (hg j hj_lt) (hg' j hj_lt) (h_dual j hj_lt)
    rw [show t + (4 * c + 12) * (j.val + 1) = t + (4 * c + 12) + (4 * c + 12) * j.val by ring]
    exact ih j.is_lt.le (fun a ha ↦ hg a (ha.trans hj_lt)) (fun a ha ↦ hg' a (ha.trans hj_lt))
      (fun a ha ↦ h_dual a (ha.trans hj_lt)) h_step

/-- Let g, x be isometries and r a unit with star r = r. Suppose `S.GaugesDifferLe r g (g * x) 0 i`:
the lengths at g and g x differ by at most L^i modulo r on the whole space. Then r⁻¹ • (x - 1) has
size i + 4. Size i means entries in `S.ofSize i`, for the scale L of `S`. -/
lemma GaugesDifferLe.hasMatrixSize_sub_one (hr_star : star r.val = r)
    (h : S.GaugesDifferLe r g (g * x) 0 i) :
    S.HasMatrixSize (i + 4) (r⁻¹.val • ((x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) - 1)) := by
  -- On the whole space a class has one lift, so the columns of g give those of (1 - x⁻¹) / r. The
  -- matrix (x - 1) / r is the adjoint, for the form, of N = (x⁻¹ - 1) / r.
  set N : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := r⁻¹.val • (x⁻¹.val.val - 1) with hN
  have h_col (k n : 𝔰.BesselIndex) : N n k ∈ S.ofSize i := by
    set ω : 𝔰.BesselIndex → A := g.val.val *ᵥ Pi.single k 1 with hω
    have hω_len : S.LengthLeAt g 0 ω := lengthLeAt_mulVec_iff.mpr (single_mem_vecsOfSize k)
    obtain ⟨ω', h_congr, h_agree⟩ : S.AgreesModulo r g (g * x) 0 (0 + i) ω :=
      h 0 ω (fun b hb ↦ absurd hb b.val.not_lt_zero) hω_len
    obtain rfl : ω = ω' := funext fun m ↦ (h_congr m (Nat.zero_le _)).symm
    have h_entry : N n k = -(r⁻¹.val • (g⁻¹.val.val *ᵥ ω - (g * x)⁻¹.val.val *ᵥ ω)) n := by
      simp only [hN, hω, mulVec_mulVec]
      simp [mul_sub, Matrix.mul_assoc]
    rw [h_entry, ← zero_add i]
    exact neg_mem_ofSize (h_agree n)
  have h_adj : T.splitGram * (r⁻¹.val • (x.val.val - 1)) = Nᴴ * T.splitGram := by
    have h_inv : T.splitGram * x.val.val = x⁻¹.val.valᴴ * T.splitGram := by
      simpa only [inv_inv] using U.form_mul_inv_eq x⁻¹
    simp [hN, hr_star, ← inverse_star_unit, h_inv, mul_sub, Matrix.sub_mul]
  exact fun a b ↦ adjoint_apply_mem_ofSize h_adj a b fun n _ k ↦ h_col k n

/-- A bound by Cramer's rule. Let K be a set of isometries of the form (elements of `T.G`) whose
entries all have size 1, and let a < j ≤ ϱ, where ϱ is the number of hyperbolic pairs e_b, e*_b. Let
s ∈ R^(j) with s g ∈ K, and let η w_p⁻¹ g ∈ K for some η ∈ R^(j). Then p₀ ⋯ p_a times the i-th entry
of the column s e*_a has size 8 ϱ. -/
lemma head_prod_mul_dual_mem_ofSize {S : Size T} {K : Set T.G} {j : ℕ} {p : ℕ → Aˣ} {s g : T.G}
    {a : Fin 𝔰.ϱ}
    (hK : ∀ ⦃x : T.G⦄, x ∈ K → S.HasMatrixSize 1 (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hj : j ≤ 𝔰.ϱ)
    (h_near : ∃ η : T.G, η ∈ partialUnitriangularGroup j ∧ η * ((weylElem j p)⁻¹ * g) ∈ K)
    (hs : s ∈ partialUnitriangularGroup j) (hsK : s * g ∈ K) (ha : a.val < j) (i : 𝔰.BesselIndex) :
    (∏ b ∈ Finset.range (a + 1), p b).val *
      (s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i (eStar a) ∈ S.ofSize (8 * 𝔰.ϱ) := by
  -- Take the rows e*_b (b < a) and i, and the columns e_d (d ≤ a), of s w_p η⁻¹. This block has
  -- size 7, being part of (s g) (η w_p⁻¹ g)⁻¹, and its determinant is the given product.
  obtain ⟨η, hη, hηK⟩ := h_near
  let c : Fin (a + 1) → Fin 𝔰.ϱ := Fin.castLE a.is_lt
  let R (b : Fin (a + 1)) : 𝔰.BesselIndex := if b = .last a then i else eStar (c b)
  let Z : Matrix (Fin (a + 1)) (Fin (a + 1)) A :=
    (s * weylElem j p * η⁻¹).val.val.submatrix R fun d ↦ inl (c d)
  have Z_size : S.HasMatrixSize 7 Z := fun b d ↦ by
    simpa [Z, Matrix.mul_assoc] using (hK hsK).mul (hK hηK).inv (R b) (inl (c d))
  -- Z = L C, where L is the same block of s w_p (w_p sends e_d to p d e*_d) and C is the block of
  -- η⁻¹ on e_0, …, e_a. L is lower triangular, C is unitriangular since η⁻¹ ∈ R^(j).
  let L : Matrix (Fin (a + 1)) (Fin (a + 1)) A := of fun b d ↦ s.val.val (R b) (eStar (c d)) * p d
  let C : Matrix (Fin (a + 1)) (Fin (a + 1)) A :=
    η⁻¹.val.val.submatrix (fun b ↦ inl (c b)) fun d ↦ inl (c d)
  have column (m : 𝔰.BesselIndex) (d : Fin (a + 1)) (hm : d ≤ level m) :
      η⁻¹.val.val m (inl (c d)) = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) m (inl (c d)) :=
    mem_partialUnitriangularGroup.mp (inv_mem hη) m _ hm (by simp [c, ha, level, val_lt_of_le])
  have det_C : C.det = 1 := det_eq_one_of_unitriangular (lev := id) fun b d hbd ↦
    (column (inl (c b)) d hbd).trans (by simp [c, Matrix.one_apply])
  have Z_eq : Z = L * C := by
    ext b d
    -- Rows other than e_0, …, e_a have level at least d, so the column e_d of η⁻¹ vanishes there.
    have h_zero (m : 𝔰.BesselIndex) (hm : m ∉ Set.range fun e ↦ inl (c e)) :
        η⁻¹.val.val m (inl (c d)) = 0 := by
      have h_level : ↑d ≤ level m := by
        obtain e | (e | e) := m
        · exact le_of_not_gt fun he ↦ hm ⟨⟨e, Nat.lt_trans he d.is_lt⟩, rfl⟩
        · exact (c d).is_lt.le
        · exact (c d).is_lt.le.trans (le_level_eStar e)
      rw [column m d h_level, one_apply_ne fun h_eq ↦ hm ⟨d, h_eq.symm⟩]
    have h_weyl (e : Fin (a + 1)) : (s * weylElem j p).val.val (R b) (inl (c e)) = L b e := by
      have he_lt : e.val < j ∧ e.val < 𝔰.ϱ := by lia
      simp [L, Matrix.mul_apply, c, he_lt, weylElem, weylOn, level]
    calc Z b d = ∑ m, (s * weylElem j p).val.val (R b) m * η⁻¹.val.val m (inl (c d)) := by
          simp only [Z, submatrix_apply, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
      _ = ∑ e, (s * weylElem j p).val.val (R b) (inl (c e)) * C e d :=
          (sum_of_injective _ (inl_injective.comp (Fin.castLE_injective _)) _ _
            (fun m hm ↦ by rw [h_zero m hm, mul_zero]) fun _ ↦ rfl).symm
      _ = (L * C) b d := by simp only [h_weyl, Matrix.mul_apply]
  -- The row of s at e*_b agrees with that of 1 outside the columns e*_d, d < b; so L is lower
  -- triangular, with p b on the diagonal for b < a.
  have s_row (b d : Fin (a + 1)) (hbd : b ≤ d) :
      s.val.val (eStar (c b)) (eStar (c d)) = if b = d then 1 else 0 := by
    have hb : (c b).val < j := (Nat.le_of_lt_succ b.is_lt).trans_lt ha
    have h_ne (e : Fin 𝔰.ϱ) (he : e < c b) : (eStar (c d) : 𝔰.BesselIndex) ≠ eStar e := by
      simpa using (he.trans_le (show c b ≤ c d from hbd)).ne'
    rw [partialUnitriangularGroup_apply_eStar hs hb _ h_ne]
    simp [c, Matrix.one_apply]
  have L_lower : L.BlockTriangular OrderDual.toDual := fun b d (hbd : b < d) ↦ by
    simp [L, R, Fin.ne_last_of_lt hbd, s_row b d hbd.le, hbd.ne]
  have L_diag (b : Fin a) : L b.castSucc b.castSucc = p b := by simp [L, R, s_row]
  have L_last : L (.last a) (.last a) = s.val.val i (eStar a) * p a := by simp [L, R, c, castLE]
  have det_Z : Z.det = (∏ b ∈ Finset.range (a + 1), p b).val * s.val.val i (eStar a) := by
    rw [det_eq_of_eq_mul_det_one C det_C Z_eq, det_of_isLowerTriangular _ L_lower,
      prod_univ_castSucc, L_last, prod_range_succ, prod_range]
    simp only [L_diag, Units.val_mul, Units.coe_prod]
    ring
  rw [← det_Z]
  exact mem_ofSize_mono (det_mem_ofSize Z a.is_lt Z_size)

/-- The leading minors at a Weyl element have bounded size. Let `K` be a set of isometries whose
matrices have size 1, and let j ≤ ϱ. Let η w_p⁻¹ g ∈ K for some η ∈ R^(j), and let s ∈ R^(j) with s
g ∈ K. Then the products p₀ ⋯ p_(l-1), l ≤ j, which are the leading minors of `T.frameGram w_p`,
have size 9 n, where n = `𝔰.n` = ϱ + 1. -/
lemma head_products_mem_ofSize {K : Set T.G}
    (hK : ∀ ⦃x : T.G⦄, x ∈ K → S.HasMatrixSize 1 (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hj : j ≤ 𝔰.ϱ)
    (h_near : ∃ η : T.G, η ∈ partialUnitriangularGroup j ∧ η * ((weylElem j p)⁻¹ * g) ∈ K)
    (hs_near : s ∈ partialUnitriangularGroup j ∧ s * g ∈ K) :
    ∀ l : ℕ, l ≤ j → (↑(∏ a ∈ Finset.range l, p a) : A) ∈ S.ofSize (9 * 𝔰.n) := by
  intro l hl
  obtain ⟨η, hη, hηK⟩ := h_near
  obtain ⟨hs, hsK⟩ := hs_near
  rw [← leadingMinor_frameGram_weylElem (T := T) hj p (j := ⟨l, by lia⟩) hl]
  exact leadingMinor_mem_ofSize hs hη (hK hsK) (hK hηK) hl

/-- A bound for s e*_a, by Cramer's rule. Let `K` be a set of isometries whose matrices have size 1,
and let a < j ≤ ϱ. Let η w_p⁻¹ g ∈ K for some η ∈ R^(j), and let s ∈ R^(j) with s g ∈ K. Let `p` be
a head: the inverses of the products p₀ ⋯ p_(l-1), l ≤ j, have size 1. Then all entries of the
vector s e*_a have size 8 ϱ + 1. -/
lemma dual_mem_vecsOfSize {K : Set T.G}
    (hK : ∀ ⦃x : T.G⦄, x ∈ K → S.HasMatrixSize 1 (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hj : j ≤ 𝔰.ϱ)
    (h_near : ∃ η : T.G, η ∈ partialUnitriangularGroup j ∧ η * ((weylElem j p)⁻¹ * g) ∈ K)
    (hs_near : s ∈ partialUnitriangularGroup j ∧ s * g ∈ K) (hp : S.IsHead j p) (ha : a < j) :
    (s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ Pi.single (eStar a) 1 ∈
      S.vecsOfSize (8 * 𝔰.ϱ + 1) := by
  intro i
  obtain ⟨hs, hsK⟩ := hs_near
  set M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := ↑s
  set P : Aˣ := ∏ b ∈ Finset.range (a + 1), p b
  have hP_inv : P⁻¹.val ∈ S.ofSize 1 := hp (a + 1) ha
  have h_cramer : P.val * M i (eStar a) ∈ S.ofSize (8 * 𝔰.ϱ) :=
    head_prod_mul_dual_mem_ofSize hK hj h_near hs hsK ha i
  have h_entry : (M *ᵥ Pi.single (eStar a) 1) i = P⁻¹.val * (P.val * M i (eStar a)) := by simp
  rw [h_entry, add_comm (8 * 𝔰.ϱ)]
  exact S.mul_mem_ofSize hP_inv h_cramer

/-- The entries of a head and of the dual vectors have bounded size. Let `K` be a set of isometries
whose matrices have size 1, and let a < j ≤ ϱ. With R^(j) = `partialUnitriangularGroup j` and the
Weyl element w_p = `weylElem j p`, let η w_p⁻¹ g ∈ K for some η ∈ R^(j), and let s ∈ R^(j) with s g
∈ K. Let `p` be a head: the inverses of the products p₀ ⋯ p_(l-1), l ≤ j, have size 1. Then p_a, its
inverse and the entries of the column s e*_a have size 10 n, where n = `𝔰.n` = ϱ + 1. -/
lemma head_entries_mem_ofSize {K : Set T.G}
    (hK : ∀ ⦃x : T.G⦄, x ∈ K → S.HasMatrixSize 1 (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hj : j ≤ 𝔰.ϱ)
    (h_near : ∃ η : T.G, η ∈ partialUnitriangularGroup j ∧ η * ((weylElem j p)⁻¹ * g) ∈ K)
    (hs_near : s ∈ partialUnitriangularGroup j ∧ s * g ∈ K) (hp : S.IsHead j p) (ha : a < j) :
    (p a : A) ∈ S.ofSize (10 * 𝔰.n) ∧
    (((p a)⁻¹ : Aˣ) : A) ∈ S.ofSize (10 * 𝔰.n) ∧
    ∀ i : 𝔰.BesselIndex,
      (s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i (eStar a) ∈ S.ofSize (10 * 𝔰.n) := by
  -- Both p a and its inverse are quotients of two consecutive products p₀ ⋯ p_(l-1).
  let P (l : ℕ) : Aˣ := ∏ b ∈ Finset.range l, p b
  have h_quot {l m : ℕ} (hl : l ≤ j) (hm : m ≤ j) : ((P l)⁻¹ * P m).val ∈ S.ofSize (10 * 𝔰.n) :=
    mem_ofSize_mono (S.mul_mem_ofSize (hp l hl)
      (head_products_mem_ofSize hK hj h_near hs_near m hm))
  have h_succ : P (a + 1) = P a * p a := prod_range_succ p a
  refine ⟨?_, ?_, fun i ↦ ?_⟩
  · simpa only [h_succ, inv_mul_cancel_left] using h_quot ha.le ha
  · simpa only [h_succ, _root_.mul_inv_rev, inv_mul_cancel_right] using h_quot ha ha.le
  · simpa using mem_ofSize_mono (j := 10 * 𝔰.n) (dual_mem_vecsOfSize hK hj h_near hs_near hp ha i)

omit [IsHermitianUnit T.splitGram] in
/-- If p_a and its inverse have size i for all a < j with a < ϱ, then the inverse of the Weyl
element w_p = `weylElem j p` has size i: its entries are 0, 1, star p_a and p_a⁻¹. -/
lemma hasMatrixSize_weylElem_inv (hp : ∀ a : Fin 𝔰.ϱ, a < j → (p a : A) ∈ S.ofSize i)
    (hp_inv : ∀ a : Fin 𝔰.ϱ, a < j → (((p a)⁻¹ : Aˣ) : A) ∈ S.ofSize i) :
    S.HasMatrixSize i (((weylElem j p)⁻¹ : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) := by
  intro k m
  obtain ⟨h_zero, h_one⟩ := S.zero_one_mem_ofSize i
  by_cases hm : floorOf m < j ∧ floorOf m < 𝔰.ϱ
  · simp [weylElem, weylOn, hm.1, hm.2, apply_ite (· ∈ S.ofSize i), h_zero,
      star_mem_ofSize (hp ⟨_, hm.2⟩ hm.1), hp_inv ⟨_, hm.2⟩ hm.1]
  · simp [weylElem, weylOn, hm, apply_ite (· ∈ S.ofSize i), h_one, h_zero]

/-- Let j ≤ ϱ and let the isometry s lie in R^(j) = `partialUnitriangularGroup j` and in
`unipotentBelow j`. If the columns s e*_a, a < j, have size d, then s⁻¹ has size (4 (d + 1) + 12)
j + 5. -/
lemma hasMatrixSize_inv_of_mem_unipotentBelow {d : ℕ} (hj : j ≤ 𝔰.ϱ)
    (hs : s ∈ partialUnitriangularGroup j) (hs_unip : s ∈ unipotentBelow j)
    (h_col : ∀ a : Fin 𝔰.ϱ, a < j → ∀ i : 𝔰.BesselIndex,
      (s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i (eStar a) ∈ S.ofSize d) :
    S.HasMatrixSize ((4 * (d + 1) + 12) * j + 5)
      ((s⁻¹ : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) := by
  -- Compare the gauges at 1 and at 1 * s⁻¹. They agree on Y^(j), where s acts as 1, and the e*_a
  -- are short duals as the columns s e*_a have size d. This bounds s⁻¹ - 1.
  set c : ℕ := d + 1
  have h_top : S.GaugesDifferLe 1 (1 : T.G) (1 * s⁻¹) j 0 := by
    intro i ω hω _
    refine ⟨s⁻¹.val.val *ᵥ ω, hω.congrBelow_mulVec (inv_mem hs_unip), ?_⟩
    simp [vecsOfSize, zero_one_mem_ofSize]
  have h_lift (a : Fin 𝔰.ϱ) (ha : a.val < j) :
      S.InducedLengthLe (1 * s⁻¹) a c (Pi.single (inl a) 1) := by
    refine ⟨(1 * s⁻¹).val.val *ᵥ Pi.single (inl a) 1, fun k hk ↦ ?_,
      lengthLeAt_mulVec_iff.2 (single_mem_vecsOfSize (inl a))⟩
    simpa [Matrix.one_apply, Pi.single_apply] using
      mem_partialUnitriangularGroup.1 (inv_mem hs) k (inl a) hk (.inl ⟨ha, ha⟩)
  have h_dual (a : Fin 𝔰.ϱ) (ha : a.val < j) : S.HasShortDual 1 (1 : T.G) (1 * s⁻¹) a c := by
    have h_diff : (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ Pi.single (eStar a) 1 -
        s.val.val *ᵥ Pi.single (eStar a) 1 ∈ S.vecsOfSize c := by
      rw [one_mulVec, mulVec_single_one]
      exact sub_mem_vecsOfSize (single_mem_vecsOfSize (eStar a)) (h_col a ha)
    exact ⟨Pi.single (eStar a) 1, fun b hb ↦ Pi.single_eq_of_ne (by grind) 1, by simp,
      lengthLeAt_one_iff.2 (single_mem_vecsOfSize (eStar a)), Pi.single (eStar a) 1, .refl _ _,
      by simpa using h_diff⟩
  have h_differ : S.GaugesDifferLe 1 (1 : T.G) (1 * s⁻¹) 0 (0 + (4 * c + 12) * j) :=
    h_top.on_whole_space_of_hasShortDual (by simp) (S.zero_one_mem_ofSize 1).right hj
      (fun a _ ↦ ⟨_, .refl _ _, lengthLeAt_one_iff.2 (single_mem_vecsOfSize (inl a))⟩) h_lift h_dual
  have h_one_sub : S.HasMatrixSize ((4 * c + 12) * j + 4) (1 - s⁻¹.val.val) := fun a b ↦ by
    simpa using neg_mem_ofSize (h_differ.hasMatrixSize_sub_one (by simp) a b)
  simpa only [sub_sub_cancel] using HasMatrixSize.one.sub h_one_sub

/-- Let `K` be a set of isometries whose matrices have size 1, and let j ≤ ϱ. Let η w_p⁻¹ g ∈ K for
some η ∈ R^(j), and let s ∈ R^(j) with s g ∈ K. Let `p` be a head: the inverses of the products p₀ ⋯
p_(l-1), l ≤ j, have size 1. If s also lies in `unipotentBelow j`, then g has size 60 n² and w_p⁻¹ g
has size 99 n², with n = `𝔰.n` = ϱ + 1. -/
lemma hasMatrixSize_of_isHead {K : Set T.G}
    (hK : ∀ ⦃x : T.G⦄, x ∈ K → S.HasMatrixSize 1 (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hj : j ≤ 𝔰.ϱ)
    (h_near : ∃ η : T.G, η ∈ partialUnitriangularGroup j ∧ η * ((weylElem j p)⁻¹ * g) ∈ K)
    (hs_near : s ∈ partialUnitriangularGroup j ∧ s * g ∈ K) (hp : S.IsHead j p)
    (hs_unip : s ∈ unipotentBelow j) :
    S.HasMatrixSize (60 * 𝔰.n ^ 2) (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) ∧
    S.HasMatrixSize (99 * 𝔰.n ^ 2)
      (((weylElem j p)⁻¹ * g : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) := by
  -- Write g = s⁻¹ (s g). The columns s e*_a bound s⁻¹, and the entries of p bound w_p⁻¹.
  have h_entries (a : Fin 𝔰.ϱ) (ha : a < j) :
      (p a : A) ∈ S.ofSize (10 * 𝔰.n) ∧ (((p a)⁻¹ : Aˣ) : A) ∈ S.ofSize (10 * 𝔰.n) ∧
        ∀ i, (s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i (eStar a) ∈ S.ofSize (10 * 𝔰.n) :=
    head_entries_mem_ofSize hK hj h_near hs_near hp ha
  choose h_p h_p_inv h_col using h_entries
  obtain ⟨hs, hsK⟩ := hs_near
  have h_g : S.HasMatrixSize (60 * 𝔰.n ^ 2) (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) := by
    have h_prod : S.HasMatrixSize ((4 * (10 * 𝔰.n + 1) + 12) * j + 5 + 1 + 1)
        ((s⁻¹ * (s * g) : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) :=
      (hasMatrixSize_inv_of_mem_unipotentBelow hj hs hs_unip h_col).mul (hK hsK)
    rw [inv_mul_cancel_left] at h_prod
    -- The size is rounded up using j ≤ ϱ.
    exact h_prod.mono (by nlinarith)
  exact ⟨h_g, ((hasMatrixSize_weylElem_inv h_p h_p_inv).mul h_g).mono (by nlinarith)⟩

end Size

end Size

end New.Floors

end
end
end

section
/-!
# Volumes on quadrics and on sections

The equation of a quadric is solved in a block of orthonormal coordinates: the other coordinates
are free, and the points of size j of the fibres have mass bounded in terms of j. A section
⟨e_a, y⟩ = c of an isotropic cone, for a unit c, is an orbit of a Heisenberg group. The letters
G^(l), U_(<l) and Y^(l) are those of the head of `New.Spanning.Frames.Lengths`.

## Main definitions and results

* `New.Floors.Gauge.exists_isSolvedIn`: the quadric of a floor is solved in a block.
* `New.Floors.Gauge.setLIntegral_orthonormalPart_le`: integrals of functions of the orthonormal
  coordinates.
* `New.Floors.Gauge.lintegral_heisenbergMeasure_le`: integrals over a Heisenberg group.
* `New.Floors.sectionPoint`, `New.Floors.Gauge.setLIntegral_sectionMeasure_le`: sections and their
  measures.

Notions from other files:

* `Γ.ofSize j`, `Γ.vecsOfSize j`: the numbers of size j and the vectors whose entries have size j.
  The powers of the number `Γ.loss` bound moduli |u| = `modulus u` and volumes.
* `F.floorBasis b`: a basis of V_b, the span of the basis vectors of floor at least b (a space of
  representatives of Y^(b)), made of hyperbolic pairs and orthonormal vectors indexed by ι. The
  orthonormal vectors whose index lies in the range of `F.freeIndex : F.FreeIndex → ι` span X'.
* `IsSolvedIn blk ρ S B`: the measure ρ is the volume in the coordinates off the block `blk` times
  measures in the block, each of mass at most B on the vectors with coordinates in S.
* `heisenbergElem a (ω, β)`: the element of the Heisenberg group of floor a with vector part ω and
  skew part β.
* `CongrBelow l ω ω'`: the vectors ω and ω' differ by a combination of the e_b with b < l.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

@[expose] public section

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Sum Set Function FloorGroups Size Place TraceOne PlaceData
  HyperbolicBasis Finset

variable {A ι : Type} {𝔰 : Shape} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]
  [Place A] [Fintype ι] [DecidableEq ι] {C B I : ℝ≥0∞} {m j : ℕ} {p : ℕ → Aˣ} {a : Fin 𝔰.ϱ}
  {T : 𝔰.Form A} [IsHermitianUnit T.splitGram] {F : PlaceData ι T m} {Γ : Gauge F} {b : Fin 𝔰.n}

namespace Gauge

/-- If the vector with coordinates x in the basis `F.floorBasis b` of V_b has size j (all its
entries do), then x has size j + 4. -/
lemma mem_vecsOfSize_of_floorBasis_mulVec {x : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A}
    (h : F.floorBasis b *ᵥ x ∈ Γ.vecsOfSize j) :
    x ∈ Γ.vecsOfSize (j + 4) := by
  -- Each entry of the basis is zero, one or an entry of `F.basisMatrix`, and so has size 1.
  have h_basis : Γ.HasMatrixSize 1 (F.floorBasis b)ᴴ := fun i k ↦ by
    simp only [conjTranspose_apply, neg_mem_iff_and_star_mem_iff]
    revert k i
    simp [floorBasis, Matrix.mul_apply, inclMatrix, Matrix.one_apply, -ite_mul, sum_boole_mul,
      Γ.hasMatrixSize_basisMatrix _, zero_one_mem_ofSize, ite_mem]
  have h_pair := (h_basis.mul Γ.splitGram_and_inv_mem.1).mulVec h
  rw [mulVec_mulVec, gram_floorBasis, show 3 + j + 1 = j + 4 by lia] at h_pair
  -- The Gram matrix of the basis swaps the two entries of each pair and fixes the others.
  rintro (i | i | i | i)
  · fin_cases i
    · simpa [fromBlocks_mulVec, dotProduct] using h_pair (inl 1)
    · simpa [fromBlocks_mulVec, dotProduct] using h_pair (inl 0)
  · simpa [fromBlocks_mulVec] using h_pair (inr (inr (inr i)))
  · simpa [fromBlocks_mulVec] using h_pair (inr (inr (inl i)))
  · simpa [fromBlocks_mulVec] using h_pair (inr (inl i))

/-- The orthonormal basis vectors, indexed by ι, contain two blocks `blk₁`, `blk₂` of `F.blockRank`
distinct vectors each, disjoint from each other and from the basis of X', which `F.freeIndex`
indexes: the three index maps together form an injective map. -/
lemma exists_blocks (Γ : Gauge F) :
    ∃ blk₁ blk₂ : Fin F.blockRank → ι,
      Function.Injective (F.freeIndex ⊕ᵥ (blk₁ ⊕ᵥ blk₂)) := by
  have h_room : 2 * F.blockRank ≤ Fintype.card ι := Γ.two_mul_blockRank_le
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨fun i ↦ e ⟨Fintype.card ι - 2 * F.blockRank + i, by lia⟩,
    fun i ↦ e ⟨Fintype.card ι - F.blockRank + i, by lia⟩, ?_⟩
  -- The indices of X' come first and the two blocks fill the last `2 * F.blockRank` places.
  rintro (i | i | i) (k | k | k) h <;> simp [PlaceData.freeIndex, e, Fin.ext_iff] at h ⊢ <;> lia

/-- Let ρ be the volume `FloorGroups.floorVolume b` of V_b or the measure `F.floorQuadricMeasure b`
of a quadric in V_b. In the coordinates of the basis `F.floorBasis b`, ρ is solved in every block of
`F.blockRank` distinct orthonormal basis vectors. That is, the other coordinates are free, and over
each of their values the points of the block with all coordinates in `Γ.ofSize j` have mass at most
Λ^(`F.blockRank` (j+1)), where Λ = `Γ.loss` is the constant of the gauge Γ. -/
lemma exists_isSolvedIn {ρ : Measure (𝔰.BesselIndex → A)}
    (hρ : ρ = FloorGroups.floorVolume b ∨ ρ = F.floorQuadricMeasure b) :
    ∃ ρ₀ : Measure (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A),
      ρ = ρ₀.map (F.floorBasis b *ᵥ ·) ∧
      ∀ blk : Fin F.blockRank → ι, Function.Injective blk → ∀ j : ℕ,
        IsSolvedIn (inr ∘ inr ∘ inl ∘ blk) ρ₀ (Γ.ofSize j) (Γ.loss ^ (F.blockRank * (j + 1))) := by
  obtain rfl | rfl := hρ
  · refine ⟨volume, (F.map_floorBasis_volume b).symm, fun blk h_inj j ↦ ?_⟩
    have h_box : volume (Γ.ofSize j) ^ Fintype.card (Fin F.blockRank) ≤
        Γ.loss ^ (F.blockRank * (j + 1)) := by
      grw [volume_ofSize_le, ← pow_mul, Fintype.card_fin, mul_comm]
    exact isSolvedIn_volume
      (inr_injective.comp (inr_injective.comp (inl_injective.comp h_inj))) h_box
  · obtain ⟨l, hl_finite, hl, h_mass⟩ :
        ∃ l : ProbabilityTheory.Kernel (skewAdjoint A) (Fin F.blockRank → A),
          ProbabilityTheory.IsSFiniteKernel l ∧ IsDisintegration volume 1 l ∧
            ∀ (β : skewAdjoint A) (j : ℕ),
              l β (Γ.vecsOfSize j) ≤ Γ.loss ^ (F.blockRank * (j + 1)) := Γ.exists_blockKernel
    refine ⟨quadricMeasure (hyperbolicGram (FloorPairs b m) 1) _, rfl, fun blk h_inj j ↦ ?_⟩
    refine hl.isSolvedIn_quadricMeasure (fun β ↦ h_mass β j) ?_
      (inr_injective.comp (inl_injective.comp h_inj)) ?_ _
    · -- the Gram matrix off the first pair is hermitian
      simp [fromBlocks_conjTranspose, conjTranspose_fromRows_eq_fromCols_conjTranspose,
        conjTranspose_fromCols_eq_fromRows_conjTranspose]
    · -- the vectors of the block are orthonormal and orthogonal to the other basis vectors
      rintro i (k | k | k) <;> simp [Matrix.one_apply]

/-- The volume of `Γ.ofSize j` is raised to the number of coordinates of V_b lying outside X' and
outside one block of `F.blockRank` vectors. This power, times the bound Λ^(`F.blockRank` (j+1)) for
the mass in that block, is at most Λ^(99 n (j+2)), where Λ = `Γ.loss` and n = `𝔰.n`. -/
lemma volume_pow_mul_le :
    volume (Γ.ofSize j) ^ (Fintype.card (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) -
        Fintype.card F.FreeIndex - Fintype.card (Fin F.blockRank)) *
      Γ.loss ^ (F.blockRank * (j + 1)) ≤ Γ.loss ^ (99 * 𝔰.n * (j + 2)) := by
  -- There are at most `99 n` coordinates off X', and each costs at most `Λ ^ (j + 1)`.
  have h_pairs : Fintype.card (FloorPairs b m) ≤ m + 𝔰.ϱ := by
    simp [card_finset_fin_le, Fintype.card_subtype]
  have h_card : Fintype.card (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) -
      Fintype.card F.FreeIndex - Fintype.card (Fin F.blockRank) + F.blockRank ≤ 99 * 𝔰.n := by
    have h_le : m ≤ 9 * 𝔰.n := Γ.pairs_le
    simp only [Fintype.card_sum (α := Fin 2), Fintype.card_sum (α := FloorPairs b m),
      Fintype.card_sum (α := ι), Fintype.card_fin]
    lia
  set d : ℕ := Fintype.card (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) -
    Fintype.card F.FreeIndex - Fintype.card (Fin F.blockRank)
  calc volume (Γ.ofSize j) ^ d * Γ.loss ^ (F.blockRank * (j + 1))
      ≤ (Γ.loss ^ (j + 1)) ^ d * Γ.loss ^ (F.blockRank * (j + 1)) := by grw [volume_ofSize_le]
    _ = Γ.loss ^ ((d + F.blockRank) * (j + 1)) := by ring
    _ ≤ Γ.loss ^ (99 * 𝔰.n * (j + 2)) :=
        pow_le_pow_right₀ Γ.one_le_loss (Nat.mul_le_mul h_card (by lia))

/-- Passage to coordinates in the basis `F.floorBasis b` of V_b: the integral of `Φ` over
`Γ.vecsOfSize j` against the image of `ρ` under x ↦ `F.floorBasis b *ᵥ x` is at most the integral of
`Φ (F.floorBasis b *ᵥ x)` over x in `Γ.vecsOfSize (j + 4)` against `ρ`. -/
lemma setLIntegral_map_floorBasis_le
    {ρ : Measure (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A)}
    (Φ : (𝔰.BesselIndex → A) → ℝ≥0∞) :
    ∫⁻ v : 𝔰.BesselIndex → A in Γ.vecsOfSize j, Φ v ∂ρ.map (F.floorBasis b *ᵥ ·) ≤
      ∫⁻ x : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A in Γ.vecsOfSize (j + 4),
        Φ (F.floorBasis b *ᵥ x) ∂ρ := by
  simp only [← lintegral_indicator measurableSet_vecsOfSize]
  refine (lintegral_map_le _ (by fun_prop)).trans (lintegral_mono fun x ↦ ?_)
  by_cases hx : F.floorBasis b *ᵥ x ∈ Γ.vecsOfSize j
  · rw [indicator_of_mem hx, indicator_of_mem (mem_vecsOfSize_of_floorBasis_mulVec hx)]
  · simp [indicator_of_notMem hx]

/-- Let ρ be the volume of V_b, the span of the basis vectors of floor at least b, or the measure
`F.floorQuadricMeasure b` of a quadric in V_b. Let Λ = `Γ.loss`, n = `𝔰.n`, and let X' be the span
of the columns of `F.orthonormalPart`. If φ is measurable and has integral at most B over the
vectors of size j + 4 of X', then φ(y_X) has ρ-integral at most Λ^(99 n (j+6)) B over the vectors y
of size j. Here y_X = `F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ y` is the vector of the products of the
basis vectors of X' with y. -/
lemma setLIntegral_orthonormalPart_le {ρ : Measure (𝔰.BesselIndex → A)}
    {φ : (F.FreeIndex → A) → ℝ≥0∞}
    (hρ : ρ = FloorGroups.floorVolume b ∨ ρ = F.floorQuadricMeasure b)
    (hB : ∫⁻ w : F.FreeIndex → A in Γ.vecsOfSize (j + 4), φ w ≤ B)
    (hφ : Measurable φ := by fun_prop) :
    ∫⁻ y : 𝔰.BesselIndex → A in Γ.vecsOfSize j,
      φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ y) ∂ρ ≤ Γ.loss ^ (99 * 𝔰.n * (j + 6)) * B := by
  -- Pairing with the basis of X' reads off coordinates. Solve in a block disjoint from X'.
  have h_cols : F.orthonormalPart =
      (F.floorBasis b).submatrix id (inr ∘ inr ∘ inl ∘ F.freeIndex) := by
    simp [← ext_iff, Matrix.mul_apply, floorBasis, inclMatrix, Matrix.one_apply]
  have h_coord (x : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A) :
      F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ F.floorBasis b *ᵥ x =
        x ∘ inr ∘ inr ∘ inl ∘ F.freeIndex :=
    calc _ = ((F.floorBasis b)ᴴ *ᵥ T.splitGram *ᵥ F.floorBasis b *ᵥ x) ∘
            inr ∘ inr ∘ inl ∘ F.freeIndex := by
          rw [h_cols]
          rfl
      _ = (planeSumGram (hyperbolicGram (FloorPairs b m) (1 : Matrix ι ι A)) *ᵥ x) ∘
            inr ∘ inr ∘ inl ∘ F.freeIndex := by
          rw [← F.gram_floorBasis b, ← mulVec_mulVec, ← mulVec_mulVec]
      _ = _ := by simp [funext_iff, fromBlocks_mulVec]
  obtain ⟨ρ₀, rfl, h_solved⟩ := Γ.exists_isSolvedIn hρ
  obtain ⟨_, blk, h_inj⟩ := Γ.exists_blocks
  have h_blk : Function.Injective blk := h_inj.comp (inr_injective.comp inr_injective)
  have h_disjoint : Function.Injective (F.freeIndex ⊕ᵥ blk) := by
    simpa only [elim_comp_map, Function.comp_id, elim_comp_inr] using
      h_inj.comp (map_injective.2 ⟨Function.injective_id, inr_injective⟩)
  grw [setLIntegral_map_floorBasis_le, ← Γ.volume_pow_mul_le (b := b) (j := j + 4), ← hB]
  simp only [h_coord]
  refine (h_solved blk h_blk (j + 4)).setLIntegral_le (Γ.isCompact_ofSize _).measurableSet ?_ hφ
  simpa only [Function.comp_assoc, comp_elim] using
    inr_injective.comp (inr_injective.comp (inl_injective.comp h_disjoint))

/-- Let S be a set of skew elements and u a unit such that (β - β') / u has size j + 1 for all β, β'
in S. Then S has Haar measure at most |u|^(1/2) Λ^(j+2), where |u| is the modulus of u and
Λ = `Γ.loss`. -/
lemma skewMeasure_le_of_sub_mem_ofSize {S : Set (skewAdjoint A)} (u : Aˣ)
    (h_diff : ∀ β ∈ S, ∀ β' ∈ S, u⁻¹ * (β - β').val ∈ Γ.ofSize (j + 1)) :
    skewMeasure S ≤ Place.modulus u.val ^ (2⁻¹ : ℝ) * Γ.loss ^ (j + 2) := by
  -- For such differences `d₁, d₂` the number `(τ δ⁻¹ d₁ + d₂) / u` has size `j + 3`, where `τ` has
  -- trace one and `δ` is the skew unit. Hence the squared mass of `S` is at most `modulus u`
  -- times the volume of the numbers of size `j + 3`.
  refine skewMeasure_le_of_sub_mem u⁻¹ (C := Γ.ofSize (1 + (j + 1) + 1)) ?_ ?_
  · rintro ⟨β₁, β₂⟩ ⟨hβ₁, hβ₂⟩ ⟨β₁', β₂'⟩ ⟨hβ₁', hβ₂'⟩
    rw [Prod.mk_sub_mk]
    convert sub_mem_ofSize (Γ.mul_mem_ofSize Γ.traceOne_div_mem_ofSize (h_diff β₁ hβ₁ β₁' hβ₁'))
      (mem_ofSize_mono (h_diff β₂' hβ₂' β₂ hβ₂)) using 1
    push_cast
    ring
  · grw [volume_ofSize_le]
    simp only [modulus_inv, inv_inv, mul_pow, ← rpow_mul_natCast, Nat.cast_ofNat,
      inv_mul_cancel₀ (two_ne_zero' ℝ), rpow_one, ← pow_mul]
    gcongr
    · exact Γ.one_le_loss
    · lia

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- The integral over the skew variable in the Heisenberg group of floor a, with points
n = `heisenbergElem a (ω, β)`; a vector part such as ω is extended by zero to the floors at most a
(`inclMatrix`). Suppose that at each n with Φ(n) ≠ 0, w / u has size j for some w congruent to
(n⁻¹ - 1) e*_a modulo the e_b with b < a, and Φ(n) ≤ C Ψ(ω / u). Then for ω = u v the integral of Φ
over β is at most |u|^(1/2) `Γ.loss`^(j+2) C Ψ(v), and it vanishes unless v has size j. -/
lemma lintegral_heisenbergElem_skewMeasure_le {Φ : T.G → ℝ≥0∞} {Ψ : (𝔰.BesselIndex → A) → ℝ≥0∞}
    (u : Aˣ)
    (hΦ : ∀ t : ({k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A) × skewAdjoint A,
      Φ (heisenbergElem a t) ≠ 0 →
        (∃ w : 𝔰.BesselIndex → A,
          CongrBelow a
            (((heisenbergElem (T := T) a t)⁻¹.val.val - 1) *ᵥ Pi.single (eStar a) 1) w ∧
          u⁻¹.val • w ∈ Γ.vecsOfSize j) ∧
        Φ (heisenbergElem a t) ≤ C * Ψ (u⁻¹.val • inclMatrix A Subtype.val *ᵥ t.1))
    (v : {k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A) :
    ∫⁻ β : skewAdjoint A, Φ (heisenbergElem a (u.val • v, β)) ∂skewMeasure ≤
      Place.modulus u.val ^ (2⁻¹ : ℝ) * (Γ.loss ^ (j + 2) *
        (Γ.vecsOfSize j).indicator (C * Ψ ·) (inclMatrix A Subtype.val *ᵥ v)) := by
  let S : Set (skewAdjoint A) := support fun β ↦ Φ (heisenbergElem a (u.val • v, β))
  -- On the support `S` the vector `v` has size `j`, and so has `(c - β) / u`, where `c`
  -- does not depend on `β`.
  let Q (w : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) : A :=
    element * star (inclMatrix A Subtype.val *ᵥ w) ⬝ᵥ T.splitGram *ᵥ inclMatrix A Subtype.val *ᵥ w
  let c : A := skewPart (Q (u.val • v)) - Q (-(u.val • v))
  have h_supp (β : skewAdjoint A) (hβ : β ∈ S) :
      inclMatrix A Subtype.val *ᵥ v ∈ Γ.vecsOfSize j ∧
      u⁻¹ * (c - β) ∈ Γ.ofSize j ∧
      Φ (heisenbergElem a (u.val • v, β)) ≤ C * Ψ (inclMatrix A Subtype.val *ᵥ v) := by
    obtain ⟨⟨w, h_congr, h_short⟩, h_le⟩ := hΦ (u.val • v, β) hβ
    rw [heisenbergElem_inv] at h_congr
    obtain ⟨h_vec, h_skew⟩ :
        u⁻¹.val • inclMatrix A Subtype.val *ᵥ (-(u.val • v)) ∈ Γ.vecsOfSize j ∧
        u⁻¹ * ((skewPart (Q (u.val • v)) - β).val - Q (-(u.val • v))) ∈ Γ.ofSize j :=
      mem_vecsOfSize_of_congrBelow_heisenbergElem h_congr h_short
    refine ⟨?_, ?_, ?_⟩
    · simpa [mulVec_neg, vecsOfSize, mulVec_smul, neg_mem_iff_and_star_mem_iff] using h_vec
    · rwa [sub_right_comm]
    · simpa [smul_smul, mulVec_smul] using h_le
  have h_diff (β : skewAdjoint A) (hβ : β ∈ S) (β' : skewAdjoint A) (hβ' : β' ∈ S) :
      u⁻¹ * (β - β').val ∈ Γ.ofSize (j + 1) := by
    obtain ⟨-, h_near, -⟩ := h_supp β hβ
    obtain ⟨-, h_near', -⟩ := h_supp β' hβ'
    simpa [mul_sub] using sub_mem_ofSize h_near' h_near
  grw [← setLIntegral_eq_of_support_subset .rfl, ← mul_assoc, mul_comm,
    ← skewMeasure_le_of_sub_mem_ofSize u h_diff, ← setLIntegral_const]
  refine setLIntegral_mono measurable_const fun β hβ ↦ ?_
  obtain ⟨h_size, -, h_le⟩ := h_supp β hβ
  rwa [indicator_of_mem h_size]

/-- The integral over the Heisenberg group of floor a, with points n = `heisenbergElem a (ω, β)`,
where ω is extended by zero to the floors at most a (`inclMatrix`). Suppose that at each n with
Φ(n) ≠ 0, v / u has size j for some v congruent to (n⁻¹ - 1) e*_a modulo the e_b with b < a, and
Φ(n) ≤ C Ψ(ω / u). Let Ψ be measurable, with integral at most I over the vectors of size j for the
volume of V_(a+1). Then the integral of Φ for `heisenbergMeasure a` is at most C B for any
B ≥ |u|^(r + 1/2) Λ^(j+2) I. Here Λ = `Γ.loss`, r is the number of coordinates of ω, and
|u|^(r + 1/2) is `F.floorModulus a u`. -/
lemma lintegral_heisenbergMeasure_le {Φ : T.G → ℝ≥0∞} {Ψ : (𝔰.BesselIndex → A) → ℝ≥0∞} (u : Aˣ)
    (hI : ∫⁻ x : 𝔰.BesselIndex → A in Γ.vecsOfSize j, Ψ x ∂FloorGroups.floorVolume a.succ ≤ I)
    (hΦ : ∀ t : ({k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A) × skewAdjoint A,
      Φ (heisenbergElem a t) ≠ 0 →
        (∃ v : 𝔰.BesselIndex → A,
          CongrBelow a
            (((heisenbergElem (T := T) a t)⁻¹.val.val - 1) *ᵥ Pi.single (eStar a) 1) v ∧
          u⁻¹.val • v ∈ Γ.vecsOfSize j) ∧
        Φ (heisenbergElem a t) ≤ C * Ψ (u⁻¹.val • inclMatrix A Subtype.val *ᵥ t.1))
    (hB : F.floorModulus a u * (Γ.loss ^ (j + 2) * I) ≤ B := by
      simp [floorModulus]
      ring_nf
      gcongr <;> simp)
    (hΨ : Measurable Ψ := by fun_prop) :
    ∫⁻ n : T.G, Φ n ∂heisenbergMeasure a ≤ C * B := by
  -- Scale the coordinates `ω` of `V_(a+1)` by `u`, and integrate first over the skew variable.
  let D : Matrix {k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} {k : 𝔰.BesselIndex // a + 1 ≤ floorOf k}
    A := u.val • 1
  have hD : IsUnit D.det := by simp [D, IsUnit.pow]
  set r : ℕ := 𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1))
  have h_jacobian : Place.modulus D.det = Place.modulus u.val ^ r := by
    rw [det_smul, det_one, mul_one, card_subtype_succ_le_floorOf_eq, map_pow]
  let χ : (𝔰.BesselIndex → A) → ℝ≥0∞ := (Γ.vecsOfSize j).indicator (C * Ψ ·)
  have hχ : Measurable χ := .indicator (by fun_prop) measurableSet_vecsOfSize
  have h_integral : ∫⁻ v : {k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A,
      χ (inclMatrix A Subtype.val *ᵥ v) ≤ C * I :=
    calc _ = ∫⁻ x, χ x ∂FloorGroups.floorVolume a.succ := (lintegral_map hχ (by fun_prop)).symm
      _ ≤ C * I := by grw [lintegral_indicator_le, lintegral_const_mul C hΨ, hI]
  calc ∫⁻ n : T.G, Φ n ∂heisenbergMeasure a
      ≤ ∫⁻ ω, ∫⁻ β, Φ (heisenbergElem a (ω, β)) ∂skewMeasure := by
        rw [heisenbergMeasure, dite_eq_left a.isLt]
        grw [lintegral_map_le _ (by fun_prop), lintegral_prod_le]
    _ ≤ Place.modulus u.val ^ r * ∫⁻ v, ∫⁻ β, Φ (heisenbergElem a (D *ᵥ v, β)) ∂skewMeasure := by
        grw [lintegral_eq_mul_lintegral_map (map_mulVec_volume _ D hD) (by simp [h_jacobian])
          (by simp [h_jacobian]), lintegral_map_le _ (by fun_prop), h_jacobian]
    _ ≤ Place.modulus u.val ^ r * ∫⁻ v : {k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A,
          Place.modulus u.val ^ (2⁻¹ : ℝ) *
            (Γ.loss ^ (j + 2) * χ (inclMatrix A Subtype.val *ᵥ v)) := by
        gcongr with v
        simpa [D, smul_mulVec] using lintegral_heisenbergElem_skewMeasure_le u hΦ v
    _ ≤ F.floorModulus a u * (Γ.loss ^ (j + 2) * (C * I)) := by
        grw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp [loss_ne_top]),
          h_integral, floorModulus, mul_assoc]
    _ ≤ C * B := by grw [← hB, mul_left_comm C, mul_left_comm C]

end Gauge

/-! ### Sections of the isotropic cones -/

/-- The vector c n⁻¹ e*_a. For n in the Heisenberg group of floor a it is a point of the section
⟨e_a, y⟩ = c of the isotropic cone of Y^(a). -/
noncomputable def sectionPoint (a : Fin 𝔰.ϱ) (c : A) (n : T.G) : 𝔰.BesselIndex → A :=
  c • n⁻¹.val.val *ᵥ Pi.single (eStar a) 1

/-- The measure dy / dc = |c|^r dn of the section ⟨e_a, y⟩ = c, where r is the rank of Y^(a+1),
|c| = `modulus c`, and dn is `heisenbergMeasure a` carried over by `sectionPoint a c`. -/
noncomputable def sectionMeasure (T : 𝔰.Form A) [IsHermitianUnit T.splitGram] (a : Fin 𝔰.ϱ)
    (c : A) : Measure (𝔰.BesselIndex → A) :=
  modulus c ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1))) •
    (heisenbergMeasure a).map (sectionPoint (T := T) a c)

omit [IsHermitianUnit T.splitGram] in
@[fun_prop]
lemma measurable_sectionPoint (c : A) : Measurable (sectionPoint (T := T) a c) := by
  unfold sectionPoint
  fun_prop

/-- The coordinates of a point of a section: for the Heisenberg element n = `heisenbergElem a t`
with t = (ω, β), the point c n⁻¹ e*_a is c (e*_a - ω) plus a multiple of c e_a. Here ω is extended
by zero to the floors at most a. -/
lemma exists_sectionPoint_heisenbergElem_eq (c : A)
    (t : ({k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A) × skewAdjoint A) :
    ∃ μ : A, sectionPoint a c (heisenbergElem (T := T) a t) =
      c • (Pi.single (eStar a) 1 - inclMatrix A Subtype.val *ᵥ t.1 + μ • Pi.single (inl a) 1) := by
  rw [sectionPoint, heisenbergElem_inv, heisenbergElem_mulVec, Pi.single_eq_same, one_smul,
    mulVec_neg, ← sub_eq_add_neg]
  exact ⟨_, rfl⟩

section

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermitianUnit T.splitGram]

/-- If n fixes the basis vectors of floor below a, the coordinates of floor below a of the vector
c n⁻¹ e*_a = `sectionPoint a c n` vanish. -/
lemma sectionPoint_apply_eq_zero_of_floorOf_lt {c : A} {n : T.G} {k : 𝔰.BesselIndex}
    (hn : n ∈ floorGroup a) (hk : floorOf k < a) : sectionPoint a c n k = 0 := by
  have h_ne : k ≠ eStar a := fun h ↦ by simp [h] at hk
  have h_entry : n⁻¹.val.val k (eStar a) = 0 := by
    rw [apply_eq_one_apply_of_mem_floorGroup (inv_mem hn) k _ (.inl ⟨hk, hk.trans a.isLt⟩),
      one_apply_ne h_ne]
  rw [sectionPoint, mulVec_single_one, Pi.smul_apply, col_apply, h_entry, smul_zero]

/-- Let the isometry n of the form `T` fix the basis vectors of floor below a (`floorGroup a`), and
let z be congruent to the point c n⁻¹ e*_a = `sectionPoint a c n` modulo the e_b with b < a
(`CongrBelow a`). If all entries of z have size j for the scale `S` (`S.vecsOfSize j`), then so
have those of the point, whose coordinates of floor below a vanish. -/
lemma Size.sectionPoint_mem_vecsOfSize {S : Size T} {c : A} {n : T.G} {z : 𝔰.BesselIndex → A}
    (hn : n ∈ floorGroup a) (hz : CongrBelow a (sectionPoint a c n) z)
    (h_size : z ∈ S.vecsOfSize j) : sectionPoint a c n ∈ S.vecsOfSize j := by
  intro k
  by_cases hk : a.val ≤ BesselIndex.level k
  · rw [← hz k hk]
    exact h_size k
  · have h_floor : floorOf k < a := by grind [floorOf_level_cases k]
    simp [sectionPoint_apply_eq_zero_of_floorOf_lt hn h_floor, S.zero_one_mem_ofSize]

open BesselIndex in
/-- Let p be a sequence of units and a < l. The Weyl element w_p = `weylElem l p` sends e_a to
p_a e*_a, so the coordinate of w_p v at e*_a (index `eStar a`) is p_a times the coordinate of v at
e_a (index `inl a`). -/
lemma weylElem_mulVec_eStar {l : ℕ} (ha : a < l) (v : 𝔰.BesselIndex → A) :
    ((weylElem l p : T.G).val.val *ᵥ v) (eStar a) = p a * v (inl a) := by
  -- The row of `w_p` at `e*_a` has its only nonzero entry in the column of `e_a`.
  have h_zero (k : 𝔰.BesselIndex) (hk : k ≠ inl a) :
      (weylElem l p : T.G).val.val (eStar a) k = 0 := by
    have h_ne : eStar a ≠ if floorOf k < l ∧ floorOf k < 𝔰.ϱ then oppositeIndex k else k := by
      split_ifs with h_swap
      · intro h
        have h_opp : oppositeIndex (oppositeIndex k) = oppositeIndex (eStar a) := by rw [← h]
        exact hk (by simpa [oppositeIndex_involutive_and_floorOf_level] using h_opp)
      · exact fun h ↦ h_swap (by simp [← h, ha])
    simp [weylElem, weylOn, h_ne]
  have h_entry : (weylElem l p : T.G).val.val (eStar a) (inl a) = p a := by
    simp [weylElem, weylOn, level, ha]
  rw [mulVec_apply_eq_sum, Fintype.sum_eq_single (inl a) fun k hk ↦ by rw [h_zero k hk, zero_mul],
    h_entry]

open BesselIndex in
/-- For the Weyl element w_p = `weylElem (a + 1) p` of the first a + 1 hyperbolic pairs and an
isometry σ, the point (w_p σ)⁻¹ e_a of the orbit of e_a is (star p_a) σ⁻¹ e*_a. -/
lemma orbitPoint_weylElem_mul (σ : T.G) :
    orbitPoint a.castSucc (weylElem (a + 1) p * σ) =
      star (p a).val • σ⁻¹.val.val *ᵥ Pi.single (eStar a) 1 := by
  have h_weyl : (weylElem (a + 1) p : T.G)⁻¹.val.val *ᵥ Pi.single (inl a) 1 =
      star (p a).val • Pi.single (eStar a) 1 := by
    ext k
    simp [weylElem, weylOn, level, Pi.single_apply]
  simp [orbitPoint, ← mulVec_mulVec, -mulVec_single, mulVec_smul, -Subgroup.coe_inv,
    -InvMemClass.coe_inv, h_weyl]

/-- For n in G^(a) = `floorGroup a`, ν in U_(<a) = `unipotentBelow a` and the Weyl element
w_p = `weylElem (a + 1) p`, the vector (w_p n ν)⁻¹ e_a is congruent to
(star p_a) n⁻¹ e*_a = `sectionPoint a (star p_a) n` modulo the e_b with b < a. -/
lemma congrBelow_sectionPoint_orbitPoint {n ν : T.G} (hn : n ∈ floorGroup a)
    (hν : ν ∈ unipotentBelow a) :
    CongrBelow a (sectionPoint a (star (p a).val) n)
      (orbitPoint a.castSucc (weylElem (a + 1) p * (n * ν))) := by
  have h_lift : orbitPoint a.castSucc (weylElem (a + 1) p * (n * ν)) =
      ν⁻¹.val.val *ᵥ sectionPoint a (star (p a).val) n := by
    simp [orbitPoint_weylElem_mul, sectionPoint, ← mulVec_mulVec, -mulVec_single, mulVec_smul]
  rw [h_lift]
  have h_orth (b : Fin 𝔰.ϱ) (hb : b.val < a.val) :
      sectionPoint a (star (p a).val) n (eStar b) = 0 :=
    sectionPoint_apply_eq_zero_of_floorOf_lt hn (by simpa using hb)
  exact IsOrthogonalBelow.congrBelow_mulVec h_orth (inv_mem hν)

end

open BesselIndex in
/-- If ω and ω' are congruent modulo the e_b with b < l, where l ≤ ϱ, then they have the same
products with the basis vectors of X', the columns of `F.orthonormalPart`. -/
lemma CongrBelow.orthonormalPart_conjTranspose_mulVec_eq {l : ℕ} {ω ω' : 𝔰.BesselIndex → A}
    (h : CongrBelow l ω ω') (hl : l ≤ 𝔰.ϱ) :
    F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ ω' = F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ ω := by
  have h_middle (k : 𝔰.MiddleIndex) : ω' (inr (inl k)) = ω (inr (inl k)) :=
    h (inr (inl k)) (by simpa [level] using hl)
  ext i
  simp [-mulVec_mulVec, Shape.Form.splitGram, hyperbolicGram, fromBlocks_mulVec,
    mulVec_apply_eq_sum, h_middle]

/-- Let the head p of length a + 1 be adapted to the scale. Let y be in the box `F.boxSet`, n in the
Heisenberg group `floorUnipotent a` of floor a, and ν in U_(<a) = `unipotentBelow a`. Suppose w_p n
ν y is near at a + 1 (`F.IsNear`), that is, R^(a+1) w_p n ν y meets the box. Then the point (star
p_a) n⁻¹ e*_a, which lies in the section of the vectors v with ⟨e_a, v⟩ = star p_a, has size
`20 * 𝔰.n`: all its entries lie in `Γ.ofSize (20 * 𝔰.n)`. Here w_p = `weylElem (a + 1) p`,
R^(a+1) = `partialUnitriangularGroup (a + 1)`, and the point is `sectionPoint a (star p_a) n`. -/
lemma Gauge.sectionPoint_mem_vecsOfSize_of_isNear {y n ν : T.G} (hp : Γ.IsHead (a + 1) p)
    (hy : y ∈ F.boxSet) (hn : n ∈ floorUnipotent a) (hν : ν ∈ unipotentBelow a)
    (h_near : F.IsNear (a + 1) (weylElem (a + 1) p * (n * ν) * y)) :
    sectionPoint a (star (p a).val) n ∈ Γ.vecsOfSize (20 * 𝔰.n) := by
  -- For the head `star p`, `star (p a)` and `(n ν)⁻¹ e*_a` have size `10 * 𝔰.n`.
  obtain ⟨h_unit, -, h_col⟩ := head_entries_mem_ofSize Γ.hasMatrixSize_boxSet a.isLt
    (by simpa [IsNear, mul_assoc] using h_near)
    ⟨inv_mem (mul_mem (unipotentBelow_le_partialUnitriangularGroup hn.2)
      (unipotentBelow_le_partialUnitriangularGroup hν)), by simpa [← mul_assoc] using hy⟩
    hp.star_head .refl
  refine sectionPoint_mem_vecsOfSize hn.1 (congrBelow_sectionPoint_orbitPoint hn.1 hν) fun k ↦ ?_
  rw [orbitPoint_weylElem_mul, mulVec_single_one]
  exact mem_ofSize_mono (Γ.mul_mem_ofSize h_unit (h_col k))

/-- Integration over a section. If φ is measurable and has integral at most B over the vectors of
size j + 5 of X', then φ(y_X) has integral at most |c|^(-1/2) Λ^(j+3) Λ^(99 n (j+7)) B over the
points y of size j of the section ⟨e_a, y⟩ = c, for a unit c. Here
y_X = `F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ y` is the vector of the products of the basis vectors
of X', which are indexed by `F.FreeIndex`, with y; the section carries `sectionMeasure T a c`;
|c| = `modulus c`, Λ = `Γ.loss` and n = `𝔰.n`. -/
lemma Gauge.setLIntegral_sectionMeasure_le {φ : (F.FreeIndex → A) → ℝ≥0∞} (c : Aˣ)
    (hB : ∫⁻ w : F.FreeIndex → A in Γ.vecsOfSize (j + 5), φ w ≤ B)
    (hφ : Measurable φ := by fun_prop) :
    ∫⁻ y : 𝔰.BesselIndex → A in Γ.vecsOfSize j,
        φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ y) ∂sectionMeasure T a c ≤
      modulus c⁻¹.val ^ (2⁻¹ : ℝ) * (Γ.loss ^ (j + 3) * (Γ.loss ^ (99 * 𝔰.n * (j + 7)) * B)) := by
  -- Integrate over the Heisenberg group at the scale `-1 / c`. The power of `|c|` in
  -- `sectionMeasure` cancels against that in `F.floorModulus a c⁻¹`, leaving `|c|^(-1/2)`.
  have h_heisenberg : ∫⁻ n : T.G, (Γ.vecsOfSize j).indicator
      (fun y ↦ φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ y)) (sectionPoint a c.val n)
        ∂heisenbergMeasure a ≤
      1 * (F.floorModulus a c⁻¹ * (Γ.loss ^ (j + 3) * (Γ.loss ^ (99 * 𝔰.n * (j + 7)) * B))) := by
    refine lintegral_heisenbergMeasure_le (j := j + 1) (-c)⁻¹
      (setLIntegral_orthonormalPart_le (.inl rfl) hB) (fun t h_ne ↦ ?_) (by simp [floorModulus])
    obtain ⟨μ, hμ⟩ := exists_sectionPoint_heisenbergElem_eq (T := T) c.val t
    have h_size : sectionPoint a c.val (heisenbergElem (T := T) a t) ∈ Γ.vecsOfSize j :=
      mem_of_indicator_ne_zero h_ne
    have hc : c.val ∈ Γ.ofSize j := by simpa [hμ, inclMatrix_val_mulVec] using h_size (eStar a)
    have h_coord :
        F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ sectionPoint a c.val (heisenbergElem (T := T) a t) =
          F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ (-c).val • inclMatrix A Subtype.val *ᵥ t.1 := by
      simp [hμ, mulVec_add, mulVec_sub, mulVec_smul, -mulVec_mulVec, mulVec_neg, splitGram_col,
        funext_iff]
    have h_short : (-c)⁻¹⁻¹.val • ((heisenbergElem (T := T) a t)⁻¹.val.val - 1) *ᵥ
        Pi.single (eStar a) 1 ∈ Γ.vecsOfSize (j + 1) := fun k ↦ by
      simpa [sectionPoint, mul_sub, neg_add_eq_sub] using sub_mem_ofSize
        (Γ.mul_mem_ofSize hc (HasMatrixSize.one (i := 0) k (eStar a))) (h_size k)
    refine ⟨⟨_, .refl _ _, h_short⟩, ?_⟩
    rw [indicator_of_mem h_size, h_coord, one_mul, inv_inv]
  rw [← lintegral_indicator measurableSet_vecsOfSize, sectionMeasure, lintegral_smul_measure,
    lintegral_map (.indicator (by fun_prop) measurableSet_vecsOfSize) (by fun_prop)]
  grw [h_heisenberg]
  simp [floorModulus, ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel]

end New.Floors
end
end

/-!
# Plancherel's formula on quadrics

Cauchy–Schwarz in the fibres and Plancherel's formula in the orthonormal coordinates bound a Fourier
kernel between two quadrics. Along a Heisenberg group a partial correlation is a Fourier transform
in the next frame vector. The letters G^(l), R^(l), U_(<l), Y^(l) are those of the head of
`New.Spanning.Frames.Lengths`, and K, M those of `New.Spanning.Frames.Levels`.

## Main definitions and results

* `New.Floors.Gauge.fourierSqNormLe_floorQuadricMeasure`: the kernel from the quadric of a floor to
  the same quadric or to the whole floor, by solving in two disjoint blocks.
* `New.Floors.Gauge.partialCorrelation_heisenbergElem_eq_integral`: the correlation along a
  Heisenberg group.
* `New.Floors.Gauge.parseval_heisenbergMeasure_le`: Parseval's inequality along a Heisenberg group.

Notions from other files:
* `F.partialCorrelation l k g y`: the correlation from floor l on, an integral of k(σ g, σ y).
* `F.IsPairingKernel l k d`: the rules obeyed by an orbital integral twisted by d.
* `orbitPoint b σ`: the vector σ⁻¹ f_b, for the b-th frame vector f_b; its law on floor b is
  `F.floorQuadricMeasure b`.
* `Γ.vecsOfSize i`, `Γ.HasMatrixSize i`: vectors and matrices all of whose entries have size i.
* `FourierSqNormLe`: a bound for the kernel ψ(ξ ⟨v, y⟩) on square norms.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

@[expose] public section

namespace New.Floors.Gauge

open Matrix MeasureTheory BesselIndex ENNReal Fintype FloorGroups ProbabilityTheory Size Set
  PlaceData U
  Place Finset

variable {A ι : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {𝔰 : Shape} [Fintype ι] [DecidableEq ι] {m j : ℕ}
  {T : 𝔰.Form A} [IsHermitianUnit T.splitGram]
  {F : PlaceData ι T m} (Γ : Gauge F) {x t q : T.G} {b : Fin 𝔰.n} (a : Fin 𝔰.ϱ) {k : T.G → T.G → ℂ}
  {d : T.G} {p : ℕ → Aˣ}

/-! ### Masses on the floors and Fourier kernels -/

/-- Let f be measurable and left invariant under R^(b+1) = `partialUnitriangularGroup (b + 1)`. For
each g ∈ K let f(σ g) be at most Ψ(σ⁻¹ f_b) for σ in `floorGroup b`, with f_b the b-th frame vector,
where σ⁻¹ f_b = `orbitPoint b σ` and the measurable function Ψ has integral at most C over the
vectors of size 7 of the quadric of floor b. Then for every g the integral of f(σ g) over the σ on
floor b with σ g near at b + 1 (that is, R^(b+1) σ g meets K) is at most C. -/
lemma floorMassLe_of_chart {f : T.G → ℝ≥0∞} {C : ℝ≥0∞}
    (hf_inv : (partialUnitriangularGroup (b + 1)).FixesLeft f)
    (h_chart : ∀ g ∈ F.boxSet, ∃ Ψ : (𝔰.BesselIndex → A) → ℝ≥0∞,
      ∫⁻ v : 𝔰.BesselIndex → A in Γ.vecsOfSize 7, Ψ v ∂F.floorQuadricMeasure b ≤ C ∧
      Measurable Ψ ∧
      ∀ σ ∈ floorGroup b, f (σ * g) ≤ Ψ (orbitPoint b σ))
    (hf : Measurable f := by fun_prop) :
    F.FloorMassLe b C f := by
  classical
  -- If some `σ * g` is near at `b + 1`, then `ξ * g` lies in K for some `ξ` in
  -- `partialUnitriangularGroup b`, and the integral does not change when `g` is replaced by
  -- `ξ * g`. The vectors `σ⁻¹ f_b` that count then have size `1 + 6`.
  intro g
  let Φ : T.G → ℝ≥0∞ := {z | F.IsNear (b + 1) z}.indicator f
  have hΦ : Measurable Φ := hf.indicator measurableSet_isNear
  refine (lintegral_indicator (measurable_mul_const g measurableSet_isNear) _).ge.trans ?_
  change ∫⁻ σ, Φ (σ * g) ∂F.floorMeasure b ≤ C
  obtain h_far | ⟨ξ, hξ, h_box⟩ := em' (F.IsNear b g)
  · have h_zero (σ : T.G) (hσ : σ ∈ floorGroup b) : Φ (σ * g) = 0 :=
      ite_eq_right fun h_near ↦ h_far (IsNear.of_floorGroup_mul h_near hσ le_self_add)
    grw [lintegral_le_of_ae_imp ae_floorMeasure_mem (g := 0) fun σ hσ ↦ (h_zero σ hσ).le]
    simp
  obtain ⟨Ψ, hΨ_int, hΨ_meas, hΨ_le⟩ : ∃ Ψ : (𝔰.BesselIndex → A) → ℝ≥0∞,
      ∫⁻ v in Γ.vecsOfSize 7, Ψ v ∂F.floorQuadricMeasure b ≤ C ∧ Measurable Ψ ∧
      ∀ σ ∈ floorGroup b, f (σ * (ξ * g)) ≤ Ψ (orbitPoint b σ) :=
    h_chart (ξ * g) h_box
  have hΦ_inv : (partialUnitriangularGroup (b + 1) ⊓ ⊤).FixesLeft fun σ : T.G ↦ Φ (σ * g) := by
    simp +contextual [Φ, indicator, hf_inv, mul_assoc]
  have hΦ_le (σ : T.G) (hσ : σ ∈ floorGroup b) :
      Φ (σ * ξ * g) ≤ (Γ.vecsOfSize 7).indicator Ψ (orbitPoint b σ) := by
    rw [mul_assoc]
    refine indicator_apply_le' (fun h_near ↦ ?_) fun _ ↦ zero_le
    have h_size : orbitPoint b σ ∈ Γ.vecsOfSize 7 :=
      orbitPoint_mem_vecsOfSize hσ (Γ.hasMatrixSize_boxSet h_box) h_near
    rw [indicator_of_mem h_size]
    exact hΨ_le σ hσ
  calc ∫⁻ σ, Φ (σ * g) ∂F.floorMeasure b
    _ = ∫⁻ σ, Φ (σ * ξ * g) ∂F.floorMeasure b :=
      (lintegral_floorMeasure_mul_right le_top hΦ_inv ⟨hξ, Subgroup.mem_top ξ⟩).symm
    _ ≤ ∫⁻ σ, (Γ.vecsOfSize 7).indicator Ψ (orbitPoint b σ) ∂F.floorMeasure b :=
      lintegral_le_of_ae_imp ae_floorMeasure_mem hΦ_le
    _ = ∫⁻ v, (Γ.vecsOfSize 7).indicator Ψ v ∂F.floorQuadricMeasure b :=
      (measurePreserving_orbitPoint b).lintegral_comp (hΨ_meas.indicator measurableSet_vecsOfSize)
    _ ≤ C := (lintegral_indicator_le Ψ (Γ.vecsOfSize 7)).trans hΨ_int

/-- Bounded mass. The measure of the quadric of floor b is the image, under the basis
`F.floorBasis b`, of `quadricMeasure` for the hyperbolic pairs `FloorPairs b m` and the orthonormal
vectors ι, at some value β of the form. If the coordinate vectors of size 11 have mass at most M
for every β, then for every g the σ on floor b with σ g near at b + 1 (`F.IsNear`) have mass at
most M. -/
lemma floorMassLe_one_of_le (b : Fin 𝔰.n) {M : ℝ≥0∞}
    (h_mass : ∀ β : skewAdjoint A,
      quadricMeasure (hyperbolicGram (FloorPairs b m) (1 : Matrix ι ι A)) β (Γ.vecsOfSize 11) ≤ M) :
    F.FloorMassLe b M 1 := by
  refine Γ.floorMassLe_of_chart (by simp) fun _ _ ↦ ⟨1, ?_, measurable_one, by simp⟩
  -- vectors of size `7` have coordinates of size `7 + 4`
  refine (setLIntegral_map_floorBasis_le (j := 7) 1).trans ?_
  simpa [Set.univ_inter] using h_mass _

/-- For every g, the σ on floor b with σ g near at b + 1 (`F.IsNear`) have mass at most
Λ^(99 · 13 n) times the volume of the vectors of size 11 in X'. Here Λ = `Γ.loss` is the constant of
the gauge, n = `𝔰.n`, and X' is spanned by the orthonormal vectors indexed by `F.FreeIndex`. -/
lemma floorMassLe_one (b : Fin 𝔰.n) :
    F.FloorMassLe b
      (Γ.loss ^ (99 * 𝔰.n * (7 + 6)) * volume (Γ.ofSize 11) ^ Fintype.card F.FreeIndex) 1 := by
  refine Γ.floorMassLe_of_chart (by simp) fun _ _ ↦ ⟨1, ?_, measurable_one, by simp⟩
  have h_vol : ∫⁻ _ : F.FreeIndex → A in Γ.vecsOfSize (7 + 4), 1 ≤
      volume (Γ.ofSize 11) ^ Fintype.card F.FreeIndex :=
    (setLIntegral_one _).le.trans (volume_coordinateBox F.FreeIndex (Γ.ofSize 11)).le
  exact setLIntegral_orthonormalPart_le (φ := 1) (.inr rfl) h_vol measurable_one

/-- Let ρ be the volume `floorVolume b` of Y^(b) or the measure of the quadric of floor b. The
kernel ψ(ξ ⟨v, y⟩), from the vectors y of size j on the quadric to the vectors v of size i with the
measure ρ, multiplies square norms by at most Λ^(99 n (i+6)) Λ^(99 n (j+6)) (c / |ξ|)^(rank X').
Here Λ = `Γ.loss` is the constant of the gauge, n = `𝔰.n`, c = `P.kernelBound`, |ξ| = `P.modulus ξ`
and rank X' = `card F.FreeIndex`. -/
lemma fourierSqNormLe_floorQuadricMeasure (ξ : Aˣ) {ρ : Measure (𝔰.BesselIndex → A)} {i : ℕ}
    (hρ : ρ = FloorGroups.floorVolume b ∨ ρ = F.floorQuadricMeasure b) :
    FourierSqNormLe T.splitGram ξ ρ (F.floorQuadricMeasure b) (Γ.vecsOfSize i) (Γ.vecsOfSize j)
      (Γ.loss ^ (99 * 𝔰.n * (i + 6)) * Γ.loss ^ (99 * 𝔰.n * (j + 6)) *
        (P.kernelBound / P.modulus ξ) ^ Fintype.card F.FreeIndex) := by
  -- In the coordinates of the basis `F.floorBasis b`, solve for `v` and `y` in different blocks.
  obtain ⟨ρ', rfl, h_solved'⟩ := Γ.exists_isSolvedIn hρ
  obtain ⟨ρ₀, h_eq, h_solved⟩ := Γ.exists_isSolvedIn (b := b) (.inr rfl)
  obtain ⟨blk', blk, h_inj⟩ : ∃ blk' blk : Fin F.blockRank → ι,
      Function.Injective (F.freeIndex ⊕ᵥ (blk' ⊕ᵥ blk)) := Γ.exists_blocks
  have h_inj' : Function.Injective blk' := h_inj.comp (Sum.inr_injective.comp Sum.inl_injective)
  have h_inj₀ : Function.Injective blk := h_inj.comp (Sum.inr_injective.comp Sum.inr_injective)
  have h_phase (v y : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A) :
      ξ * star (F.floorBasis b *ᵥ v) ⬝ᵥ T.splitGram *ᵥ F.floorBasis b *ᵥ y =
        ξ * star v ⬝ᵥ planeSumGram (hyperbolicGram (FloorPairs b m) (1 : Matrix ι ι A)) *ᵥ y := by
    rw [← F.gram_floorBasis b, star_mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec]
  rw [h_eq]
  refine FourierSqNormLe.map ?_ (by fun_prop) (by fun_prop) h_phase measurableSet_vecsOfSize
    (fun _ ↦ mem_vecsOfSize_of_floorBasis_mulVec) fun _ ↦ mem_vecsOfSize_of_floorBasis_mulVec
  refine (IsSolvedIn.fourierSqNormLe (inner := .inr ∘ .inr ∘ .inl ∘ F.freeIndex)
    (h_solved' blk' h_inj' (i + 4)) (h_solved blk h_inj₀ (j + 4))
    (Γ.isCompact_ofSize (i + 4)).measurableSet ?_ ?_ ξ).mono ?_
  · have h_incl : Function.Injective
        (.inr ∘ .inr ∘ .inl : ι → Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) :=
      Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inl_injective)
    simpa only [Sum.comp_elim, Function.comp_assoc] using h_incl.comp h_inj
  · -- the rows of the Gram matrix at the orthonormal vectors are those of the identity
    rintro (i | i) (k | k | k | k) <;> simp [Matrix.one_apply]
  · -- the outer coordinates and one block cost `Λ ^ (99 n (l + 6))` at size `l + 4`
    grw [volume_pow_mul_le (j := i + 4), volume_pow_mul_le (j := j + 4)]

/-- The support of a correlation. Let k be a pairing kernel for the element d (`IsPairingKernel`),
let t lie in `floorGroup b`, let t⁻¹ q lie in `unipotentBelow b`, and let the matrix q x have
entries of size j. For almost every σ on floor b at which the correlation from floor b + 1 on at (σ
x, σ y) is not zero, the vector t σ⁻¹ f_b has size j + 6. -/
lemma correlation_support (ht : t ∈ floorGroup b)
    (h_size : Γ.HasMatrixSize j ((q * x : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hk : F.IsPairingKernel b k d) (y : T.G) (hq : t⁻¹ * q ∈ unipotentBelow b := by simp) :
    ∀ᵐ σ : T.G ∂F.floorMeasure b, F.partialCorrelation (b + 1) k (σ * x) (σ * y) ≠ 0 →
      (t : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ orbitPoint b σ ∈ Γ.vecsOfSize (j + 6) := by
  filter_upwards [ae_floorMeasure_mem] with σ hσ h_ne
  have h_conj : σ * (t⁻¹ * q) * σ⁻¹ ∈ partialUnitriangularGroup (b + 1) :=
    unipotentBelow_le_partialUnitriangularGroup (conj_mem_unipotentBelow hσ hq)
  have h_near : F.IsNear (b + 1) (σ * t⁻¹ * (q * x)) := by
    simpa [mul_assoc] using (isNear_mul_iff h_conj).2 (hk.isNear_of_partialCorrelation_ne_zero h_ne)
  have h_orbit : (t : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ orbitPoint b σ =
      orbitPoint b (σ * t⁻¹) := by
    rw [orbitPoint, orbitPoint, mulVec_mulVec]
    simp
  rw [h_orbit]
  exact orbitPoint_mem_vecsOfSize (mul_mem hσ (inv_mem ht)) h_size h_near

/-- Plancherel's inequality for the amplitude of floor b, that is, the Fourier transform of a
correlation along the quadric of that floor. Let k be a pairing kernel for the element d at floor b,
let t lie in `floorGroup b`, let t⁻¹ q lie in `unipotentBelow b`, and let the matrix q x have
entries of size j (`Γ.HasMatrixSize j`). Let ρ be the Haar measure `floorVolume b` on the vectors of
floor at least b, or the measure `F.floorQuadricMeasure b` of the quadric of floor b. Integrate the
correlation from floor b + 1 on at (σ x, σ y) against ψ(ξ ⟨v + v₀, t σ⁻¹ f_b⟩) over σ on floor b.
Here ψ is the additive character of the place, ⟨·,·⟩ is the form with Gram matrix `T.splitGram`, and
σ⁻¹ f_b = `orbitPoint b σ`, with f = (e_0, …, e_{ϱ-1}, z) the frame. The integral for ρ of the
squared modulus of this transform over the v of size i (`Γ.vecsOfSize i`) is at most Λ^(99 n (i+6))
Λ^(99 n (j+12)) (c / |ξ|)^(card `F.FreeIndex`) times the squared L² norm of the correlation on floor
b. -/
lemma correlation_plancherel (ht : t ∈ floorGroup b)
    (h_size : Γ.HasMatrixSize j ((q * x : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hk : F.IsPairingKernel b k d) (y : T.G) (hq : t⁻¹ * q ∈ unipotentBelow b) (ξ : Aˣ)
    (v₀ : 𝔰.BesselIndex → A) {ρ : Measure (𝔰.BesselIndex → A)} {i : ℕ}
    (hρ : ρ = FloorGroups.floorVolume b ∨ ρ = F.floorQuadricMeasure b) :
    ∫⁻ v : 𝔰.BesselIndex → A in Γ.vecsOfSize i,
        ‖∫ σ : T.G, ψ (ξ * star (v + v₀) ⬝ᵥ T.splitGram *ᵥ t *ᵥ orbitPoint b σ) *
          F.partialCorrelation (b + 1) k (σ * x) (σ * y) ∂F.floorMeasure b‖ₑ ^ 2 ∂ρ ≤
      Γ.loss ^ (99 * 𝔰.n * (i + 6)) * Γ.loss ^ (99 * 𝔰.n * (j + 12)) *
        (P.kernelBound / P.modulus ξ) ^ Fintype.card F.FreeIndex *
        ∫⁻ σ : T.G, ‖F.partialCorrelation (b + 1) k (σ * x) (σ * y)‖ₑ ^ 2 ∂F.floorMeasure b := by
  -- On `G^(b)` the correlation is a measurable function `f₀` of `σ⁻¹ f_b`, so a function `f` of
  -- `t σ⁻¹ f_b` that vanishes off size `j + 6`. The shift by `v₀` multiplies `f` by a phase.
  let κ (σ : T.G) : ℂ := F.partialCorrelation (b + 1) k (σ * x) (σ * y)
  have hκ_inv : (partialUnitriangularGroup (b + 1) ⊓ floorGroup b).FixesLeft κ := by
    simp +contextual [κ, hk.partialCorrelation_mul_left, mul_assoc]
  obtain ⟨f₀, hf₀_meas, hf₀⟩ : ∃ f₀ : (𝔰.BesselIndex → A) → ℂ, Measurable f₀ ∧
      ∀ σ ∈ floorGroup b, F.partialCorrelation (b + 1) k (σ * x) (σ * y) = f₀ (orbitPoint b σ) :=
    exists_factor_orbitPoint b (Φ := κ) (by fun_prop) hκ_inv
  let f : (𝔰.BesselIndex → A) → ℂ := (Γ.vecsOfSize (j + 6)).indicator fun w ↦ f₀ (t⁻¹ *ᵥ w)
  let φ (w : 𝔰.BesselIndex → A) : ℂ := ψ (ξ * star v₀ ⬝ᵥ T.splitGram *ᵥ w) * f w
  have hf_meas : Measurable f := .indicator (by fun_prop) measurableSet_vecsOfSize
  have hφ_meas : Measurable φ := by
    unfold φ
    fun_prop
  have h_law : MeasurePreserving (fun σ ↦ t *ᵥ orbitPoint b σ) (F.floorMeasure b)
      (F.floorQuadricMeasure b) :=
    measurePreserving_mulVec_orbitPoint b ht
  have h_eq : ∀ᵐ σ ∂F.floorMeasure b,
      F.partialCorrelation (b + 1) k (σ * x) (σ * y) = f (t *ᵥ orbitPoint b σ) := by
    filter_upwards [Γ.correlation_support ht h_size hk y hq, ae_floorMeasure_mem] with σ h_supp hσ
    revert h_supp
    simp +contextual [f, indicator, not_imp_comm, hf₀ σ hσ]
  have hκ_int : Integrable κ (F.floorMeasure b) := hk.integrable_partialCorrelation_succ
  have hf_int : Integrable f (F.floorQuadricMeasure b) :=
    (h_law.integrable_comp hf_meas.aestronglyMeasurable).1 (hκ_int.congr h_eq)
  have hφ_int : Integrable φ (F.floorQuadricMeasure b) :=
    hf_int.bdd_mul (c := 1) (by fun_prop) (by simp)
  have hφ_supp (w : 𝔰.BesselIndex → A) (hw : φ w ≠ 0) : w ∈ Γ.vecsOfSize (j + 6) :=
    mem_of_indicator_ne_zero (right_ne_zero_of_mul hw)
  have h_fourier (v : 𝔰.BesselIndex → A) :
      ∫ σ, ψ (ξ * star (v + v₀) ⬝ᵥ T.splitGram *ᵥ t *ᵥ orbitPoint b σ) *
          F.partialCorrelation (b + 1) k (σ * x) (σ * y) ∂F.floorMeasure b =
        ∫ w, ψ (ξ * star v ⬝ᵥ T.splitGram *ᵥ w) * φ w ∂F.floorQuadricMeasure b := by
    rw [← h_law.map_eq, integral_map h_law.aemeasurable (by fun_prop)]
    exact integral_congr_ae (h_eq.mono fun σ hσ ↦ by
      simp [φ, hσ, mul_add, mul_assoc, AddChar.map_add_eq_mul])
  have h_norm : ∫⁻ σ, ‖F.partialCorrelation (b + 1) k (σ * x) (σ * y)‖ₑ ^ 2 ∂F.floorMeasure b =
      ∫⁻ w, ‖φ w‖ₑ ^ 2 ∂F.floorQuadricMeasure b := by
    rw [← h_law.lintegral_comp (by fun_prop)]
    exact lintegral_congr_ae (h_eq.mono fun σ hσ ↦ by simp [φ, hσ, ← ofReal_norm])
  simp only [h_fourier, h_norm]
  exact Γ.fourierSqNormLe_floorQuadricMeasure ξ hρ φ hφ_meas hφ_int hφ_supp

/-! ### Correlations along a Heisenberg group -/

/-- Let k be a pairing kernel (`IsPairingKernel`) from floor a + 1 on for the element d, and let
n = `P.heisenbergElem a t` with t = (ω, β). Suppose that (σ₀(d s d⁻¹) - σ₀(s^ε)) / M = ξ σ₀(s) for s
in the Heisenberg group `floorUnipotent a`, where σ₀ = `simpleRootSum` and M = `F.levelUnit` is the
level. Then the correlation `F.partialCorrelation` from floor a + 1 on at (n^ε x, n y) is the
integral over σ on floor a + 1 of ψ(-ξ ⟨ω, σ⁻¹ f_(a+1)⟩), with f the frame, times the correlation
from floor a + 2 on at (σ x, σ y). -/
lemma partialCorrelation_heisenbergElem_eq_integral {ξ : A} {ε : ℕ}
    (hk : F.IsPairingKernel (a + 1) k d)
    (h_twist : ∀ s ∈ floorUnipotent a,
      F.levelUnit⁻¹.val * (simpleRootSum (d * s * d⁻¹) - simpleRootSum (s ^ ε)) = ξ * simpleRootSum
        s)
    (t : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A) (x y : T.G) :
    F.partialCorrelation (a + 1) k (P.heisenbergElem a t ^ ε * x) (P.heisenbergElem a t * y) =
      ∫ σ : T.G,
        ψ (-ξ * star (inclMatrix A Subtype.val *ᵥ t.1) ⬝ᵥ T.splitGram *ᵥ orbitPoint a.succ σ) *
          F.partialCorrelation (a + 1 + 1) k (σ * x) (σ * y) ∂F.floorMeasure (a + 1) := by
  rw [hk.partialCorrelation_eq_integral_floorMeasure]
  refine integral_congr_ae (ae_floorMeasure_mem.mono fun σ hσ ↦ ?_)
  -- move `n` to the left of `σ` and apply the equivariance of the correlation to `s = σ n σ⁻¹`
  set s : T.G := σ * P.heisenbergElem a t * σ⁻¹ with hs_eq
  have hs : s ∈ floorUnipotent a :=
    conj_mem_floorUnipotent (heisenbergElem_mem_floorUnipotent a t) σ hσ
  have hs_unip : s ∈ unipotentBelow (a + 1) := (Subgroup.mem_inf.1 hs).right
  have h_law : F.partialCorrelation (a + 1 + 1) k (s ^ ε * (σ * x)) (s * (σ * y)) =
      ψ (F.levelUnit⁻¹.val * (simpleRootSum (d * s * d⁻¹) - simpleRootSum (s ^ ε))) *
        F.partialCorrelation (a + 1 + 1) k (σ * x) (σ * y) :=
    hk.equivariance (pow_mem hs_unip ε) hs_unip (σ * x) (σ * y)
  rw [h_twist s hs, hs_eq, simpleRootSum_conj_heisenbergElem hσ, mul_neg, ← neg_mul,
    conj_pow] at h_law
  simpa only [mul_assoc, inv_mul_cancel_left] using h_law

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermitianUnit T.splitGram] in
/-- Let p, q be sequences of units and j ≤ a + 1. Conjugation by the diagonal element
`weylRatio j p q`, with entry p_b / q_b at e_b for b < j, multiplies the character
`simpleRootSum` (the sum of the entries just above the diagonal of the
frame block) on the Heisenberg group `floorUnipotent a` by p_a / q_a if a < j, and by 1
otherwise. -/
lemma simpleRootSum_weylRatio_conj {q : ℕ → Aˣ} {s : T.G} (hs : s ∈ floorUnipotent a)
    (hj : j ≤ a + 1) :
    simpleRootSum (weylRatio j p q * s * (weylRatio j p q)⁻¹) =
      (if a < j then (p a / q a).val else 1) * simpleRootSum s := by
  simp_rw [simpleRootSum, mul_sum]
  congr with b
  -- conjugation by a diagonal matrix scales each entry
  simp only [Subgroup.coe_mul, Units.val_mul, weylRatio_inv, coe_weylRatio,
    diagonal_mul, mul_diagonal]
  obtain rfl | hab := eq_or_ne a b
  · -- the factor is `p a / q a` in row `a` if `a < j`, and `1` in column `a + 1` as `j ≤ a + 1`
    grind
  · -- just above the diagonal only the entry of floor `a` survives
    simp only [floorUnipotent_superdiag_eq_zero b hs (Fin.val_ne_of_ne hab), mul_zero, zero_mul]

/-- Let j ≤ a + 1 and ε ≤ 1, let k satisfy `F.IsPairingKernel (a + 1) k (weylRatio j p q)`, and let
n = `P.heisenbergElem a t` with t = (ω, β). Then `F.partialCorrelation (a + 1) k` at (n^ε x, n y) is
the integral over σ, for `F.floorMeasure (a + 1)`, of ψ(-ξ h(ω, σ⁻¹ f_(a+1))) times
`F.partialCorrelation (a + 2) k` at (σ x, σ y). Here ψ is the additive character of the place `P`, h
is the form with Gram matrix `T.splitGram`, and f = (e_0, …, e_{ϱ-1}, z) is the frame. The frequency
ξ is (p_a / q_a - ε) / M if a < j (that is, j = a + 1), and (1 - ε) / M otherwise. -/
lemma partialCorrelation_weylRatio_heisenbergElem {q : ℕ → Aˣ} {ε : ℕ} (hε : ε ≤ 1) (hj : j ≤ a + 1)
    (hk : F.IsPairingKernel (a + 1) k (weylRatio j p q))
    (t : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A) (x y : T.G) :
    F.partialCorrelation (a + 1) k (P.heisenbergElem a t ^ ε * x) (P.heisenbergElem a t * y) =
      ∫ σ : T.G,
        ψ (-(F.levelUnit⁻¹.val * ((if a < j then (p a / q a).val else 1) - ε)) *
            star (inclMatrix A Subtype.val *ᵥ t.1) ⬝ᵥ T.splitGram *ᵥ orbitPoint a.succ σ) *
          F.partialCorrelation (a + 1 + 1) k (σ * x) (σ * y) ∂F.floorMeasure (a + 1) := by
  refine partialCorrelation_heisenbergElem_eq_integral a hk (fun s hs ↦ ?_) t x y
  have h_pow : simpleRootSum (s ^ ε) = ε * simpleRootSum s := by
    obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.1 hε
    · simp [simpleRootSum_eq_zero_of_mem_besselH]
    · simp
  rw [simpleRootSum_weylRatio_conj a hs hj, h_pow]
  ring

/-- Parseval's inequality along the Heisenberg group N = `floorUnipotent a` of floor a. Let k be a
pairing kernel from floor a + 1 on for the element d, and let the characters of the two points
differ by the invertible frequency ξ on N. For n ∈ N with Φ(n) ≠ 0, let n lie in S and let Φ(n) be
at most C times the squared correlation `F.partialCorrelation` from floor a + 1 on at (n^ε x, n y).
For each n₀ ∈ S let there be t in `partialUnitriangularGroup (a + 1) ⊓ floorGroup a` and q in
`unipotentBelow (a + 1)` such that t q x has entries of size i and, for each n ∈ S, v / u has size
j for some v congruent to (t n₀ (t n)⁻¹ - 1) e*_a modulo the e_b with b < a (`CongrBelow`). Then
the integral of Φ over N is at most C (c / |ξ u|)^(rank X') |u|^(ρ+1/2) Λ^(100 n (i+j+31)) times
the integral over σ on floor a + 1 of the squared correlation from floor a + 2 on at (σ x, σ y).
Here c = `P.kernelBound`, rank X' = `card F.FreeIndex`, |u|^(ρ+1/2) = `F.floorModulus a u` with ρ
the rank of the vector part of N, Λ = `Γ.loss` is the constant of the gauge, and the n in its
exponent is `𝔰.n`. -/
lemma parseval_heisenbergMeasure_le {S : Set T.G} {i : ℕ} {Φ : T.G → ℝ≥0∞} (ξ u : Aˣ) (ε : ℕ)
    (C : ℝ≥0∞) (hk : F.IsPairingKernel (a + 1) k d) (x y : T.G)
    (h_twist : ∀ s ∈ floorUnipotent a,
      F.levelUnit⁻¹.val * (simpleRootSum (d * s * d⁻¹) - simpleRootSum (s ^ ε)) = ξ * simpleRootSum
        s)
    (hΦ : ∀ n ∈ floorUnipotent a, Φ n ≠ 0 →
      n ∈ S ∧ Φ n ≤ C * ‖F.partialCorrelation (a + 1) k (n ^ ε * x) (n * y)‖ₑ ^ 2)
    (h_centre : ∀ n₀ ∈ S, ∃ t ∈ partialUnitriangularGroup (a + 1) ⊓ floorGroup a,
      ∃ q ∈ unipotentBelow (a + 1),
      Γ.HasMatrixSize i (t * q * x).val.val ∧
      ∀ n ∈ S, ∃ v : 𝔰.BesselIndex → A,
        CongrBelow a (((t * n₀ * (t * n)⁻¹).val.val - 1) *ᵥ Pi.single (eStar a) 1) v ∧
        u⁻¹.val • v ∈ Γ.vecsOfSize j) :
    ∫⁻ n : T.G, Φ n ∂heisenbergMeasure a ≤
      C * ((P.kernelBound / P.modulus (ξ * u)) ^ Fintype.card F.FreeIndex * F.floorModulus a u *
        Γ.loss ^ (100 * 𝔰.n * (i + j + 31)) *
        ∫⁻ σ : T.G, ‖F.partialCorrelation (a + 1 + 1) k (σ * x) (σ * y)‖ₑ ^ 2
          ∂F.floorMeasure (a + 1)) := by
  -- Fix `n₀` in the support of `Φ`, write the element that `h_centre` gives as `t * r`, and
  -- substitute `n = r⁻¹ t⁻¹ n(v) t r n₀`. The correlation at `n` is a Fourier transform read at a
  -- translate of `v.1 / u`, and `h_close` bounds the size of a lift of `(n(v)⁻¹ - 1) e*_a / u`.
  obtain h_zero | h_int := eq_or_ne (∫⁻ n, Φ n ∂heisenbergMeasure a) 0
  · exact h_zero.trans_le zero_le
  obtain ⟨n₀, hn₀, hn₀_ne⟩ : ∃ n₀ ∈ floorUnipotent a, Φ n₀ ≠ 0 :=
    exists_ne_zero_of_ae ae_mem_floorUnipotent h_int
  obtain ⟨hn₀_mem, -⟩ := hΦ n₀ hn₀ hn₀_ne
  obtain ⟨t₀, ht₀, q, hq, h_size, h_close⟩ := h_centre n₀ hn₀_mem
  obtain ⟨t, ht, r, hr, rfl⟩ : ∃ t ∈ floorGroup (a + 1), ∃ r ∈ floorUnipotent a, t₀ = t * r :=
    exists_floorGroup_mul_floorUnipotent ht₀
  obtain ⟨w, rfl⟩ := exists_eq_heisenbergElem_of_mem hr
  obtain ⟨z, rfl⟩ := exists_eq_heisenbergElem_of_mem hn₀
  let N (v : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A) : T.G :=
    (P.heisenbergElem a w)⁻¹ * (t⁻¹ * P.heisenbergElem a v * t) *
      (P.heisenbergElem a w * P.heisenbergElem a z)
  have hN (v : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A) :
      N v ∈ floorUnipotent a := by
    simp only [N, mul_heisenbergElem (inv_mem ht), inv_mul_cancel_right]
    exact mul_mem (mul_mem (inv_mem hr) (heisenbergElem_mem_floorUnipotent a _)) (mul_mem hr hn₀)
  -- the vector part of `N v` is `t⁻¹ v.1 + z.1`
  have h_fourier (v : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A) :
      F.partialCorrelation (a + 1) k (N v ^ ε * x) (N v * y) =
        ∫ σ, ψ ((-ξ * star u).val * star (u⁻¹.val • inclMatrix A Subtype.val *ᵥ v.1 +
            u⁻¹.val • t.val.val *ᵥ inclMatrix A Subtype.val *ᵥ z.1) ⬝ᵥ
              T.splitGram *ᵥ t *ᵥ orbitPoint a.succ σ) *
          F.partialCorrelation (a + 1 + 1) k (σ * x) (σ * y) ∂F.floorMeasure (a + 1) := by
    simp only [N, mul_heisenbergElem (inv_mem ht), inv_mul_cancel_right, heisenbergElem_inv,
      heisenbergElem_mul, partialCorrelation_heisenbergElem_eq_integral a hk h_twist]
    congr 3 with σ
    simp only [← add_assoc, ← form_mulVec_mulVec t _ (orbitPoint _ _), mulVec_add,
      inclMatrix_mulVec_floor_block a.isLt, inv_mem, ht]
    simp [← inverse_star_unit, star_mulVec_dotProduct, mul_add, mul_assoc]
  -- the measure is invariant under the group on both sides and under conjugation by `t`
  have h_subst : ∫⁻ n, Φ n ∂heisenbergMeasure a =
      ∫⁻ n, Φ ((P.heisenbergElem a w)⁻¹ * (t⁻¹ * n * t) *
        (P.heisenbergElem a w * P.heisenbergElem a z)) ∂heisenbergMeasure a := by
    obtain ⟨-, h_left⟩ := heisenbergMeasure_mconv_dirac hr
    obtain ⟨h_right, -⟩ := heisenbergMeasure_mconv_dirac (mul_mem hr hn₀)
    rw [lintegral_eq_of_dirac_mconv_eq (h_left.trans h_right.symm),
      lintegral_eq_of_dirac_mconv_eq (dirac_mconv_heisenbergMeasure_comm ht)]
  have h_unip : t⁻¹ * (t * P.heisenbergElem a w * q) ∈ unipotentBelow (a + 1) := by
    simpa [mul_assoc] using mul_mem (Subgroup.mem_inf.1 hr).right hq
  rw [h_subst]
  -- Plancherel's bound on floor `a + 1`, at the frequency `-ξ * star u`
  refine lintegral_heisenbergMeasure_le (j := j) u
    (Γ.correlation_plancherel (b := a.succ) ht h_size hk y h_unip (-ξ * star u)
      (u⁻¹.val • t.val.val *ᵥ inclMatrix A Subtype.val *ᵥ z.1) (.inl rfl))
    fun v h_ne ↦ ?_
  obtain ⟨h_mem, h_le⟩ :
      N v ∈ S ∧ Φ (N v) ≤ C * ‖F.partialCorrelation (a + 1) k (N v ^ ε * x) (N v * y)‖ₑ ^ 2 :=
    hΦ (N v) (hN v) h_ne
  have h_inv : t * P.heisenbergElem a w * P.heisenbergElem a z *
      (t * P.heisenbergElem a w * N v)⁻¹ = (P.heisenbergElem a v)⁻¹ := by
    simp only [N]
    group
  rw [h_fourier v] at h_le
  refine ⟨?_, h_le⟩
  rw [← h_inv]
  exact h_close (N v) h_mem

end New.Floors.Gauge
