module

import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import TauCeti.NumberTheory.NumberField.Countable
public import New.Spanning.Unfolding.Terms
import Lib.Adelic.Adeles.StrongApproximation
import Lib.General.NumberTheory.LatticeCovolumes
import New.Spanning.RemainingTerms.FrameCount
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Monotonicity.Lemmas
import TauCeti.MeasureTheory.Integral.Pi
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import New.Spanning.RemainingTerms.SchurTest
public import New.Spanning.RemainingTerms.OrbitSize
import Lib.Cohomology.Etale.Basic
import Lib.General.Analysis.HolomorphicIntegrals
import New.Spanning.RemainingTerms.FrameParts
import New.Spanning.RemainingTerms.LinkLattice
public import New.Spanning.Unfolding.AmplitudeSums
import New.Spanning.Unfolding.ReducedPoints
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Shift.Basic
public import New.Spanning.Unfolding.TermStructure
public import New.Spanning.RemainingTerms.Data
import Lib.Adelic.Unitary.CongruenceLevels
import Lib.DiscreteSeries.Bruhat.ComplexPlace
import New.Spanning.Bessel.OpenCellPairing
import New.Spanning.Unfolding.Climbing

section
section
/-!
# The covolume of the lattice of columns

The tuples of vectors of the lattice `Λ ∩ X₀` of a class form a lattice in the product of the
complex places. The real inner product of two of its points is an integer, so its covolume is at
least `1`.

## Main definitions and results

* `New.Filling.columnLattice`, `New.Filling.exists_isAddFundamentalDomain_columnLattice`: the
  lattice of tuples of vectors of `Λ ∩ X₀` and its fundamental domain.

Notions from other files:

* `S : Filling E 𝔰`: the data of the filling theorem over the CM field `E` for the shape `𝔰`; the
  space `X₀` has a basis indexed by `𝔰.κ`, a set of `𝔰.k` elements.
* `c : S.Classes`: a class of the definite unitary group of `X₀`, with lattice `Λ`.
* `S.classCoordX₀ c`: the matrix that writes vectors of `X₀` in a basis of `Λ`; thus a vector lies
  in `Λ ∩ X₀` if its image under this matrix is integral.
* `Φ v`: the chosen complex embedding of `E` at the infinite place `v`.
* `Ô E`, `finAdeleMatrix q`: the integral finite adeles, and the matrix `q` over the finite adeles.

## Relation to the literature

See `New.Spanning.RemainingTerms.Sum` for related work.
-/

@[expose] public section

open MeasureTheory Matrix Module Fintype NumberField

namespace New.Filling

section Columns

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {ι : Type}

variable (E 𝔰 ι) in
/-- The point of the product of the complex places given by a matrix over `E` whose columns are
`ι` vectors of `X₀`: at the place `v`, the entry `q a l` goes to the conjugate of `Φ v (q a l)`. -/
def conjColumnsAtInfinity : Matrix 𝔰.κ ι E →+ (InfinitePlace E → ι → 𝔰.κ → ℂ) where
  toFun q v l a := star (Φ v (q a l))
  map_zero' := by simp [funext_iff]
  map_add' q q' := by simp [funext_iff]

@[simp]
lemma conjColumnsAtInfinity_apply (q : Matrix 𝔰.κ ι E) (v : InfinitePlace E) (l : ι) (a : 𝔰.κ) :
    conjColumnsAtInfinity E 𝔰 ι q v l a = star (Φ v (q a l)) :=
  rfl

lemma conjColumnsAtInfinity_injective : Function.Injective (conjColumnsAtInfinity E 𝔰 ι) := by
  intro q q' h_eq
  ext a l
  exact (Φ (Classical.arbitrary (InfinitePlace E))).injective
    (star_injective (congrFun₂ (congrFun h_eq _) l a))

/-- Let `Φ v` be the chosen complex embedding of `E` at the infinite place `v`. The map
`conjColumnsAtInfinity`, which sends a matrix `q` over `E` to the family of the complex conjugates
of its images `Φ v (q a l)`, indexed by the place `v`, the column `l` and the row `a`, has dense
range. -/
lemma denseRange_conjColumnsAtInfinity : DenseRange (conjColumnsAtInfinity E 𝔰 ι) := by
  -- `E` is dense in the product of the complex places; take one copy for each entry.
  let conjSwap (x : 𝔰.κ → ι → InfinitePlace E → ℂ) : InfinitePlace E → ι → 𝔰.κ → ℂ :=
    fun v l a ↦ star (x a l v)
  have h_surjective : Function.Surjective conjSwap :=
    fun y ↦ ⟨fun a l v ↦ star (y v l a), by simp [conjSwap]⟩
  have h_dense : DenseRange (Pi.map fun _ : 𝔰.κ ↦ Pi.map fun _ : ι ↦ RingHom.pi (Φ (E := E))) :=
    .piMap fun _ ↦ .piMap fun _ ↦ denseRange_Φ
  change DenseRange (conjSwap ∘ Pi.map fun _ : 𝔰.κ ↦ Pi.map fun _ : ι ↦ RingHom.pi (Φ (E := E)))
  exact h_surjective.denseRange.comp h_dense (by fun_prop)

variable (ι) in
/-- The tuples of vectors of `Λ ∩ X₀`, for the lattice `Λ` of the class `c`, as the columns of a
matrix. -/
def integralColumns (S : Filling E 𝔰) (c : S.Classes) : AddSubgroup (Matrix 𝔰.κ ι E) where
  carrier := {q : Matrix 𝔰.κ ι E | IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix q)}
  zero_mem' := by simp [IsIntMatrix]
  add_mem' hq hq' := by simpa [Matrix.map_add, Matrix.mul_add] using hq.add hq'
  neg_mem' hq := by simpa [Matrix.map_neg] using hq.neg

variable (ι) in
/-- The image of the tuples of vectors of `Λ ∩ X₀` in the product of the complex places. -/
def columnLattice (S : Filling E 𝔰) (c : S.Classes) :
    AddSubgroup (InfinitePlace E → ι → 𝔰.κ → ℂ) :=
  (S.integralColumns ι c).map (conjColumnsAtInfinity E 𝔰 ι)

/-- A point is in the lattice of columns if and only if it is the image under
`conjColumnsAtInfinity` of a matrix over `E` whose columns lie in the lattice of the class `c`. -/
lemma mem_columnLattice {S : Filling E 𝔰} {c : S.Classes} {x : InfinitePlace E → ι → 𝔰.κ → ℂ} :
    x ∈ S.columnLattice ι c ↔ ∃ q : Matrix 𝔰.κ ι E,
      IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix q) ∧ conjColumnsAtInfinity E 𝔰 ι q = x :=
  .rfl

variable [Fintype ι]

instance {S : Filling E 𝔰} {c : S.Classes} : Countable (S.columnLattice ι c) := by
  exact ((Set.to_countable _).image _).to_subtype

omit [Fintype ι] in
/-- If `q` and `q'` are matrices whose columns lie in `Λ ∩ X₀`, for the lattice `Λ` of the class
`c`, then the hermitian products of their columns, the entries of `qᴴ * q'`, are algebraic
integers. -/
lemma isIntegral_conjTranspose_mul {S : Filling E 𝔰} {c : S.Classes}
    {q q' : Matrix 𝔰.κ ι E} (hq : IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix q))
    (hq' : IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix q')) (l l' : ι) :
    IsIntegral ℤ ((qᴴ * q') l l') := by
  have h_gram : (S.classCoordX₀ c * finAdeleMatrix q)ᴴ * S.latticeMiddle (𝔸f E) *
      (S.classCoordX₀ c * finAdeleMatrix q') = finAdeleMatrix (qᴴ * q') := calc
    _ = (finAdeleMatrix q)ᴴ * ((S.classCoordX₀ c)ᴴ * S.latticeMiddle (𝔸f E) * S.classCoordX₀ c) *
        finAdeleMatrix q' := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = finAdeleMatrix (qᴴ * q') := by
      rw [gram_classCoordX₀, Matrix.mul_one, ← finAdeleMatrix_conjTranspose, ← Matrix.map_mul]
  have h_int : ((S.classCoordX₀ c * finAdeleMatrix q)ᴴ * S.latticeMiddle (𝔸f E) *
      (S.classCoordX₀ c * finAdeleMatrix q')) l l' ∈ Ô E :=
    (hq.conjTranspose.mul S.isUnimodular_latticeMiddle.isIntMatrix).mul hq' l l'
  rw [h_gram] at h_int
  exact algebraMap_mem_Ô.1 h_int

/-- A nonzero vector of `Λ ∩ X₀`, for the lattice `Λ` of the class `c`, has length at least `1` at
some place, so the lattice of columns is discrete. -/
instance {S : Filling E 𝔰} {c : S.Classes} :
    DiscreteTopology (S.columnLattice ι c) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  -- The tuples all of whose vectors are short at every place form a neighbourhood of zero.
  let U : Set (InfinitePlace E → ι → 𝔰.κ → ℂ) :=
    ⋂ (v : InfinitePlace E) (l : ι), {x | ∑ a : 𝔰.κ, ‖x v l a‖ ^ 2 < 1}
  have hU : IsOpen U := isOpen_iInter_of_finite fun v ↦ isOpen_iInter_of_finite fun l ↦
    isOpen_lt (by fun_prop) continuous_const
  suffices h_zero : ({0} : Set (S.columnLattice ι c)) = Subtype.val ⁻¹' U by
    rw [h_zero]
    exact hU.preimage continuous_subtypeVal
  ext ⟨x, hx⟩
  obtain ⟨q, hq, rfl⟩ := mem_columnLattice.1 hx
  refine ⟨fun h_eq ↦ ?_, fun h_short ↦ Subtype.ext ?_⟩
  · have h_point : conjColumnsAtInfinity E 𝔰 ι q = 0 := congrArg Subtype.val h_eq
    change conjColumnsAtInfinity E 𝔰 ι q ∈ U
    rw [h_point]
    simp [U]
  · have h_col (l : ι) : q.col l = 0 := col_eq_zero_of_norm_lt_one hq fun v ↦ by
      simpa using Set.mem_iInter₂.1 h_short v l
    have hq_zero : q = 0 := ext fun a l ↦ congrFun (h_col l) a
    simp [hq_zero]

end Columns

/-- Let `S` be filling data of shape `𝔰` over the CM field `E`, let `c` be a class of the definite
unitary group of `X₀ = E ^ 𝔰.κ`, with lattice `Λ`, and let `ι` be a finite set. The subgroup
`S.columnLattice ι c` is the image of the `ι`-tuples of vectors of `Λ ∩ X₀`, under the conjugates
of the chosen complex embeddings of `E`, in the product over the infinite places of `E` of the
spaces of `ι`-tuples of vectors of `ℂ ^ 𝔰.κ`. It spans this product over `ℝ`. -/
lemma span_columnLattice {E : Type} [Field E] [CMType E] {𝔰 : Shape} {ι : Type} [Fintype ι]
    {S : Filling E 𝔰} {c : S.Classes} :
    Submodule.span ℝ (S.columnLattice ι c : Set (InfinitePlace E → ι → 𝔰.κ → ℂ)) = ⊤ := by
  -- Every tuple of vectors of `X₀` has a nonzero integer multiple in `Λ ∩ X₀`, so the span
  -- contains the image of all such tuples, which is dense.
  have h_range : Set.range (conjColumnsAtInfinity E 𝔰 ι) ⊆
      Submodule.span ℝ (S.columnLattice ι c : Set (InfinitePlace E → ι → 𝔰.κ → ℂ)) := by
    rintro _ ⟨q, rfl⟩
    -- A common denominator of the finitely many coordinates makes them all integral.
    obtain ⟨N, hN, h_mem⟩ : ∃ N : ℕ, N ≠ 0 ∧
        ∀ x ∈ Set.range (S.classCoordX₀ c * finAdeleMatrix q).uncurry, (N : 𝔸f E) • x ∈ Ô E :=
      exists_natCast_smul_mem_of_isCompact E (Set.finite_range _).isCompact
        (isOpen_Ô.mem_nhds (zero_mem _))
    have h_int : IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix (N • q)) := fun a l ↦ by
      simpa [Function.uncurry, Matrix.mul_apply, Finset.mul_sum, mul_left_comm] using
        h_mem _ ⟨(a, l), rfl⟩
    have h_point : conjColumnsAtInfinity E 𝔰 ι (N • q) ∈ S.columnLattice ι c :=
      mem_columnLattice.2 ⟨N • q, h_int, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hN : (N : ℝ) ≠ 0),
      Nat.cast_smul_eq_nsmul, ← map_nsmul]
    exact Submodule.subset_span h_point
  -- The span is closed and contains a dense set.
  have h_dense :
      Dense (Submodule.span ℝ (S.columnLattice ι c : Set (InfinitePlace E → ι → 𝔰.κ → ℂ)) :
        Set (InfinitePlace E → ι → 𝔰.κ → ℂ)) :=
    denseRange_conjColumnsAtInfinity.mono h_range
  rw [← Submodule.dense_iff_topologicalClosure_eq_top.1 h_dense,
    (Submodule.isClosed_of_finiteDimensional _).submodule_topologicalClosure_eq]

/-- Let the CM field `E` contain a primitive root of unity of order `5040`, hence a square root of
`-1`. For an algebraic integer `x` of `E`, the sum over the infinite places `v` of the real parts of
the images `Φ v x` under the chosen embeddings, which is half the trace of `x`, is an integer. -/
lemma exists_int_eq_sum_re {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {x : E}
    (hx : IsIntegral ℤ x) :
    ∃ n : ℤ, ∑ v : InfinitePlace E, (Φ v x).re = n := by
  -- Let `i² = -1` in `E`, and let `t v` be the image of `x` under the embedding at `v` that sends
  -- `i` to `I`. The sum of the `t v` is an algebraic integer equal to `(p - q I) / 2`, for the
  -- traces `p` of `x` and `q` of `i x`. So its squared absolute value `(p² + q²) / 4` is an
  -- integer, and `p` is even.
  obtain ⟨i, hi, -⟩ : ∃ i : 𝓞 E, i * i = -1 ∧ star i = -i :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one
  have h_trace {y : E} (hy : IsIntegral ℤ y) :
      ∃ n : ℤ, ∑ v : InfinitePlace E, 2 * (Φ v y).re = n := by
    obtain ⟨n, hn⟩ : ∃ n : ℤ, algebraMap ℤ ℚ n = Algebra.trace ℚ E y :=
      IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace hy)
    exact ⟨n, by rw [← trace_eq_sum_Φ, ← hn, eq_intCast, Rat.cast_intCast]⟩
  obtain ⟨p, hp⟩ : ∃ p : ℤ, ∑ v : InfinitePlace E, 2 * (Φ v x).re = p := h_trace hx
  obtain ⟨q, hq⟩ : ∃ q : ℤ, ∑ v : InfinitePlace E, 2 * (Φ v (i * x)).re = q :=
    h_trace (i.property.mul hx)
  let t (v : InfinitePlace E) : ℂ := if Φ v i = Complex.I then Φ v x else star (Φ v x)
  have h_term (v : InfinitePlace E) : t v = (Φ v x).re - (Φ v (i * x)).re * Complex.I := by
    have h_sq : Φ v i ^ 2 = Complex.I ^ 2 := by
      simpa [sq] using congrArg (fun y : 𝓞 E ↦ Φ v y) hi
    obtain h_eq_I | h_eq_neg_I : Φ v i = Complex.I ∨ Φ v i = -Complex.I :=
      sq_eq_sq_iff_eq_or_eq_neg.1 h_sq
    · simp [t, h_eq_I, Complex.ext_iff]
    · simp [t, h_eq_neg_I, Complex.ext_iff, neg_eq_self]
  have h_int : IsIntegral ℤ (∑ v : InfinitePlace E, t v) := .sum _ fun v _ ↦ by
    unfold t
    split_ifs
    exacts [map_isIntegral_int _ hx, map_isIntegral_int (starRingEnd ℂ) (map_isIntegral_int _ hx)]
  have h_sum : ∑ v : InfinitePlace E, t v = ((p : ℝ) - (q : ℝ) * Complex.I) / 2 := by
    simp only [h_term, ← hp, ← hq, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    push_cast
    ring
  have h_norm : IsIntegral ℤ (algebraMap ℚ ℂ ((p ^ 2 + q ^ 2) / 4)) := by
    have h_eq : algebraMap ℚ ℂ ((p ^ 2 + q ^ 2) / 4) =
        (∑ v : InfinitePlace E, t v) * starRingEnd ℂ (∑ v : InfinitePlace E, t v) := by
      rw [h_sum, Complex.mul_conj, Complex.normSq_div]
      simp [Complex.normSq_apply, sq]
      norm_num
    rw [h_eq]
    exact h_int.mul (map_isIntegral_int (starRingEnd ℂ) h_int)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, algebraMap ℤ ℚ m = (p ^ 2 + q ^ 2) / 4 :=
    IsIntegrallyClosed.isIntegral_iff.1 h_norm.tower_bot_of_field
  have h_four : 4 * m = p ^ 2 + q ^ 2 := by
    rw [eq_intCast, eq_div_iff four_ne_zero, mul_comm] at hm
    exact_mod_cast hm
  obtain ⟨n, rfl⟩ : Even p := by
    obtain ⟨a, rfl | rfl⟩ := Int.even_or_odd' p
    · exact even_two_mul a
    · obtain ⟨b, rfl | rfl⟩ := Int.even_or_odd' q <;> lia
  rw [← Finset.mul_sum] at hp
  push_cast at hp
  exact ⟨n, by linarith⟩

/-- Let `E` be a CM field containing a primitive root of unity of order `5040`, and let `S`
be filling data over `E`. The subgroup `S.columnLattice ι c` is the image of the `ι`-tuples of
vectors of `Λ ∩ X₀` under the conjugates of the chosen complex embeddings, one for each infinite
place. It has a measurable fundamental domain whose Lebesgue measure is finite and at least `1`. -/
theorem exists_isAddFundamentalDomain_columnLattice {E : Type} [Field E] [CMType E] {𝔰 : Shape}
    (ι : Type) [Fintype ι] (S : Filling E 𝔰) (c : S.Classes)
    [HasPrimitiveRoot5040 E] :
    ∃ D : Set (InfinitePlace E → ι → 𝔰.κ → ℂ),
      MeasurableSet D ∧
      IsAddFundamentalDomain (S.columnLattice ι c) D volume ∧
      1 ≤ volume D ∧
      volume D ≠ ⊤ := by
  -- In the coordinates of the standard real basis `e`, the euclidean product of two lattice points
  -- is half the trace of an algebraic integer of `E`, hence an integer.
  let L : Submodule ℤ (InfinitePlace E → ι → 𝔰.κ → ℂ) := (S.columnLattice ι c).toIntSubmodule
  have : DiscreteTopology L := inferInstanceAs (DiscreteTopology (S.columnLattice ι c))
  have : IsZLattice ℝ L := ⟨span_columnLattice⟩
  let e : Basis (Σ _ : InfinitePlace E, Σ _ : ι, Σ _ : 𝔰.κ, Fin 2) ℝ
      (InfinitePlace E → ι → 𝔰.κ → ℂ) :=
    Pi.basis fun _ ↦ Pi.basis fun _ ↦ Pi.basis fun _ ↦ Complex.basisOneI
  have h_volume : volume (ZSpan.fundamentalDomain e) = 1 :=
    volume_fundamentalDomain_pi_basis _ fun _ ↦ volume_fundamentalDomain_pi_basis _ fun _ ↦
      volume_fundamentalDomain_pi_basis _ fun _ ↦ volume_fundamentalDomain_basisOneI
  refine exists_isAddFundamentalDomain_of_integral volume e h_volume L ?_
  intro x hx y hy
  obtain ⟨q, hq, rfl⟩ := mem_columnLattice.1 hx
  obtain ⟨q', hq', rfl⟩ := mem_columnLattice.1 hy
  have h_int : IsIntegral ℤ (∑ l : ι, (qᴴ * q') l l) :=
    .sum _ fun l _ ↦ isIntegral_conjTranspose_mul hq hq' l l
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ∑ v : InfinitePlace E, (Φ v (∑ l : ι, (qᴴ * q') l l)).re = n :=
    exists_int_eq_sum_re h_int
  refine ⟨n, .trans ?_ hn⟩
  simp [e, Fintype.sum_sigma, Matrix.mul_apply]

end New.Filling
end
end

/-!
# Schur's test for one orbit

A term is a rational point `γ` of the unitary group with
`S.translateByClassReps c c' γ = h_c⁻¹ γ h_c'` integral. Its orbit is the double coset of `γ` under
the groups `New.Filling.classUnipotent₀` of unipotent elements of level `M = S.M` that fix the
frame. The amplitude majorants of the terms of an orbit are summed by Schur's test: the mean of the
sum of the weights over the orbit is reduced to a sum over a lattice, and then to the integral of a
kernel divided by the covolume of the lattice.

Throughout, `Λ` is the lattice of the class `c`, `A` is the isotropic space spanned by `e₁, …, e_ϱ`,
and `X₀` is the positive definite part of dimension `k`. For a term of cell rank `j`
(`New.Filling.HasCellRank`) put `i = min ϱ j`. The unit frame at an infinite place is the frame
rescaled by `New.Filling.basisScale`.

Notions from other files:
* `S.frameProducts γ`: the matrix of products of the frame `e₁, …, e_ϱ, z` with its image by `γ`.
* `S.HasCellRank j γ`: in `γ` a norm-one pair occurs from `j`, its leading minor of order `j` is
  nonzero, and `S.termDisc γ` is nonzero exactly when `j = ϱ + 1`.
* `S.schurWeight c' γ i y`: the boxed cutoff of `c'` at `γ⁻¹ y` times the product over the places of
  the powers `-(k + i)` of the ratio of volumes `volumeRatio`.
* `S.tailScale`: the number `α = b ^ (k f / 4)`, where `f` is the number of infinite places.

## Main definitions and results

* `New.Filling.tsum_orbit_le_of_isLatticeTranslate`: the frames of an orbit lie in at most
  `isotropicRowsIndex ^ k` cosets of a lattice.
* `New.Filling.exists_tsum_schurWeight_le`: from cosets to the lattice.
* `New.Filling.tsum_schurIntegral_le`: from the lattice to an integral.
* `New.Filling.sq_tsum_amplitudeMajorant_doubleCoset_le`,
  `New.Filling.tsum_amplitudeMajorant_orbit_le`: the test, and its form as a bound by
  `New.Filling.orbitBound`.
-/

@[expose] public section

namespace New.Filling

open MeasureTheory Matrix Fintype RealPlace ENNReal Real Pointwise Fin
  DoubleCoset AddSubgroup Finset LinearMap
open NumberField (InfinitePlace)

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
  [S.IsAdmissible] {j : Fin (𝔰.ϱ + 2)} {c c' : S.Classes} {s : S.ResidueGL} {γ : S.G E}

omit [S.IsAdmissible] in
/-- The terms of an orbit have the same cell rank: if `δ` lies in the double coset of `γ` under the
unipotent groups `classUnipotent₀` of `c` and `c'`, and `γ` has cell rank `j`, then so has `δ`. -/
lemma HasCellRank.of_mem_doubleCoset {δ : S.G E}
    (hδ : δ ∈ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'))
    (h_rank : S.HasCellRank j γ) : S.HasCellRank j δ := by
  obtain ⟨u, ⟨-, hu_bessel, -⟩, x, ⟨-, hx_bessel, -⟩, rfl⟩ := mem_doubleCoset.1 hδ
  have h_stable : S.HasCellRank j (u⁻¹⁻¹ * γ * x) ↔ S.HasCellRank j γ :=
    isStable_hasCellRank j u⁻¹ (inv_mem hu_bessel) x hx_bessel γ
  rw [inv_inv] at h_stable
  exact h_stable.2 h_rank

omit [S.IsAdmissible] in
/-- If `δ` lies in the orbit of `γ`, the double coset under the groups `classUnipotent₀` of the
classes `c` and `c'`, then `δ` and `γ` have the same matrix of products of the frame with its
image. -/
lemma frameProducts_eq_of_mem_doubleCoset {δ : S.G E}
    (hδ : δ ∈ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c')) :
    S.frameProducts δ = S.frameProducts γ := by
  obtain ⟨u, ⟨-, hu_frame⟩, x, ⟨-, hx_frame⟩, rfl⟩ := mem_doubleCoset.1 hδ
  obtain ⟨hu_bessel, hu_matrix⟩ := mem_besselU0_iff.1 (inv_mem hu_frame)
  obtain ⟨hx_bessel, hx_matrix⟩ := mem_besselU0_iff.1 hx_frame
  have h_gram : S.frameProducts (u⁻¹⁻¹ * γ * x) =
      (frameMatrix u⁻¹)ᴴ * S.frameProducts γ * frameMatrix x :=
    frameGram_inv_mul_mul hu_bessel hx_bessel
  simpa [hu_matrix, hx_matrix] using h_gram

omit [S.IsAdmissible] in
/-- The terms of an orbit lie over the same block `(c, s, c')`: if `γ ∈ S.termsOver c s c'` (its
translate by the class representatives is integral with residue `s`), then so is every `δ` in the
double coset of `γ` under `classUnipotent₀ c` and `classUnipotent₀ c'`. -/
lemma termsOver.of_mem_doubleCoset {δ : S.G E}
    (hδ : δ ∈ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'))
    (h_over : γ ∈ S.termsOver c s c') : δ ∈ S.termsOver c s c' := by
  obtain ⟨u, ⟨⟨-, hu_over⟩, -⟩, x, ⟨⟨-, hx_over⟩, -⟩, rfl⟩ := mem_doubleCoset.1 hδ
  simpa using termsOver.mul (termsOver.mul hu_over h_over) hx_over

omit [S.IsAdmissible] in
/-- For `δ` in the orbit of `γ`, the conjugate of each row `i` of middle coordinates of the frame
moved by `translateByClassReps c c' δ` differs from that for `γ` by `M` times an `Ô`-combination of
the conjugates of the isotropic rows of the products (`frameGram`) of the frame with its image under
`translateByClassReps c c' γ`. -/
lemma col_frameMiddle_sub_mem {δ : S.G E}
    (hδ : δ ∈ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c')) (i : 𝔰.MiddleIndex) :
    (frameMiddle (S.translateByClassReps c c' δ) - frameMiddle (S.translateByClassReps c c' γ))ᴴ.col
      i ∈
      S.ideleM • colLattice (Ô E)
        (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram (S.translateByClassReps c c' γ)))ᴴ := by
  -- Write `δ = u γ x`. The new frame is `u'` times the old one, where
  -- `u' = translateByClassReps c c u` is `u` in the basis of the lattice, and `M⁻¹ (u' - 1)` is
  -- integral.
  obtain ⟨u, ⟨hu_over, hu_frame⟩, x, ⟨-, hx_frame⟩, rfl⟩ := mem_doubleCoset.1 hδ
  let u' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := (S.translateByClassReps c c u).val.val
  have h_frame : frameImage (S.translateByClassReps c c' (u * γ * x)).val.val =
      frameImage (S.translateByClassReps c c u * S.translateByClassReps c c' γ).val.val := by
    -- `↓`: these rules must act before the products are reassociated.
    simp [↓frameImage_translateByClassReps, coe_translateByClassReps, classCoord,
      ↓frameImage_mul_of_mem_besselU0 hx_frame, ↓frameImage_mul, Matrix.mul_assoc]
  have h_int : IsIntMatrix (Ô E) (S.ideleM⁻¹ • (u' - 1)) :=
    (S.principalLevel_eq_unitaryLevel.le hu_over.2).2
  have h_star : star S.ideleM = S.ideleM := Units.ext (by simp [ideleM])
  -- The coefficients are the conjugates of row `i` of `M⁻¹ (u' - 1)` in the last block of columns;
  -- off this block the row agrees with the identity, as `u'` is unipotent.
  let row : Fin 𝔰.ϱ → 𝔸f E := fun a ↦ star ((S.ideleM⁻¹ • (u' - 1)) (.inr (.inl i)) (eStar a))
  refine ⟨_, ⟨row, fun a ↦ star_mem_Ô (h_int (.inr (.inl i)) (eStar a)), rfl⟩, ?_⟩
  let g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := (S.translateByClassReps c c' γ).val.val
  have h_unipotent (b : 𝔰.BesselIndex) (hb : ∀ a : Fin 𝔰.ϱ, b ≠ eStar a) :
      u' (.inr (.inl i)) b = if .inr (.inl i) = b then 1 else 0 :=
    apply_inr_of_mem_besselU (hu_frame.1.translateByClassReps_mem_besselU c) (.inl i) b hb
  -- The products of `e_a` with the frame of `g` are the coordinates of that frame along `e*_a`.
  have h_diff (b : Fin (𝔰.ϱ + 1)) : (frameMiddle (u' * g) - frameMiddle g) i b =
      ∑ a : Fin 𝔰.ϱ, u' (.inr (.inl i)) (eStar a) *
        isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram g) a b := by
    simp [Matrix.mul_apply, frameGram, splitGram, h_unipotent, Matrix.one_apply]
  rw [frameMiddle, h_frame]
  funext b
  change _ = star ((frameMiddle (u' * g) - frameMiddle g) i b)
  rw [h_diff]
  simp [row, g, mulVec_eq_sum, h_star, ← Units.smul_def, mul_comm]

variable [HasPrimitiveRoot5040 E]

section

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible]
/-- Two elements `δ`, `γ` of `S.G E` with the same matrix `frameProducts` have, at every infinite
place `v`, images `S.ratToInf δ v` and `S.ratToInf γ v` in `G₁` with the same matrix
`realFrameGram`. -/
lemma realFrameGram_ratToInf_congr {δ : S.G E} (hδ : S.frameProducts δ = S.frameProducts γ)
    {v : InfinitePlace E} : realFrameGram (S.ratToInf δ v) = realFrameGram (S.ratToInf γ v) := by
  ext a b
  simp [hδ]

/-- If `δ` has the same matrix `frameProducts` as `γ` and `u ∈ besselU0` (a unipotent element of
`G₁` fixing each frame vector), then at every infinite place `v`, `u⁻¹ * S.ratToInf δ v` has the
same matrix `realFrameGram` as `S.ratToInf γ v`. -/
lemma realFrameGram_inv_mul_ratToInf {u : 𝔰.G₁} (hu : u ∈ besselU0) {δ : S.G E}
    (hδ : S.frameProducts δ = S.frameProducts γ) {v : InfinitePlace E} :
    realFrameGram (u⁻¹ * S.ratToInf δ v) = realFrameGram (S.ratToInf γ v) := by
  simp [← realFrameGram_ratToInf_congr hδ, realFrameGram_mul_of_mem_besselFixer, hu,
    mem_besselFixer_of_mem_besselU0]

/-- At the infinite place `v`, take the leading `j × j` minor of `realFrameGram (S.ratToInf γ v)`,
the matrix of products in the unit frame. Its modulus is
`(|realM v| ^ ∑_{a < j} (ϱ - a)) ^ 2 / N ^ j` times `‖Φ v (leadingMinor (frameProducts γ) j)‖`. So
each index `a < j` contributes the square of its scale `basisScale`, which is
`realM v ^ (ϱ - a) / √N`. -/
lemma norm_det_submatrix_realFrameGram (v : InfinitePlace E) :
    ‖((realFrameGram (S.ratToInf γ v)).submatrix (castLE j.is_le) (castLE j.is_le)).det‖ =
      (|S.realM v| ^ ∑ a : Fin j, (𝔰.ϱ - a)) ^ 2 / S.N ^ j.val *
        ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ := by
  rw [det_submatrix_realFrameGram_ratToInf, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Finset.prod_div_distrib, abs_div, abs_prod]
  simp [leadingMinor, prod_pow_eq_pow_sum, ← pow_mul, sum_mul, mul_comm 2]

/-- If `γ` has cell rank `j`, the determinant of the products of `e₁, …, e_i, z` (`i = min ϱ j`)
with their images, in the unit frame at `v` (the matrix `subframeBlock`), has the modulus of the
rescaled leading minor of order `j` of `S.frameProducts γ`. -/
lemma HasCellRank.norm_det_subframeBlock (h_rank : S.HasCellRank j γ) (v : InfinitePlace E) :
    ‖(subframeBlock (min_le_left 𝔰.ϱ j) (realFrameGram (S.ratToInf γ v))).det‖ =
      (|S.realM v| ^ ∑ a : Fin j, (𝔰.ϱ - a)) ^ 2 / S.N ^ j.val *
        ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ := by
  have h_pair : NormOnePairOccursFrom j (S.ratToInf γ v) := h_rank.normOnePairOccursFrom.ratToInf v
  rw [← norm_det_submatrix_realFrameGram]
  exact RealPlace.norm_det_subframeBlock (min_le_left 𝔰.ϱ j) (hZ := rfl) h_pair j.is_le
    (hij := rfl)

omit [HasPrimitiveRoot5040 E] in
/-- A matrix product `P * M` with `P` integral has the conjugates of its rows in every `Ô`-module
that contains the conjugates of the rows of `M`. -/
lemma col_conjTranspose_mul_mem {m m' n : Type} [Fintype m]
    {M : Matrix m n (𝔸f E)} {P : Matrix m' m (𝔸f E)} (hP : IsIntMatrix (Ô E) P)
    {K : Submodule (Ô E) (n → 𝔸f E)} (hM : ∀ r : m, Mᴴ.col r ∈ K) (i : m') :
    (P * M)ᴴ.col i ∈ K := by
  rw [conjTranspose_mul]
  exact colLattice_le hM ⟨Pᴴ.col i, fun r ↦ hP.conjTranspose r i, rfl⟩

variable (S j)

/-- The first `min ϱ j` indices of the isotropic vectors of the frame. -/
abbrev initialIsotropicIndex : Fin (min 𝔰.ϱ j) ↪ Fin 𝔰.ϱ := castLEEmb (min_le_left 𝔰.ϱ j)

/-- The diagonal matrix with entries `S.M / basisScale v (e_l)`, `l < min ϱ j`. It converts the
parameters of a shift, given in the rational frame, to the unit frame at the place `v`. -/
noncomputable def shiftScaling (v : InfinitePlace E) :
    Matrix (Fin (min 𝔰.ϱ j)) (Fin (min 𝔰.ϱ j)) ℂ :=
  diagonal fun l ↦ S.M / S.basisScale v (.inl (initialIsotropicIndex j l))

/-- The shift with parameter `x`: at each infinite place, the unipotent element with central
parameter `0` that acts on `X₀` as the product of the Eichler maps along `e₁, …, e_i`,
`i = min ϱ j`, with the parameters given by the rows of `(shiftScaling j v)ᴴ * x v`: the vectors
`x_l` multiplied by the conjugates of `S.M / basisScale v (e_l)`. -/
noncomputable def eichlerShift (x : InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ)
    (v : InfinitePlace E) : 𝔰.G₁ :=
  unipotentOf (inclMatrix ℂ (initialIsotropicIndex j) * ((S.shiftScaling j v)ᴴ * of (x v)), 0)

/-- The bound of `RealPlace.exists_majorant_volumeRatio_inv_pow` for the integral of the kernel at
the place `v`, times the Jacobian of the passage to the parameters of `eichlerShift`. -/
noncomputable def kernelBound (γ : S.G E) (v : InfinitePlace E) : ℝ :=
  ‖(S.shiftScaling j v).det‖⁻¹ ^ (2 * 𝔰.k) *
    ((2 * S.frameBoxRadius ^ 2) ^ ((min 𝔰.ϱ j + 1) * min 𝔰.ϱ j) *
      (2 ^ (min 𝔰.ϱ j + 1) * (S.b ^ (6 * 𝔰.n + 2)) ^ (2 * (j - min 𝔰.ϱ j))) ^ 𝔰.k /
      ‖(subframeBlock (min_le_left 𝔰.ϱ j) (realFrameGram (S.ratToInf γ v))).det‖ ^
        (𝔰.k + min 𝔰.ϱ j))

variable {S j}

/-- The columns of `l` lie in `Λ ∩ X₀`, where `Λ` is the lattice of the class `c`, and modulo the
isotropic space the frame of `p` is that of `p₀` moved in `X₀` by `S.M • l` times the first
`min ϱ j` rows of the matrix of products of `γ`. -/
def IsLatticeTranslate (c : S.Classes) (γ p₀ p : S.G E) (l : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E) :
    Prop :=
  IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix l) ∧
    (frameImage (p : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₂ =
      (frameImage (p₀ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₂ +
        fromRows (fromRows (S.M • (l * (isotropicRows (S.frameProducts γ)).submatrix
          (initialIsotropicIndex j) id)) 0) 0

@[fun_prop]
lemma measurable_eichlerShift : Measurable (S.eichlerShift j) := by
  unfold eichlerShift
  exact Continuous.measurable (by fun_prop)

/-- At every place a shift `eichlerShift` is a unipotent element that fixes the frame. -/
lemma eichlerShift_mem (x : InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ) (v : InfinitePlace E) :
    S.eichlerShift j x v ∈ besselU0 :=
  unipotentOf_mem_besselU0 _

/-- Let `p` be a lattice translate of `p₀` by `q`, for the lattice of the class `c` and the matrix
of products of `γ`. In the unit frame at the place `v`, the parts in `X₀` of the two frames
(`frameX₀Part`) differ by the conjugate transpose of the rescaled point `conjColumnsAtInfinity q`
times the first `min ϱ j` isotropic rows of products of `γ`. -/
lemma IsLatticeTranslate.frameX₀Part_eq {p p₀ : S.G E} {q : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E}
    (hq : IsLatticeTranslate c γ p₀ p q) (v : InfinitePlace E) :
    frameX₀Part (S.ratToInf p v) = frameX₀Part (S.ratToInf p₀ v) +
      ((S.shiftScaling j v)ᴴ * of (conjColumnsAtInfinity E 𝔰 (Fin (min 𝔰.ϱ j)) q v))ᴴ *
        (isotropicRows (realFrameGram (S.ratToInf γ v))).submatrix (initialIsotropicIndex j)
          id := by
  ext a b
  obtain ⟨-, hq_eq⟩ := hq
  have h_entry : p.1.1 (𝔰.indexX₀ a) (𝔰.besselFrame b) = p₀.1.1 (𝔰.indexX₀ a) (𝔰.besselFrame b) +
      S.M * ∑ l, q a l * S.frameProducts γ (initialIsotropicIndex j l).castSucc b := by
    have h_translate_entry := congrFun₂ hq_eq (.inl (.inl a)) b
    simpa [Matrix.mul_apply] using h_translate_entry
  have h_term (l : Fin (min 𝔰.ϱ j)) :
      S.M * (Φ v (q a l) * Φ v (S.frameProducts γ (initialIsotropicIndex j l).castSucc b)) *
          S.basisScale v (𝔰.besselFrame b) =
        Φ v (q a l) * (S.M / S.basisScale v (.inl (initialIsotropicIndex j l))) *
          realFrameGram (S.ratToInf γ v) (initialIsotropicIndex j l).castSucc b := by
    have h_scale : S.basisScale v (.inl (initialIsotropicIndex j l)) =
        S.realM v ^ (𝔰.ϱ - initialIsotropicIndex j l) / √S.N := by simp [basisScale]
    have h_sqrt : (S.N : ℂ) = √S.N * √S.N := by
      rw [← Complex.ofReal_mul, mul_self_sqrt S.N.cast_nonneg, Complex.ofReal_natCast]
    have h_ne : (√S.N : ℂ) ≠ 0 := by simp [Nat.Prime.ne_zero]
    simp only [realFrameGram_ratToInf, basisScale_besselFrame, h_scale, val_castSucc]
    push_cast
    rw [h_sqrt]
    field_simp
  have h_one : S.basisScale v (𝔰.indexX₀ a) = 1 := by simp [basisScale]
  rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.add_apply, Matrix.mul_apply]
  simp only [shiftScaling, mul_diagonal, conjTranspose_apply, of_apply, conjColumnsAtInfinity_apply,
    star_star, submatrix_apply, id_eq, ← h_term]
  simp [frameX₀Part, inclMatrix, Matrix.mul_apply, Matrix.one_apply, h_entry, add_mul, mul_sum,
    sum_mul, h_one, -Nat.cast_mul]

/-- **The shifted points.** Let `p` be a lattice translate of `p₀` by `q`, both with the matrix of
products `frameProducts γ`. Let `u` lie in `besselU0`, and let `s` be `eichlerShift j x v`. Then the
parts in `X₀` (`frameX₀Part`) of the frames of `(u s)⁻¹ p` and of `u⁻¹ p₀` at `v` differ by a
product. The first factor is the conjugate transpose of the point `conjColumnsAtInfinity q + x`,
rescaled by `shiftScaling j v`. The second factor is the first `min ϱ j` isotropic rows of products
of `γ`. -/
lemma frameX₀Part_eichlerShift_inv_mul {p p₀ : S.G E} (hp : S.frameProducts p = S.frameProducts γ)
    (hp₀ : S.frameProducts p₀ = S.frameProducts γ) {q : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E}
    (hq : IsLatticeTranslate c γ p₀ p q) (v : InfinitePlace E) {u : 𝔰.G₁} (hu : u ∈ besselU0)
    (x : InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ) :
    frameX₀Part ((u * S.eichlerShift j x v)⁻¹ * S.ratToInf p v) =
      frameX₀Part (u⁻¹ * S.ratToInf p₀ v) +
        ((S.shiftScaling j v)ᴴ * of ((conjColumnsAtInfinity E 𝔰 (Fin (min 𝔰.ϱ j)) q + x) v))ᴴ *
          (isotropicRows (realFrameGram (S.ratToInf γ v))).submatrix (initialIsotropicIndex j)
            id := by
  obtain ⟨t, rfl⟩ : ∃ t : 𝔰.UnipotentParams, u = unipotentOf t :=
    mem_besselU0_iff_unipotentOf.1 hu
  set Z : 𝔰.FrameMatrix := realFrameGram (S.ratToInf γ v) with hZ
  have h_moved : frameX₀Part ((unipotentOf t * S.eichlerShift j x v)⁻¹ * S.ratToInf p v) =
      frameX₀Part (S.ratToInf p v) + t.1ᴴ * isotropicRows Z +
        ((S.shiftScaling j v)ᴴ * of (x v))ᴴ * (isotropicRows Z).submatrix (initialIsotropicIndex j)
          id := by
    rw [_root_.mul_inv_rev, mul_assoc, eichlerShift, frameX₀Part_unipotentOf_inv_mul,
      realFrameGram_inv_mul_ratToInf hu hp, frameX₀Part_unipotentOf_inv_mul,
      realFrameGram_ratToInf_congr hp, conjTranspose_mul (inclMatrix ℂ _),
      Matrix.mul_assoc _ _ᴴ, conjTranspose_inclMatrix_mul]
  have h_base : frameX₀Part ((unipotentOf t)⁻¹ * S.ratToInf p₀ v) =
      frameX₀Part (S.ratToInf p₀ v) + t.1ᴴ * isotropicRows Z := by
    rw [frameX₀Part_unipotentOf_inv_mul, realFrameGram_ratToInf_congr hp₀]
  rw [h_moved, h_base, hq.frameX₀Part_eq, Pi.add_apply, ← of_add_of, Matrix.mul_add,
    conjTranspose_add, Matrix.add_mul]
  abel

/-- Two terms with the same matrix of products differ, in the middle part of the frame, by vectors
of `X₀`: in the basis of the lattice of `c`, the difference is `S.classCoordX₀ c` times the
difference of the rational coordinates in `X₀`, taken as finite adeles. -/
lemma frameMiddle_translateByClassReps_sub {p p' : S.G E}
    (hZ : S.frameProducts p' = S.frameProducts p) :
    frameMiddle (S.translateByClassReps c c' p') - frameMiddle (S.translateByClassReps c c' p) =
      S.classCoordX₀ c * finAdeleMatrix
        (frameMiddle (p' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) -
          frameMiddle (p : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₁ := by
  have hz_eq (b : Fin (𝔰.ϱ + 1)) :
      (p' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) 𝔰.z (𝔰.besselFrame b) =
        (p : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) 𝔰.z (𝔰.besselFrame b) := by
    simpa [frameGram, splitGram, middleGram, Matrix.mul_apply, Nat.Prime.ne_zero] using
      congrFun₂ hZ 𝔰.top b
  ext r b
  simp [frameMiddle_translateByClassReps, hz_eq, Matrix.mul_apply, mul_sub]

end

omit [HasPrimitiveRoot5040 E] in
/-- If `γ` has cell rank `j`, the products of `e₁, …, e_i, z` (`i = min ϱ j`) with their images
form an invertible matrix at every infinite place. -/
lemma HasCellRank.det_subframeBlock_ne_zero (h_rank : S.HasCellRank j γ) (v : InfinitePlace E) :
    (subframeBlock (min_le_left 𝔰.ϱ j) (realFrameGram (S.ratToInf γ v))).det ≠ 0 := by
  have hδ : 0 < ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ := by
    simpa using h_rank.leadingMinor_ne_zero
  have hκ : 1 ≤ |S.realM v| := one_le_abs_realM v
  have hN : 0 < S.N := S.N_prime.pos
  rw [← norm_pos_iff, h_rank.norm_det_subframeBlock]
  positivity

omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
/-- Let `γ` have cell rank `j` (`HasCellRank`), let `ξ` be the first `min ϱ j` isotropic rows of
`frameProducts γ`, and let `p₀`, `p` have the same matrix of products as `γ`. Suppose the middle
parts (`frameMiddle`) of the frames moved by `translateByClassReps c c' p` and
`translateByClassReps c c' p₀` differ row by row by `M` times `Ô`-linear combinations of the rows of
`ξ`, taken as finite adeles (`finAdeleMatrix`). Then `p` is a lattice translate of `p₀`. -/
lemma HasCellRank.exists_isLatticeTranslate (h_rank : S.HasCellRank j γ) {p₀ p : S.G E}
    (hZ₀ : S.frameProducts p₀ = S.frameProducts γ) (hZ : S.frameProducts p = S.frameProducts γ)
    (h_rows : ∀ r : 𝔰.MiddleIndex,
      (frameMiddle (S.translateByClassReps c c' p) - frameMiddle
        (S.translateByClassReps c c' p₀))ᴴ.col r ∈
        S.ideleM • colLattice (Ô E)
          (finAdeleMatrix ((isotropicRows (S.frameProducts γ)).submatrix (initialIsotropicIndex j)
            id))ᴴ) :
    ∃ l : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E, IsLatticeTranslate c γ p₀ p l := by
  -- The rows of `ξ` are independent, so the adelic coefficients `W` come from a rational `l`.
  set ξ : Matrix (Fin (min 𝔰.ϱ j)) (Fin (𝔰.ϱ + 1)) E :=
    (isotropicRows (S.frameProducts γ)).submatrix (initialIsotropicIndex j) id with hξ
  let ξ' : Matrix (Fin (𝔰.ϱ + 1)) (Fin (min 𝔰.ϱ j)) E :=
    (paddedLeading j (S.frameProducts γ))⁻¹.submatrix id (castSucc ∘ initialIsotropicIndex j)
  have h_inv : ξ * ξ' = 1 := by
    ext a b
    have ha : a.val < j.val := a.isLt.trans_le (min_le_right _ _)
    simpa [hξ, ξ', paddedLeading, Matrix.mul_apply, ha, Matrix.one_apply, Fin.ext_iff] using
      congrFun₂ h_rank.paddedLeading_mul_inv (initialIsotropicIndex j a).castSucc
        (initialIsotropicIndex j b).castSucc
  have h_eq : S.frameProducts p = S.frameProducts p₀ := hZ.trans hZ₀.symm
  set x : Matrix 𝔰.κ (Fin (𝔰.ϱ + 1)) E := (frameMiddle p.1.1 - frameMiddle p₀.1.1).toRows₁ with hx
  rw [frameMiddle_translateByClassReps_sub h_eq, ← colLattice_smul] at h_rows
  obtain ⟨W, hW_int, hW⟩ := exists_isIntMatrix_mul_eq_of_col_mem h_rows
  have h_adelic : S.classCoordX₀ c * finAdeleMatrix x = (S.M : 𝔸f E) • (Wᴴ * finAdeleMatrix ξ) := by
    rw [← conjTranspose_conjTranspose (S.classCoordX₀ c * finAdeleMatrix x), ← hW]
    simp [Units.smul_def, ideleM_val]
  let l : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E := (S.M : E)⁻¹ • (x * ξ')
  have hl : S.classCoordX₀ c * finAdeleMatrix l = Wᴴ := by
    have h_cancel : (((S.M : E)⁻¹ : E) : 𝔸f E) * (S.M : 𝔸f E) = 1 := by
      simpa [Nat.Prime.ne_zero, -Nat.cast_mul] using
        (map_mul (algebraMap E (𝔸f E)) (S.M : E)⁻¹ S.M).symm
    rw [finAdeleMatrix_smul, finAdeleMatrix_mul, Matrix.mul_smul, ← Matrix.mul_assoc, h_adelic,
      Matrix.smul_mul, Matrix.mul_assoc, ← finAdeleMatrix_mul, h_inv, smul_smul, h_cancel]
    simp
  have h_rational : x = S.M • (l * ξ) := by
    -- `classCoordX₀ c` has a left inverse, so it is enough to compare coordinates.
    have h_coords : S.classCoordX₀ c * finAdeleMatrix x =
        S.classCoordX₀ c * finAdeleMatrix ((S.M : E) • (l * ξ)) := by
      simp [h_adelic, finAdeleMatrix_smul, ← Matrix.mul_assoc, hl]
    rw [← Nat.cast_smul_eq_nsmul E]
    exact Matrix.map_injective (algebraMap E (𝔸f E)).injective
      (mul_right_injective_of_inv _ _ (gram_classCoordX₀ c) h_coords)
  refine ⟨l, by simpa only [hl] using hW_int.conjTranspose, ?_⟩
  rw [← hξ, ← h_rational]
  ext (⟨i | i⟩ | i) b
  · simp [hx]
  · simpa [frameGram, splitGram, middleGram, Matrix.mul_apply, S.N_prime.ne_zero] using
      congrFun₂ h_eq 𝔰.top b
  · simpa [frameGram, Matrix.mul_apply, Matrix.one_apply] using congrFun₂ h_eq i.castSucc b

omit [S.IsAdmissible] in
/-- Let `γ` have cell rank `j` and lie over the block `(c, s, c')`, let `Λ` be the lattice of the
class `c` and `A` the span of the isotropic vectors `e_a` of the frame. A term `p` is a lattice
translate of `p₀` by `l` if `l` has columns in `Λ ∩ X₀` and, modulo `A`, the frame of `p` is that of
`p₀` moved in `X₀` by `M l` times the first `min ϱ j` rows of products of `γ`. If the sum of `w` is
at most `bound` over every subset `B` of the orbit of `γ` that consists of translates of one of its
points, then the sum over the orbit is at most `isotropicRowsIndex ^ k * bound`, as the orbit falls
into at most `isotropicRowsIndex ^ k` such sets. -/
lemma tsum_orbit_le_of_isLatticeTranslate (h_over : γ ∈ S.termsOver c s c')
    (h_rank : S.HasCellRank j γ) (w : S.G E → ℝ≥0∞) (bound : ℝ≥0∞)
    (h_coset : ∀ B : Set (S.G E), B ⊆ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c') →
      ∀ p₀ ∈ B, ∀ l : S.G E → Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E,
        (∀ p ∈ B, IsLatticeTranslate c γ p₀ p (l p)) → ∑' p : B, w p ≤ bound) :
    ∑' p : doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'), w p ≤
      .ofReal (S.isotropicRowsIndex j (S.translateByClassReps c c' γ) ^ 𝔰.k) * bound := by
  -- The middle parts of the frames differ by `k` rows in a basis of `Λ ∩ X₀`. These rows lie in `M`
  -- times the larger lattice in the definition of `isotropicRowsIndex`; colour them modulo `M`
  -- times the smaller one. `a` is a basis of `Λ ∩ X₀`, and `Q` is an integral left inverse of its
  -- coordinates.
  obtain ⟨a, -, ha, Q, hQ, hQa⟩ :=
    exists_preimageLattice_eq_colLattice (R := Ô E) ⟨_, gram_classCoordX₀ c⟩
  -- `D p` is the change of the middle part of the frame from `γ` to `p`, and `Z` is the matrix of
  -- products of `γ` in the basis of the lattice.
  let D (p : S.G E) : Matrix 𝔰.MiddleIndex (Fin (𝔰.ϱ + 1)) (𝔸f E) :=
    frameMiddle (S.translateByClassReps c c' p) - frameMiddle (S.translateByClassReps c c' γ)
  let Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) (𝔸f E) :=
    (S.latticeMiddle (𝔸f E)).frameGram (S.translateByClassReps c c' γ)
  let latticeBelow : Submodule (Ô E) (Fin (𝔰.ϱ + 1) → 𝔸f E) :=
    colLattice (Ô E) (Z.submatrix (fun b : IndexBelow j ↦ b.val.castSucc) _root_.id)ᴴ
  have h_index : relIndex (S.ideleM • latticeBelow.toAddSubgroup)
      (S.ideleM • (colLattice (Ô E) (isotropicRows Z)ᴴ).toAddSubgroup) ≠ 0 :=
    ((relIndex_pointwise_smul S.ideleM ..).trans_gt (isotropicRowsIndex_pos h_over h_rank)).ne'
  have h_mem_all (p : S.G E) (hp : p ∈ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'))
      (i : 𝔰.κ) : (Q * D p)ᴴ.col i ∈ S.ideleM • colLattice (Ô E) (isotropicRows Z)ᴴ :=
    col_conjTranspose_mul_mem hQ (col_frameMiddle_sub_mem hp) i
  have h_card : card 𝔰.κ = 𝔰.k := by simp
  rw [isotropicRowsIndex, submoduleIndex, ← relIndex_pointwise_smul S.ideleM, ← h_card]
  refine tsum_le_relIndex_pow_mul (fun p ↦ (Q * D p)ᴴ.col) h_index h_mem_all w bound
    fun B hB p₀ hp₀ h_colour ↦ ?_
  have hZ {p : S.G E} (hp : p ∈ B) : S.frameProducts p = S.frameProducts γ :=
    frameProducts_eq_of_mem_doubleCoset (hB hp)
  have h_basis {p : S.G E} (hp : p ∈ B) : S.classCoordX₀ c * a.val * (Q * D p) = D p := by
    have hQ_inv : Q * S.classCoordX₀ c = (a⁻¹).val :=
      (Units.inv_eq_of_mul_eq_one_left (by rw [Matrix.mul_assoc, hQa])).symm
    simp [D, frameMiddle_translateByClassReps_sub (hZ hp), ← Matrix.mul_assoc Q, hQ_inv,
      Matrix.mul_assoc,
      ← Matrix.mul_assoc a.val]
  have h_rows_le : latticeBelow ≤ colLattice (Ô E)
    ((isotropicRows Z).submatrix (initialIsotropicIndex j) _root_.id)ᴴ :=
    colLattice_le fun ⟨b, hb⟩ ↦ col_mem_colLattice (⟨b, lt_min b.isLt hb⟩ : Fin (min 𝔰.ϱ j))
  -- Two terms of one colour differ by `M` times the smaller lattice, so are lattice translates.
  have h_translate (p : S.G E) (hp : p ∈ B) :
      ∃ l : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E, IsLatticeTranslate c γ p₀ p l := by
    refine h_rank.exists_isLatticeTranslate (c' := c') (hZ hp₀) (hZ hp) fun r ↦ ?_
    have h_diff : frameMiddle (S.translateByClassReps c c' p) - frameMiddle
      (S.translateByClassReps c c' p₀) =
        S.classCoordX₀ c * a.val * (Q * D p - Q * D p₀) := by
      rw [Matrix.mul_sub, h_basis hp, h_basis hp₀, sub_sub_sub_cancel_right]
    have h_mem (i : 𝔰.κ) : (Q * D p - Q * D p₀)ᴴ.col i ∈
        S.ideleM • colLattice (Ô E) ((isotropicRows Z).submatrix (initialIsotropicIndex j)
          _root_.id)ᴴ := by
      rw [conjTranspose_sub]
      exact Set.smul_set_mono h_rows_le (h_colour p hp p₀ hp₀ i)
    rw [h_diff]
    simpa [Z, frameGram_translateByClassReps] using! col_conjTranspose_mul_mem ha h_mem r
  choose! l hl using h_translate
  exact h_coset B hB p₀ hp₀ l hl

/-- Let the terms of `B` lie in the orbit of `γ` and be lattice translates of `p₀` with parameters
`l`. The frames of the terms with one lattice point `q` differ by vectors of the isotropic space. So
by packing, for `γ` over the block `(c, s, c')` and any exponent `i`, the sum of their weights
`schurWeight` at `y` is at most `tailScale` times a common bound `C` for the products over the
places of the powers `-(k + i)` of the ratios of the volumes (`volumeRatio`). -/
lemma tsum_schurWeight_fibre_le {B : Set (S.G E)}
    (hB : B ⊆ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c')) {p₀ : S.G E}
    {l : S.G E → Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E}
    (hl : ∀ p ∈ B, IsLatticeTranslate c γ p₀ p (l p))
    {y : NumberField.InfinitePlace E → 𝔰.G₁} (h_over : γ ∈ S.termsOver c s c')
    (q : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E) {i : ℕ} {C : ℝ≥0∞}
    (hC : ∀ p ∈ B, l p = q →
      ∏ v : NumberField.InfinitePlace E,
        ENNReal.ofReal ((volumeRatio (S.ratToInf p v) (y v))⁻¹ ^ (𝔰.k + i)) ≤ C) :
    ∑' p : {p ∈ B | l p = q}, S.schurWeight c' p i y ≤ .ofReal S.tailScale * C := by
  have h_term (p : {p ∈ B | l p = q}) (_ : S.schurWeight c' p i y ≠ 0) :
      S.schurWeight c' p i y ≤ S.classCutoff c' ((S.ratToInf p)⁻¹ * y) * C := by
    obtain ⟨p, hp_mem, hp_point⟩ := p
    grw [schurWeight, boxCutoff, Set.indicator_le_self .., hC p hp_mem hp_point]
  have h_box (p : {p ∈ B | l p = q}) (hp : S.schurWeight c' p i y ≠ 0) :
      (S.ratToInf p)⁻¹ * y ∈ S.boxedPoints :=
    Set.mem_of_indicator_ne_zero (left_ne_zero_of_mul hp)
  -- `V` is the space of `n`-tuples of vectors of the isotropic space, seen from `y`.
  let V : Submodule ℝ (NumberField.InfinitePlace E → Fin 𝔰.n → EuclideanSpace ℂ 𝔰.BesselIndex) :=
    (piMap fun v ↦ Fintype.linearCombination ℂ (fun a : Fin 𝔰.ϱ ↦ frameVector (y v) a.castSucc)
      |>.restrictScalars ℝ |>.compLeft (Fin 𝔰.n)).range
  -- `10 ^ 5 * n ^ 9 * numInfPlaces E` is the exponent of `b` up to which `pow_le_tailScale` bounds
  -- by `S.tailScale`.
  have h_dim : 6 * 𝔰.n ^ 2 * Module.finrank ℝ V ≤ 10 ^ 5 * 𝔰.n ^ 9 * numInfPlaces E := by
    grw [finrank_range_le]
    simp [Module.finrank_pi_fintype]
    lia
  have h_differ (p : {p ∈ B | l p = q}) (_ : S.schurWeight c' p i y ≠ 0) (p₁ : {p ∈ B | l p = q})
      (_ : S.schurWeight c' p₁ i y ≠ 0) :
      (fun v ↦ frameVector ((S.ratToInf p v)⁻¹ * y v)) -
        (fun v ↦ frameVector ((S.ratToInf p₁ v)⁻¹ * y v)) ∈ V := by
    obtain ⟨p, hp_mem, hp_point⟩ := p
    obtain ⟨p₁, hp₁_mem, hp₁_point⟩ := p₁
    obtain ⟨-, hp_eq⟩ := hl p hp_mem
    obtain ⟨-, hp₁_eq⟩ := hl p₁ hp₁_mem
    have h_rows : (frameImage p.val.val).toRows₂ = (frameImage p₁.val.val).toRows₂ := by
      rw [hp_eq, hp₁_eq, hp_point, hp₁_point]
    exact ⟨_, funext₂ fun v _ ↦ (frameVector_sub_eq_sum h_rows ..).symm⟩
  have h_lie (p : {p ∈ B | l p = q}) (_ : S.schurWeight c' p i y ≠ 0) :
      p.val ∈ S.termsOver c s c' :=
    termsOver.of_mem_doubleCoset (hB p.property.1) h_over
  have h_size (p : {p ∈ B | l p = q}) (hp : S.schurWeight c' p i y ≠ 0)
      (v : NumberField.InfinitePlace E) :
      besselLength (((S.ratToInf p)⁻¹ * y) v) ≤ S.b ^ (6 * 𝔰.n + 2) * 1 :=
    (inCut_of_mem_boxedPoints (h_box p hp) v).trans_eq (mul_one _).symm
  refine (tsum_le_of_le_classCutoff_mul le_rfl (fun _ ↦ Subtype.ext) h_lie h_size h_term
    h_differ).trans ?_
  grw [one_pow, mul_one, ← pow_mul, pow_le_tailScale h_dim]

omit [HasPrimitiveRoot5040 E] in
/-- **The kernel at one place.** Let `γ` have cell rank `j`, let `i = min ϱ j`, let `y` be boxed,
and let `Z` be the matrix of products of `γ` in the unit frame at `v`. Let `g₀` have the products
`Z`, with a norm-one pair from `j`. There is a measurable `φ` on `X₀ ^ i` with integral at most
`kernelBound j γ v` such that `volumeRatio g (y v) ^ (-(k + i)) ≤ φ A` for every `g` with the same
two properties whose frame differs in `X₀` from that of `g₀` by the rescaled point `A` times the
first `i` rows of `Z`. -/
lemma HasCellRank.exists_majorant_lintegral_le_kernelBound (h_rank : S.HasCellRank j γ)
    {y : InfinitePlace E → 𝔰.G₁} (hy : y ∈ S.boxedPoints) (v : InfinitePlace E) {g₀ : 𝔰.G₁}
    (hg₀_gram : realFrameGram g₀ = realFrameGram (S.ratToInf γ v))
    (hg₀_pair : NormOnePairOccursFrom j g₀) :
    ∃ φ : (Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ) → ℝ≥0∞, Measurable φ ∧
      ∫⁻ A : Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ, φ A ≤ .ofReal (S.kernelBound j γ v) ∧
      ∀ (g : 𝔰.G₁) (A : Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ),
        realFrameGram g = realFrameGram (S.ratToInf γ v) → NormOnePairOccursFrom j g →
        frameX₀Part g = frameX₀Part g₀ + ((S.shiftScaling j v)ᴴ * of A)ᴴ *
          (isotropicRows (realFrameGram (S.ratToInf γ v))).submatrix (initialIsotropicIndex j) id →
        .ofReal ((volumeRatio g (y v))⁻¹ ^ (𝔰.k + min 𝔰.ϱ j)) ≤ φ A := by
  have h_box : y v ∈ frameBox S.frameBoxRadius := mem_frameBox_of_mem_boxedPoints hy v
  have h_cut : InCut (y v) S.b := inCut_of_mem_boxedPoints hy v
  have h_seven : 7 ≤ 𝔰.k := by
    have h_base : 2 ^ 9 ≤ (2 * 𝔰.ϱ + 2) ^ 9 := Nat.pow_le_pow_left (by lia) 9
    grind [S.pow_le_k]
  obtain ⟨φ₀, h_meas, h_int, h_le⟩ := exists_majorant_volumeRatio_inv_pow (min_le_left 𝔰.ϱ j)
    h_box h_cut j.is_le (hij := rfl) h_seven hg₀_gram hg₀_pair (h_rank.det_subframeBlock_ne_zero v)
  -- Pass to the parameters of the shift; the term `+ 0` is the form that `lintegral_comp_mul_add`
  -- takes.
  refine ⟨fun A ↦ φ₀ ((S.shiftScaling j v)ᴴ * of A + 0), h_meas.comp (Continuous.measurable ?_),
    ?_, fun g A hg_gram hg_pair hg_part ↦ h_le g _ hg_gram hg_pair ?_⟩
  · fun_prop
  · -- The change of variables brings in the Jacobian that `kernelBound` carries.
    have h_det : (S.shiftScaling j v)ᴴ.det ≠ 0 := by
      simp [shiftScaling, prod_eq_zero_iff, Nat.Prime.ne_zero]
    have h_card : card 𝔰.κ = 𝔰.k := by simp
    refine (lintegral_comp_mul_add h_det 0 h_meas).trans_le ?_
    grw [h_int, det_conjTranspose, norm_star, h_card, kernelBound, ofReal_mul (by positivity)]
  · rw [hg_part, Matrix.add_mul, Matrix.mul_assoc, mul_inclMatrix ((isotropicRows _).submatrix _ _)]
    congr 2
    · exact congrArg conjTranspose (add_zero _).symm
    · ext a b
      simp

/-- **From cosets to a lattice.** Let `γ` be a term of cell rank `j` over the block `(c, s, c')`,
let `i = min ϱ j` and let `Λ` be the lattice of `c`. Let `B` be a set of terms of the orbit of `γ`,
each a lattice translate of `p₀ ∈ B`: the matrix `l p` has columns in `Λ ∩ X₀` and, modulo the
isotropic space, the frame of `p` is that of `p₀` moved in `X₀` by `M * l p` times the first `i`
rows of products of `γ`. Let `u v` be unipotent and fix the frame at every place `v`, and let `y` be
boxed. There is a measurable `φ` whose integral is at most the product of the explicit numbers
`kernelBound j γ v`, which bound the integrals of its local factors, such that for every `x` the sum
over `B` of the weights `schurWeight` at `u * eichlerShift j x * y` is at most `S.tailScale` times
the sum of `φ` over the translate by `x` of the lattice `(Λ ∩ X₀) ^ i` (`columnLattice`). -/
lemma exists_tsum_schurWeight_le {B : Set (S.G E)}
    (hB : B ⊆ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c')) {p₀ : S.G E}
    (hp₀ : p₀ ∈ B) {l : S.G E → Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E}
    (hl : ∀ p ∈ B, IsLatticeTranslate c γ p₀ p (l p)) {u y : NumberField.InfinitePlace E → 𝔰.G₁}
    (hu : ∀ v : NumberField.InfinitePlace E, u v ∈ besselU0)
    (h_over : γ ∈ S.termsOver c s c') (h_rank : S.HasCellRank j γ) (hy : y ∈ S.boxedPoints) :
    ∃ φ : (NumberField.InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ) → ℝ≥0∞, Measurable φ ∧
      ∫⁻ x : NumberField.InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ, φ x ≤
        ∏ v : NumberField.InfinitePlace E, .ofReal (S.kernelBound j γ v) ∧
      ∀ x : NumberField.InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ,
        ∑' p : B, S.schurWeight c' p (min 𝔰.ϱ j) (u * S.eichlerShift j x * y) ≤
          .ofReal S.tailScale * ∑' w : S.columnLattice (Fin (min 𝔰.ϱ j)) c, φ (w +ᵥ x) := by
  -- `φ` is the product of the kernels at the places for the base point `u⁻¹ p₀`. The terms with one
  -- lattice point are then summed by packing.
  have hZ {p : S.G E} (hp : p ∈ B) : S.frameProducts p = S.frameProducts γ :=
    frameProducts_eq_of_mem_doubleCoset (hB hp)
  have h_pair {p : S.G E} (hp : p ∈ B) (v : InfinitePlace E) {g : 𝔰.G₁} (hg : g ∈ besselU0) :
      NormOnePairOccursFrom j (g⁻¹ * S.ratToInf p v) :=
    ((h_rank.of_mem_doubleCoset (hB hp)).normOnePairOccursFrom.ratToInf v).besselU_mul
      (inv_mem hg.1)
  choose φ₀ hφ₀_meas hφ₀_int hφ₀_le using fun v : InfinitePlace E ↦
    h_rank.exists_majorant_lintegral_le_kernelBound hy v
      (realFrameGram_inv_mul_ratToInf (hu v) (hZ hp₀)) (h_pair hp₀ v (hu v))
  refine ⟨fun x ↦ ∏ v : InfinitePlace E, φ₀ v (x v),
    Finset.measurable_prod _ fun v _ ↦ (hφ₀_meas v).comp (measurable_pi_apply v), ?_, fun x ↦ ?_⟩
  · rw [volume_pi, TauCeti.lintegral_fintype_prod_eq_prod _ hφ₀_meas]
    exact Finset.prod_le_prod fun v _ ↦ hφ₀_int v
  -- The kernel at the shifted lattice point of `p` bounds the ratio of the volumes of `p`.
  have h_ratio {p : S.G E} (hp : p ∈ B) (v : InfinitePlace E) :
      .ofReal ((volumeRatio (S.ratToInf p v) (u v * S.eichlerShift j x v * y v))⁻¹ ^
          (𝔰.k + min 𝔰.ϱ j)) ≤ φ₀ v ((conjColumnsAtInfinity E 𝔰 _ (l p) + x) v) := by
    have h_shift : u v * S.eichlerShift j x v ∈ besselU0 := mul_mem (hu v) (eichlerShift_mem x v)
    rw [volumeRatio_mul_left _ h_shift]
    exact hφ₀_le v _ _ (realFrameGram_inv_mul_ratToInf h_shift (hZ hp)) (h_pair hp v h_shift)
      (frameX₀Part_eichlerShift_inv_mul (hZ hp) (hZ hp₀) (hl p hp) v (hu v) x)
  -- Sort the terms by their lattice point and sum each fibre by packing.
  let point (p : B) : S.columnLattice (Fin (min 𝔰.ϱ j)) c :=
    ⟨conjColumnsAtInfinity E 𝔰 _ (l p), mem_columnLattice.2 ⟨l p, (hl p p.property).1, rfl⟩⟩
  rw [← tsum_fiberwise _ point, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun ⟨_, q, hq_int, rfl⟩ ↦ ?_
  let f (p : point ⁻¹' {⟨conjColumnsAtInfinity E 𝔰 _ q, ⟨q, hq_int, rfl⟩⟩}) : {p ∈ B | l p = q} :=
    ⟨p.val, p.val.property, conjColumnsAtInfinity_injective (congrArg Subtype.val p.property)⟩
  have hf : Function.Injective f := fun _ _ h_eq ↦
    Subtype.ext (Subtype.ext (congrArg Subtype.val h_eq :))
  refine (tsum_comp_le_tsum_of_injective (f := f) hf
    fun r ↦ S.schurWeight c' r (min 𝔰.ϱ j) (u * S.eichlerShift j x * y)).trans ?_
  refine tsum_schurWeight_fibre_le hB hl h_over q fun p hp hq ↦ ?_
  subst hq
  exact Finset.prod_le_prod fun v _ ↦ h_ratio hp v

omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
/-- The matrix `shiftScaling j v` is diagonal with entries `M / basisScale v (e_l)` for `l < i`. The
absolute value of its determinant is `(M √N) ^ i / |realM v| ^ ∑_{a < j} (ϱ - a)`, where
`i = min ϱ j`, `M = S.M` is the level, `N = S.N` is the number with `h(z, z) = -N`, and `S.realM v`
is the ratio of consecutive scales `basisScale` of the isotropic vectors. -/
lemma norm_det_shiftScaling (v : NumberField.InfinitePlace E) :
    ‖(S.shiftScaling j v).det‖ =
      (S.M * √S.N) ^ min 𝔰.ϱ j / |S.realM v| ^ ∑ a : Fin j, (𝔰.ϱ - a) := by
  -- The index `ϱ`, if it is below `j`, contributes `0` to the exponent.
  have h_exp : ∑ l : Fin (min 𝔰.ϱ j), (𝔰.ϱ - l) = ∑ a : Fin j, (𝔰.ϱ - a) := by
    refine sum_of_injective (castLE (min_le_right 𝔰.ϱ j)) (castLE_injective _) _ _
      (fun a ha ↦ ?_) fun _ ↦ rfl
    by_contra h_ne
    have ha_lt : a.val < min 𝔰.ϱ j := by lia
    exact ha ⟨⟨a, ha_lt⟩, rfl⟩
  have h_entry (l : Fin (min 𝔰.ϱ j)) :
      ‖(S.M / S.basisScale v (.inl (initialIsotropicIndex j l)) : ℂ)‖ =
        S.M * √S.N / |S.realM v| ^ (𝔰.ϱ - l) := by
    simp [basisScale, abs_of_nonneg, div_div_eq_mul_div, -Nat.cast_mul]
  rw [shiftScaling, det_diagonal, norm_prod, ← h_exp]
  simp only [h_entry]
  simp [prod_pow_eq_pow_sum, -Nat.cast_mul]

omit [HasPrimitiveRoot5040 E] in
/-- Let `γ` have cell rank `j ≥ 1`, let `i = min ϱ j`, and let `δ` be the image of the leading minor
of order `j` of `S.frameProducts γ` under the chosen embedding `Φ v` at the place `v`. The number
`kernelBound j γ v`, which bounds the integral over `X₀ ^ i` of the kernel of Schur's test at `v`,
is at most `((2 ρ²) ^ (i + 1) N ^ j / |δ|) ^ i` times the main factor
`((b ^ 13 / M²) ^ i N ^ (j - ϱ) / |δ|) ^ k`. Here `ρ = frameBoxRadius = b ^ (37 n)`, and the
truncated difference `j - ϱ` is `1` at the top rank `j = ϱ + 1` and `0` below. -/
lemma kernelBound_le (h_rank : S.HasCellRank j γ) (hj : j ≠ 0) (v : NumberField.InfinitePlace E) :
    S.kernelBound j γ v ≤
      ((2 * S.frameBoxRadius ^ 2) ^ (min 𝔰.ϱ j + 1) * S.N ^ j.val /
          ‖Φ v (leadingMinor (S.frameProducts γ) j)‖) ^ min 𝔰.ϱ j *
        ((S.b ^ 13 / S.M ^ 2) ^ min 𝔰.ϱ j * S.N ^ (j - 𝔰.ϱ) /
          ‖Φ v (leadingMinor (S.frameProducts γ) j)‖) ^ 𝔰.k := by
  have hb : 2 ≤ S.b := two_le_b
  have hM : 2 ≤ S.M := two_le_M
  have hN : 0 < S.N := S.N_prime.pos
  have hδ : 0 < ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ := by
    simpa using h_rank.leadingMinor_ne_zero
  rw [kernelBound, h_rank.norm_det_subframeBlock, norm_det_shiftScaling]
  set δ : ℝ := ‖Φ v (leadingMinor (S.frameProducts γ) j)‖
  set θ : ℝ := S.b ^ (6 * 𝔰.n + 2) with hθ
  set w : ℝ := |S.realM v| ^ ∑ a : Fin j, (𝔰.ϱ - a)
  set i : ℕ := min 𝔰.ϱ j with hi
  have hw : 1 ≤ w := one_le_pow₀ (one_le_abs_realM v)
  have h_extra : j - i = j - 𝔰.ϱ := by lia
  -- The last column: `2 ^ (i + 1) θ ^ (2 (j - i)) ≤ b ^ (13 i)`, as `i ≥ 1`, and `i = ϱ` is
  -- large if `j > i`: then `2 ^ (i + 1) ≤ b ^ (i - 17)`, as `2 ^ 2 ≤ b`.
  have h_last : 2 ^ (i + 1) * θ ^ (2 * (j - 𝔰.ϱ)) ≤ (S.b ^ 13) ^ i := by
    have h_four : 2 ^ 2 ≤ S.b := by linarith [S.thousand_le_b]
    have h_exp : i - 17 * (j - 𝔰.ϱ) + (6 * 𝔰.n + 2) * (2 * (j - 𝔰.ϱ)) ≤ 13 * i := by
      obtain h_zero | h_one : j - 𝔰.ϱ = 0 ∨ j - 𝔰.ϱ = 1 := by lia
      · grind
      · grind [S.ten_pow_five_le_varrho]
    have h_two : i + 1 ≤ 2 * (i - 17 * (j - 𝔰.ϱ)) := by
      grind [S.ten_pow_five_le_varrho, val_ne_zero_iff.2 hj]
    calc 2 ^ (i + 1) * θ ^ (2 * (j - 𝔰.ϱ))
        ≤ (2 ^ 2) ^ (i - 17 * (j - 𝔰.ϱ)) * θ ^ (2 * (j - 𝔰.ϱ)) := by
          grw [pow_le_pow_right₀ one_le_two h_two, pow_mul 2]
      _ ≤ S.b ^ (i - 17 * (j - 𝔰.ϱ)) * θ ^ (2 * (j - 𝔰.ϱ)) := by gcongr
      _ = S.b ^ (i - 17 * (j - 𝔰.ϱ) + (6 * 𝔰.n + 2) * (2 * (j - 𝔰.ϱ))) := by
          rw [hθ, ← pow_mul, ← pow_add]
      _ ≤ (S.b ^ 13) ^ i := by grw [← pow_mul, pow_le_pow_right₀ S.one_le_b h_exp]
  -- The power `w` of `|realM v|` from the scales of the unit frame cancels in the `k`-th power and
  -- is dropped in the `i`-th power.
  have h_power : (S.N : ℝ) ^ j.val = S.N ^ (j - 𝔰.ϱ) * S.N ^ i := by
    rw [← pow_add, ← h_extra, Nat.sub_add_cancel (min_le_right _ _)]
  have h_jacobian : ((S.M * √S.N) ^ i / w)⁻¹ ^ 2 = w ^ 2 / ((S.M ^ 2) ^ i * S.N ^ i) := by
    rw [inv_div, div_pow, pow_right_comm _ i 2, mul_pow, sq_sqrt (by positivity), mul_pow]
  calc ((S.M * √S.N) ^ i / w)⁻¹ ^ (2 * 𝔰.k) *
        ((2 * S.frameBoxRadius ^ 2) ^ ((i + 1) * i) * (2 ^ (i + 1) * θ ^ (2 * (j - i))) ^ 𝔰.k /
          (w ^ 2 / S.N ^ j.val * δ) ^ (𝔰.k + i))
    _ = ((2 * S.frameBoxRadius ^ 2) ^ (i + 1) * S.N ^ j.val / (w ^ 2 * δ)) ^ i *
        (2 ^ (i + 1) * θ ^ (2 * (j - 𝔰.ϱ)) * S.N ^ (j - 𝔰.ϱ) / ((S.M ^ 2) ^ i * δ)) ^ 𝔰.k := by
      rw [h_extra, pow_mul _ 2 𝔰.k, h_jacobian, pow_mul _ (i + 1), pow_add _ 𝔰.k, h_power]
      simp only [div_pow, mul_pow]
      field_simp
    _ ≤ ((2 * S.frameBoxRadius ^ 2) ^ (i + 1) * S.N ^ j.val / (1 ^ 2 * δ)) ^ i *
        ((S.b ^ 13) ^ i * S.N ^ (j - 𝔰.ϱ) / ((S.M ^ 2) ^ i * δ)) ^ 𝔰.k := by gcongr
    _ = _ := by ring

omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
lemma kernelBound_nonneg (hb : 0 ≤ S.b) (v : NumberField.InfinitePlace E) :
    0 ≤ S.kernelBound j γ v := by
  unfold kernelBound
  positivity

omit [HasPrimitiveRoot5040 E] in
/-- Let `γ` be a term of cell rank `j ≥ 1` over the block `(c, s, c')` and let `i = min ϱ j`. The
number `kernelBound j γ v` bounds the integral over `X₀ ^ i` of the kernel of Schur's test at the
place `v`. Its product over the `f` infinite places is at most
`tailScale * (b ^ 13 / M²) ^ (i k f) * minorNorm ^ (-k / 2)`, where `minorNorm` is the absolute norm
of the leading minor of order `j` of `S.frameProducts γ`, divided by `N ^ (2 f)` if `j = ϱ + 1`. -/
lemma prod_kernelBound_le (h_over : γ ∈ S.termsOver c s c') (h_rank : S.HasCellRank j γ)
    (hj : j ≠ 0) :
    ∏ v : NumberField.InfinitePlace E, S.kernelBound j γ v ≤
      S.tailScale * (S.b ^ 13 / S.M ^ 2) ^ (min 𝔰.ϱ j * 𝔰.k * numInfPlaces E) *
        (√(S.minorNorm j γ))⁻¹ ^ 𝔰.k := by
  have hb : 2 ≤ S.b := two_le_b
  have hN : 0 < S.N := S.N_prime.pos
  set P : ℝ := ∏ v, ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ with hP
  -- The minor is a nonzero integer of `E`.
  have h_one_le : 1 ≤ P := one_le_prod_norm_Φ (.det fun a b ↦ isIntegral_frameProducts h_over ..)
    h_rank.leadingMinor_ne_zero
  have h_sqrt : √(S.minorNorm j γ) = P / (S.N ^ (j - 𝔰.ϱ)) ^ numInfPlaces E := by
    rw [minorNorm, abs_norm_eq_prod_norm_sq, prod_pow, mul_assoc, pow_mul', ← div_pow,
      sqrt_sq (by positivity), pow_mul]
  have h_small : (((2 * S.frameBoxRadius ^ 2) ^ (min 𝔰.ϱ j + 1) * S.N ^ j.1) ^ numInfPlaces E / P) ^
      min 𝔰.ϱ j ≤ S.tailScale := by
    have h_exp : (37 * 𝔰.n * 2 + 1) * (min 𝔰.ϱ j + 1) + 60 * 𝔰.n * j ≤ 135 * 𝔰.n ^ 2 := by
      have h_min : min 𝔰.ϱ j + 1 ≤ 𝔰.n := Nat.succ_le_succ (min_le_left 𝔰.ϱ j)
      have h_le : j.val ≤ 𝔰.n := j.is_le
      have h_sq : 𝔰.n ≤ 𝔰.n ^ 2 := Nat.le_self_pow two_ne_zero 𝔰.n
      calc _ ≤ (37 * 𝔰.n * 2 + 1) * 𝔰.n + 60 * 𝔰.n * 𝔰.n := by gcongr
        _ = 134 * 𝔰.n ^ 2 + 𝔰.n := by ring
        _ ≤ 135 * 𝔰.n ^ 2 := by linarith
    -- Here `frameBoxRadius = b ^ (37 n)`, `2 ≤ b` and `N ≤ b ^ (60 n)`.
    have h_base : (2 * S.frameBoxRadius ^ 2) ^ (min 𝔰.ϱ j + 1) * S.N ^ j.val ≤
        S.b ^ (135 * 𝔰.n ^ 2) := by
      grw [frameBoxRadius, hb, N_le, ← pow_mul, ← pow_succ', ← pow_mul, ← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ S.one_le_b h_exp
    calc _ ≤ ((S.b ^ (135 * 𝔰.n ^ 2)) ^ numInfPlaces E) ^ min 𝔰.ϱ j := by
          grw [← h_one_le, div_one, h_base]
      _ ≤ S.b ^ (135 * 𝔰.n ^ 2 * numInfPlaces E * 𝔰.ϱ) := by
          rw [← pow_mul, ← pow_mul, ← mul_assoc]
          exact pow_le_pow_right₀ S.one_le_b (by grw [min_le_left])
      _ ≤ S.tailScale := pow_le_tailScale (by lia)
  calc ∏ v : InfinitePlace E, S.kernelBound j γ v
      ≤ ∏ v : InfinitePlace E, ((2 * S.frameBoxRadius ^ 2) ^ (min 𝔰.ϱ j + 1) * S.N ^ j.val /
            ‖Φ v (leadingMinor (S.frameProducts γ) j)‖) ^ min 𝔰.ϱ j *
          ((S.b ^ 13 / S.M ^ 2) ^ min 𝔰.ϱ j * S.N ^ (j - 𝔰.ϱ) /
            ‖Φ v (leadingMinor (S.frameProducts γ) j)‖) ^ 𝔰.k :=
        prod_le_prod₀ (fun v _ ↦ kernelBound_nonneg b_pos.le v) fun v _ ↦ kernelBound_le h_rank hj v
    _ = (((2 * S.frameBoxRadius ^ 2) ^ (min 𝔰.ϱ j + 1) * S.N ^ j.val) ^ numInfPlaces E / P) ^
          min 𝔰.ϱ j * (((S.b ^ 13 / S.M ^ 2) ^ min 𝔰.ϱ j * S.N ^ (j - 𝔰.ϱ)) ^
            numInfPlaces E / P) ^ 𝔰.k := by
        rw [prod_mul_distrib, prod_pow, prod_pow, Finset.prod_div_distrib, Finset.prod_div_distrib,
          Finset.prod_const, Finset.prod_const, card_univ]
    _ ≤ S.tailScale * (((S.b ^ 13 / S.M ^ 2) ^ min 𝔰.ϱ j * S.N ^ (j - 𝔰.ϱ)) ^
          numInfPlaces E / P) ^ 𝔰.k := by grw [h_small]
    _ = _ := by
        rw [h_sqrt, inv_div]
        ring

omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
/-- The sum of the weights `schurWeight` over the orbit of `γ` is left invariant under the
subgroup `classUnipotent₀ c`, which permutes the orbit and fixes the frame. -/
lemma tsum_schurWeight_ratToInf_mul {i : ℕ} {u : S.G E} (hu : u ∈ S.classUnipotent₀ c)
    (y : NumberField.InfinitePlace E → 𝔰.G₁) :
    ∑' p : doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'),
        S.schurWeight c' p i (S.ratToInf u * y) =
      ∑' p : doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'),
        S.schurWeight c' p i y := by
  set orbit : Set (S.G E) := doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c') with h_orbit
  have h_image : (fun p : S.G E ↦ u • p) '' orbit = orbit := by
    rw [Set.image_smul, h_orbit, doubleCoset, ← smul_mul_assoc, ← smul_mul_assoc, smul_coe_set hu]
  conv_lhs => rw [← h_image, tsum_image (S.schurWeight c' · _ _) (by simp)]
  simp [schurWeight, volumeRatio, frameVolume_mul_left, ratToInf_mem_besselU0 hu.2]

/-- **From the lattice to an integral.** Let `γ` have cell rank `j ≥ 1` (`HasCellRank`) and lie in
`termsOver c s c'`.

One factor `schurIntegral` of Schur's test (the integral of the box cutoff of `c` times the squared
norm of the cut Bessel function times `schurWeight`), summed over the orbit of `γ`, is at most
`unipotentCovolume * #BesselCoord` times `tailScale² (b ^ 13 / M²) ^ (i k f)
(isotropicRowsIndex / √minorNorm) ^ k`. Here `i = min ϱ j`, `k = |κ|` and `f` is the number of
infinite places. Let `Λ` be the lattice of `c` and `A` the span of the isotropic vectors `e_a`. Then
`isotropicRowsIndex` is the index, in the lattice of the rows of products of `Λ ∩ A` with the frame
of `translateByClassReps c c' γ = h_c⁻¹ γ h_c'`, of the part that comes from the `e_a` with
`a < j`. -/
lemma tsum_schurIntegral_le (h_over : γ ∈ S.termsOver c s c') (h_rank : S.HasCellRank j γ)
    (hj : j ≠ 0) :
    ∑' δ : doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'),
        S.schurIntegral c c' δ (min 𝔰.ϱ j) ≤
      .ofReal (S.unipotentCovolume * (card S.BesselCoord * S.tailScale ^ 2 *
        (S.b ^ 13 / S.M ^ 2) ^ (min 𝔰.ϱ j * 𝔰.k * numInfPlaces E) *
        (S.isotropicRowsIndex j (S.translateByClassReps c c' γ) / √(S.minorNorm j γ)) ^ 𝔰.k)) := by
  -- Integrate in stages, averaging over the shifts with parameter in a fundamental domain `D` of
  -- the lattice. On each of the `isotropicRowsIndex ^ k` cosets the mean of the sum of the weights
  -- is at most `tailScale` times the integral of the kernel divided by the volume of `D`, which is
  -- at least `1`.
  have hτ : 2 ≤ S.tailScale := two_le_tailScale
  have hV : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb : 0 < S.b := b_pos
  obtain ⟨D, -, hD, hD_vol, hD_finite⟩ :=
    S.exists_isAddFundamentalDomain_columnLattice (Fin (min 𝔰.ϱ j)) c
  set d : ℕ := min 𝔰.ϱ j * 𝔰.k * numInfPlaces E with hd
  set orbit : Set (S.G E) := doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c')
  set index : ℕ := S.isotropicRowsIndex j (S.translateByClassReps c c' γ)
  -- Instance search finds this only when it is asked directly.
  have : Measure.IsAddHaarMeasure
      (volume : Measure (NumberField.InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ)) := inferInstance
  let F (y : NumberField.InfinitePlace E → 𝔰.G₁) : ℝ≥0∞ :=
    ∑' p : orbit, S.schurWeight c' p (min 𝔰.ϱ j) y
  set C : ℝ≥0∞ :=
    .ofReal (index ^ 𝔰.k) * (.ofReal S.tailScale * ∏ v, .ofReal (S.kernelBound j γ v)) with hC
  have h_mean (u : NumberField.InfinitePlace E → 𝔰.G₁) (hu : ∀ v, u v ∈ besselU0)
      (y : NumberField.InfinitePlace E → 𝔰.G₁) (hy : y ∈ S.boxedPoints) :
      ∫⁻ x in D, F (u * S.eichlerShift j x * y) ≤ volume D * C := by
    refine le_trans ?_ (le_mul_of_one_le_left' hD_vol)
    rw [hC, lintegral_tsum fun _ ↦ Measurable.aemeasurable (by fun_prop)]
    refine tsum_orbit_le_of_isLatticeTranslate h_over h_rank
      (fun p ↦ ∫⁻ x in D, S.schurWeight c' p _ (u * S.eichlerShift j x * y)) _
      fun B hB p₀ hp₀ l hl ↦ ?_
    obtain ⟨φ, hφ_meas, hφ_int, hφ_le⟩ := exists_tsum_schurWeight_le hB hp₀ hl hu h_over h_rank hy
    have h_unfold : ∫⁻ x in D, ∑' w : S.columnLattice (Fin (min 𝔰.ϱ j)) c, φ (w +ᵥ x) =
        ∫⁻ x, φ x := by
      rw [hD.lintegral_eq_tsum'' φ, lintegral_tsum fun _ ↦ Measurable.aemeasurable (by fun_prop)]
    grw [← lintegral_tsum fun _ ↦ Measurable.aemeasurable (by fun_prop), lintegral_mono hφ_le,
      lintegral_const_mul' _ _ ofReal_ne_top, h_unfold, hφ_int]
  have h_inv (u : S.G E) (hu : u ∈ S.classUnipotent₀ c) (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      F (S.ratToInf u * y) = F y := tsum_schurWeight_ratToInf_mul hu y
  have h_pos : volume D ≠ 0 := (zero_lt_one.trans_le hD_vol).ne'
  calc
    _ = ∫⁻ y : NumberField.InfinitePlace E → 𝔰.G₁,
        S.boxCutoff c y * S.besselCutNormSq y * F y := by
      simp (disch := fun_prop) only [schurIntegral, ← lintegral_tsum, ENNReal.tsum_mul_left, F]
    _ ≤ C * (.ofReal S.unipotentCovolume * card S.BesselCoord) :=
      lintegral_boxCutoff_le_of_average c volume measurable_eichlerShift eichlerShift_mem
        (by fun_prop) h_inv D h_pos hD_finite h_mean
    _ ≤ .ofReal (index ^ 𝔰.k * (S.tailScale * (S.tailScale *
          (S.b ^ 13 / S.M ^ 2) ^ d * (√(S.minorNorm j γ))⁻¹ ^ 𝔰.k)) *
          (S.unipotentCovolume * card S.BesselCoord)) := by
      grw [hC, ← ofReal_prod_of_nonneg fun v _ ↦ kernelBound_nonneg hb.le v,
        prod_kernelBound_le h_over h_rank hj, ← ofReal_natCast]
      simp (disch := positivity) only [← ofReal_mul, ← hd, le_refl]
    _ = _ := by
      simp only [div_pow, inv_pow]
      congr 1
      field_simp

/-- **Schur's test.** Let `S` be admissible data over a CM field `E` with a primitive 5040th root of
unity, with size parameter `b`, `M = p₀ p₁` and `k = dim X₀`. Let `γ` have cell rank `j ≥ 1` and lie
over the block `(c, s, c')`. The square of the sum over its orbit of the absolute amplitudes, taken
with the cut Bessel functions `W♭` (`.cut`), is at most
`(V d τ² (b ^ 13 / M²) ^ (i k f))² (N ^ f / minorGauge) ^ k`.
Here `i = min ϱ j`, `V` is `unipotentCovolume`, the common covolume of the
unipotent groups of the classes, `d` is the number of Bessel coordinates, `τ = tailScale`, `f` is
the number of infinite places, and the gauge `minorGauge` is `N ^ f * minorNorm` divided by the two
indices `isotropicRowsIndex` of the term. -/
theorem sq_tsum_amplitudeMajorant_doubleCoset_le (h_over : γ ∈ S.termsOver c s c')
    (h_rank : S.HasCellRank j γ) (hj : j ≠ 0) :
    (∑' δ : doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'),
      S.amplitudeMajorant .cut c c' δ) ^ 2 ≤
      .ofReal ((S.unipotentCovolume * card S.BesselCoord * S.tailScale ^ 2 *
          (S.b ^ 13 / S.M ^ 2) ^ (min 𝔰.ϱ j * 𝔰.k * numInfPlaces E)) ^ 2 *
        (S.N ^ numInfPlaces E / S.minorGauge j c c' γ) ^ 𝔰.k) := by
  -- By Cauchy–Schwarz the square is at most the product of the sums of the two factors, for `γ`
  -- and for `γ⁻¹`.
  have hN : 0 < S.N := S.N_prime.pos
  have hV : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb : 0 < S.b := b_pos
  set orbit : Set (S.G E) := doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c') with h_orbit
  have h_schur : (∑' δ : orbit, S.amplitudeMajorant .cut c c' δ) ^ 2 ≤
      (∑' δ : orbit, S.schurIntegral c c' δ (min 𝔰.ϱ j)) *
        ∑' δ : orbit, S.schurIntegral c' c δ.val⁻¹ (min 𝔰.ϱ j) := by
    -- With every set measurable, a sum over the orbit is an integral for the counting measure.
    let : MeasurableSpace (S.G E) := ⊤
    simp only [← lintegral_count]
    exact sq_lintegral_le .of_discrete .of_discrete fun δ ↦ amplitudeMajorant_sq_le _
  -- Inversion maps the orbit of `γ` into that of `γ⁻¹`, which has the same cell rank and minor.
  have h_inverse : ∑' δ : orbit, S.schurIntegral c' c δ.val⁻¹ (min 𝔰.ϱ j) ≤
      ∑' δ : doubleCoset γ⁻¹ (S.classUnipotent₀ c') (S.classUnipotent₀ c),
        S.schurIntegral c' c δ (min 𝔰.ϱ j) := by
    rw [← tsum_image (S.schurIntegral c' c · (min 𝔰.ϱ j)) inv_injective.injOn]
    refine tsum_mono_subtype (S.schurIntegral c' c · (min 𝔰.ϱ j)) ?_
    simp [h_orbit, doubleCoset, mul_assoc, -Set.mul_singleton, -Set.singleton_mul]
  have h_translate_inv : S.translateByClassReps c' c γ⁻¹ = (S.translateByClassReps c c' γ)⁻¹ := by
    simp [translateByClassReps, mul_assoc]
  have h_ratio : S.N ^ numInfPlaces E / S.minorGauge j c c' γ =
      S.isotropicRowsIndex j (S.translateByClassReps c c' γ) / √(S.minorNorm j γ) *
        (S.isotropicRowsIndex j (S.translateByClassReps c c' γ)⁻¹ / √(S.minorNorm j γ)) := by
    rw [h_rank.minorGauge_eq, div_mul_div_comm, mul_self_sqrt h_rank.minorNorm_pos.le,
      div_div_eq_mul_div, mul_div_mul_left _ _ (by positivity)]
  grw [h_schur, h_inverse, tsum_schurIntegral_le h_over h_rank hj,
    tsum_schurIntegral_le (termsOver.inv h_over) h_rank.inv hj, minorNorm_inv, h_translate_inv,
    ← ofReal_mul (by positivity), h_ratio, mul_pow _ _ 𝔰.k]
  exact ofReal_le_ofReal (le_of_eq (by ring))

omit [HasPrimitiveRoot5040 E] in
/-- At cell rank `j ≥ 1`, the second moment `cellRankSecondMoment j` is at least `α ^ (8 - 32 i)`
times `identitySecondMoment`. Here `identitySecondMoment` is the order of the reduced image of the
Bessel subgroup `besselS` times the dimension `sourceDim` of the space of source forms, and
`cellRankSecondMoment j` is `mainSecondMoment` for `j = ϱ + 1` and `α ^ (-16)` times
`identitySecondMoment` for `j ≤ ϱ`. -/
lemma div_tailScale_pow_mul_identitySecondMoment_le_cellRankSecondMoment (hj : j ≠ 0) :
    S.tailScale ^ 8 / (S.tailScale ^ 32) ^ min 𝔰.ϱ j * S.identitySecondMoment ≤
      S.cellRankSecondMoment j := by
  have hτ : 1 ≤ S.tailScale := one_le_two.trans two_le_tailScale
  have h_id : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  unfold cellRankSecondMoment
  split_ifs with h_top
  · refine le_trans ?_ tailScale_pow_mul_identitySecondMoment_le
    grw [div_le_self (by positivity) (by bound)]
    gcongr
    lia
  · grw [← le_self_pow₀ (by bound)
      ((min_eq_right (not_lt.1 h_top)).trans_ne (val_ne_zero_iff.2 hj))]
    rw [show S.tailScale ^ 8 / S.tailScale ^ 32 * S.identitySecondMoment =
        S.identitySecondMoment / S.tailScale ^ 24 by field_simp]
    gcongr
    lia

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible] in
/-- The field `le_M` of `S` gives `S.b ^ 19 ≤ S.M`, so the factor `S.b ^ 13 / S.M²` is at most
`1 / (S.b ^ 4 S.M)`. -/
lemma b_pow_div_M_sq_le : S.b ^ 13 / (S.M : ℝ) ^ 2 ≤ (S.b ^ 4 * S.M)⁻¹ := by
  have hb_pos : 0 < S.b := b_pos
  have h_pow : S.b ^ 17 ≤ (S.M : ℝ) := (pow_le_pow_right₀ S.one_le_b (by norm_num)).trans S.le_M
  have hM_pos : 0 < (S.M : ℝ) := (pow_pos hb_pos 17).trans_le h_pow
  field_simp
  exact h_pow

/-- Let `γ` lie over the block `(c, s, c')` and have cell rank `j ≥ 1`, and let
`termDiscNorm γ ≤ N ^ f * minorNorm j γ`, so that `maxGauge` equals `minorGauge` at `γ`. Then the
absolute amplitudes of the terms of its orbit, taken with the cut Bessel functions `W♭` (`.cut`),
add up to at most `unipotentCovolume` times `orbitBound`, which is
`α² √(D_j / (n_p (M ^ (2 i f) x) ^ k))` at the gauge `x = maxGauge`. Here `i = min ϱ j`,
`k = dim X₀`, `D_j` is the second moment `cellRankSecondMoment j`, `n_p = pairCountScale` and
`α = tailScale`. -/
lemma tsum_amplitudeMajorant_orbit_le (h_over : γ ∈ S.termsOver c s c')
    (h_rank : S.HasCellRank j γ) (hj : j ≠ 0)
    (h_disc_le : S.termDiscNorm γ ≤ S.N ^ numInfPlaces E * S.minorNorm j γ) :
    ∑' δ : doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'),
      S.amplitudeMajorant .cut c c' δ ≤
      .ofReal (S.unipotentCovolume * S.orbitBound j (S.maxGauge j c c' γ)) := by
  classical
  have hτ : 2 ≤ S.tailScale := two_le_tailScale
  have h_identityMoment_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_rankMoment_nonneg : 0 ≤ S.cellRankSecondMoment j := cellRankSecondMoment_nonneg j
  have hV : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb_pos : 0 < S.b := b_pos
  have h_gauge : S.maxGauge j c c' γ = S.minorGauge j c c' γ := by
    rw [h_rank.maxGauge_eq, max_eq_right h_disc_le, h_rank.minorGauge_eq]
  have h_pos : 0 < S.minorGauge j c c' γ := (maxGauge_pos h_over h_rank).trans_eq h_gauge
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, orbitBound, ← ofReal_pow (by positivity)]
  refine (sq_tsum_amplitudeMajorant_doubleCoset_le h_over h_rank hj).trans (ofReal_le_ofReal ?_)
  -- One factor `card S.BesselCoord` is at most `b ^ (2 k f) = tailScale ^ 8`; the other is part
  -- of `identitySecondMoment`.
  have h_dim : (card S.BesselCoord : ℝ) ≤ S.tailScale ^ 8 := by
    grw [IsAdmissible.card_besselCoord_le, pow_mul _ 4 2, tailScale_pow_four]
    exact le_of_eq (by ring)
  have h_gain : (S.tailScale ^ 32) ^ min 𝔰.ϱ j =
      ((S.b ^ 4) ^ (min 𝔰.ϱ j * 𝔰.k * numInfPlaces E)) ^ 2 := by
    rw [pow_mul _ 4 8, tailScale_pow_four]
    ring
  rw [h_gauge, mul_pow S.unipotentCovolume, mul_pow (S.tailScale ^ 2), sq_sqrt (by positivity)]
  -- Insert the bounds for `b ^ 13 / M²`, the second moment and the number of coordinates. What is
  -- left is an identity, by the definitions of `identitySecondMoment` and `pairCountScale`.
  have h_moment_le : S.tailScale ^ 8 / (S.tailScale ^ 32) ^ min 𝔰.ϱ j * S.identitySecondMoment ≤
      S.cellRankSecondMoment j :=
    div_tailScale_pow_mul_identitySecondMoment_le_cellRankSecondMoment hj
  have h_ratio_le : S.b ^ 13 / (S.M : ℝ) ^ 2 ≤ (S.b ^ 4 * S.M)⁻¹ := b_pow_div_M_sq_le
  grw [h_ratio_le, ← h_moment_le, ← h_dim, h_gain]
  refine le_of_eq ?_
  simp only [identitySecondMoment, sourceDim, pairCountScale, Nat.cast_mul, div_pow, inv_pow,
    mul_inv, mul_pow]
  field

end New.Filling
end
end

/-!
# The orbit bound: a bound for a block of amplitudes; the second moment of a set of terms

Let `S : New.Filling E 𝔰` be filling data. The block `New.Filling.amplitudeSum S side T c s c'` is
the sum of the amplitudes of the rational elements of `T` that lie over the classes `c`, `c'` with
reduction `s` in `New.Filling.ResidueGL S`. The argument `side : New.FullOrCut` selects the full or
the cut Bessel functions. Write `ν` for `New.Filling.unipotentCovolume S`, the covolume of the
unipotent group of a class, `d₁` for `New.Filling.identitySecondMoment S` and `b` for the size
parameter `S.b ≥ 1`. The file defines the second moment of a family of blocks and proves that its
square root is subadditive. Its main result bounds the norm of a single block by ν times the sum of
the orbit bounds of the near orbits.

## Main definitions and results

* `New.Filling.secondMoment A Ω`: for a family of blocks `A c s c'`, the sum of the squared norms of
  the blocks with `s ∈ Ω`, divided by `ν²`.
* `New.Filling.secondMoment_sub_cut_le`: the second moment of the difference between the blocks of
  `U` and those for the cut functions is at most `b⁻⁴⁰` times `identitySecondMoment`.
* `New.Filling.enorm_integral_besselKernel_le`: the bound for one term on the open cell, from the
  bound `New.BesselSystem.enorm_integral_pairKernel_cut_le` for a family of real points.
* `New.Filling.enorm_amplitudeSum_le_orbitBound_top`: the bound for a block when
  `New.Filling.termDisc` vanishes nowhere on `T`; it rests on a change of weight
  (`New.Filling.hasSum_amplitudeSum_of_cutoff`) and the bound for one term.
* `New.Filling.enorm_amplitudeSum_le_orbitBound`: one bound for a stable set of terms of one cell
  rank `j` (`New.Filling.HasCellRank`), none of cell rank `0` over the block. Terms with large
  `New.Filling.termDiscNorm` use the open cell, the others are summed by
  `New.Filling.tsum_amplitudeMajorant_orbit_le`.
* `New.Filling.enorm_amplitudeSum_le_tsum_termSize`: a cut block of a stable subset of
  `New.Filling.remainingTerms` is at most `ν` times the sum of the sizes of its near
  representatives.

Notions from other files:
* `New.Filling.termsOver`: The rational γ such that h_c⁻¹ γ h_c' is integral and has reduction s,
  where h_c is the representative of the class c.
* `New.Filling.ResidueGL`: The finite group of reductions, a product of general linear groups over
  the residue fields at the chosen places.
* `New.Filling.termDisc`: The element 𝗀(γ) = |D_{ϱ+1}|² − N²|D_ϱ|² of E, formed from the last two
  leading minors of the matrix of products between the frame and its image under γ; N = S.N.
* `New.Filling.IsNear`: Some archimedean point y has both y and γ⁻¹ y among the boxed points;
  `New.Filling.IsNearRepresentative` says also that γ is the chosen element of its orbit.
* `New.Filling.IsAdmissible`: The standing hypotheses on the filling data, mostly size inequalities
  between its parameters.

## Relation to the literature

See `New.Spanning.RemainingTerms.Sum` for related work.
-/

@[expose] public section

/-!
## Second moment of a set of terms and transfer to cut Bessel functions

The second moment `New.Filling.secondMoment` sums the squared norms of the blocks, divided by `ν²`.
-/

section SecondMoment

open MeasureTheory ENNReal Finset

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {V : Type*}
  {S : Filling E 𝔰} [NormedAddCommGroup V]

open scoped Classical in
/-- The second moment 𝖤(A, Ω) of a family of blocks `A c s c'` in a normed group: ν⁻² times the sum
over classes c, c' and s ∈ Ω of the squared norm of `A c s c'`, with ν = `S.unipotentCovolume`. -/
noncomputable def secondMoment (A : S.Classes → S.ResidueGL → S.Classes → V) (Ω : Set S.ResidueGL) :
    ℝ :=
  ∑ c : S.Classes, ∑ c' : S.Classes, ∑ s : S.ResidueGL with s ∈ Ω,
    ‖A c s c'‖ ^ 2 / S.unipotentCovolume ^ 2

/-- The sum, over classes `c`, `c'`, reductions `s ∈ Ω` and submodules `Λ`, of the squared norm of
the block over `(c, s, c')` of the terms `γ` of `T` with `New.link γ = Λ`, for the cut Bessel
function. It takes values in `ℝ≥0∞` and, unlike `New.Filling.secondMoment`, is not divided by
`ν²`. -/
noncomputable def linkSecondMoment (T : Set (S.G E)) (Ω : Set S.ResidueGL) : ℝ≥0∞ :=
  ∑' (c : S.Classes) (c' : S.Classes) (s : Ω)
    (Λ : Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E)),
    ‖S.amplitudeSum .cut (T ∩ link ⁻¹' {Λ}) c s.val c'‖ₑ ^ 2

/-- The blocks (sums of amplitudes over two classes and a reduction) of a set `T` of rational
elements are the sums of the blocks of `T ∩ Uᶜ` and of `T ∩ U`. -/
lemma amplitudeSum_eq_inter_compl_add_inter [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (T U : Set (S.G E)) {side : FullOrCut} :
    S.amplitudeSum side T = S.amplitudeSum side (T ∩ Uᶜ) + S.amplitudeSum side (T ∩ U) := by
  funext c s c'
  have h_union : T ∩ S.termsOver c s c' =
      (T ∩ Uᶜ ∩ S.termsOver c s c') ∪ (T ∩ U ∩ S.termsOver c s c') := by grind
  simp only [Pi.add_apply, amplitudeSum, tsum_congr_set_coe _ h_union]
  exact (summable_amplitude ..).tsum_union_of_disjoint (by grind) (summable_amplitude ..)

lemma secondMoment_nonneg {A : S.Classes → S.ResidueGL → S.Classes → V} {Ω : Set S.ResidueGL} :
    0 ≤ secondMoment A Ω := by
  unfold secondMoment
  positivity

/-- Minkowski's inequality for the second moment: for families `A`, `B` of vectors `A c s c'` in
`V`, indexed by `S.Classes × S.ResidueGL × S.Classes`, `√(secondMoment (A + B) Ω) ≤ √(secondMoment A
Ω) + √(secondMoment B Ω)`. -/
lemma sqrt_secondMoment_add_le {A B : S.Classes → S.ResidueGL → S.Classes → V}
    {Ω : Set S.ResidueGL} :
    √(secondMoment (A + B) Ω) ≤ √(secondMoment A Ω) + √(secondMoment B Ω) := by
  classical
  -- The square root of the second moment is a multiple of the norm in an `ℓ²` space of blocks.
  let vec (A : S.Classes → S.ResidueGL → S.Classes → V) :
      PiLp 2 fun _ : S.Classes × S.Classes × Ω ↦ V :=
    WithLp.toLp 2 fun ⟨c, c', s⟩ ↦ A c s c'
  have h_norm (A : S.Classes → S.ResidueGL → S.Classes → V) :
      √(secondMoment A Ω) = ‖vec A‖ / S.unipotentCovolume := by
    rw [PiLp.norm_eq_of_L2, ← Real.sqrt_sq S.unipotentCovolume_pos.le,
      ← Real.sqrt_div' _ (sq_nonneg _)]
    simp [secondMoment, vec, Fintype.sum_prod_type, Finset.sum_div,
      sum_subtype (p := (· ∈ Ω)) (Finset.univ.filter (· ∈ Ω)) (by simp)]
  simp only [h_norm, ← add_div]
  exact div_le_div_of_nonneg_right (norm_add_le (vec A) (vec B)) S.unipotentCovolume_pos.le

/-- For a set `U` of rational elements and fixed `c`, `s`, consider the amplitude sums
`S.amplitudeSum .full U c s c'` and `S.amplitudeSum .cut U c s c'`. The norms of their differences
have sum over `c'` at most `ν b ^ (-k³ f) / 2`. Here `ν` is `S.unipotentCovolume`, `b = S.b` is the
size parameter, `k = 𝔰.k` and `f` is the number of infinite places of `E`. -/
lemma sum_norm_amplitudeSum_sub_cut_le [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (U : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) :
    ∑ c' : S.Classes, ‖S.amplitudeSum .full U c s c' - S.amplitudeSum .cut U c s c'‖ ≤
      S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * Core.numInfPlaces E))⁻¹ / 2 := by
  -- The amplitudes converge absolutely, and the integrals of the norm of the difference of the
  -- kernels, summed over `c'` and the terms, are small.
  have h_integrable (side : FullOrCut) (c' : S.Classes) (γ : ↥(U ∩ S.termsOver c s c')) :
      Integrable fun y ↦
        (S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y)).toReal •
          S.besselKernel side γ y :=
    integrable_toReal_smul (by fun_prop) (by fun_prop)
      ((le_tsum _ γ).trans_lt
        ((le_tsum _ c').trans_lt (tsum_amplitudeMajorant_lt_top U c s)))
  have h_block (c' : S.Classes) :
      ‖S.amplitudeSum .full U c s c' - S.amplitudeSum .cut U c s c'‖ₑ ≤
        ∑' γ : ↥(U ∩ S.termsOver c s c'),
          ∫⁻ y, S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y) *
            ‖S.besselKernel .full γ y - S.besselKernel .cut γ y‖ₑ := by
    simp only [amplitudeSum, ← Summable.tsum_sub, summable_amplitude]
    simp only [amplitude, ← integral_sub, h_integrable, ← smul_sub]
    grw [eNorm_tsum_le_tsum_eNorm, eNorm_integral_le_lintegral_eNorm, enorm_toReal_smul_le]
  have hν : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb : 1 ≤ S.b := S.one_le_b
  rw [← ofReal_le_ofReal_iff (by positivity), ofReal_sum_of_nonneg (by simp)]
  simp only [ofReal_norm]
  exact (Finset.sum_le_sum fun c' _ ↦ h_block c').trans
    (by simpa using tsum_lintegral_enorm_besselKernel_sub_cut_le (side := .full) U c s)

/-- The cardinality of `S.ResidueGL` times `S.b ^ 40` is at most `(S.b ^ (𝔰.k ^ 3 * f) * 2) ^ 2`,
where `f` is the number of infinite places of `E`. -/
lemma card_residueGL_mul_b_pow_le :
    (Fintype.card S.ResidueGL : ℝ) * S.b ^ 40 ≤
      (S.b ^ (𝔰.k ^ 3 * Core.numInfPlaces E) * 2) ^ 2 := by
  -- `ResidueGL` is a product over the chosen places of general linear groups of degree
  -- `r = 2 ϱ + k + 1` over fields with `levelPrime i` elements, so `|ResidueGL| ≤ M ^ (r² f)` with
  -- `M = levelPrime 0 * levelPrime 1 ≤ b ^ 23`; and `23 r² f + 40 ≤ 2 k³ f` as `k` is large.
  have hb : 1 ≤ S.b := S.one_le_b
  set k : ℕ := 𝔰.k
  set f : ℕ := numInfPlaces E
  have h_group : (Fintype.card S.ResidueGL : ℝ) ≤
      (((S.levelPrime 0 * S.levelPrime 1 : ℕ) : ℝ) ^ (2 * 𝔰.ϱ + k + 1) ^ 2) ^ f := by
    grw [Fintype.card_eq_nat_card, Nat.card_pi, Nat.card_pi.le, card_GL_le _]
    simp [card_resField_eq_levelPrime, S.card_chosenPlaces, ← mul_pow, -Nat.cast_mul, k, f, two_mul,
      add_assoc, add_comm, add_left_comm]
  have h_exp : 23 * (2 * 𝔰.ϱ + k + 1) ^ 2 * f + 40 ≤ k ^ 3 * f * 2 := by
    have hkf : k ≤ f := S.k_le_f
    obtain ⟨r, hr : 1000 * (2 * 𝔰.ϱ + 2) + r = k⟩ := S.thousand_mul_le_k.dest
    rw [← hr] at hkf ⊢
    lia
  calc
    _ ≤ ((S.b ^ 23) ^ (2 * 𝔰.ϱ + k + 1) ^ 2) ^ f * S.b ^ 40 := by grw [h_group, M_le_b_pow]
    _ = S.b ^ (23 * (2 * 𝔰.ϱ + k + 1) ^ 2 * f + 40) := by ring
    _ ≤ S.b ^ (k ^ 3 * f * 2) := by gcongr
    _ ≤ _ := by grw [pow_mul, ← le_mul_of_one_le_right (by positivity) one_le_two]

/-- For a set `U` of rational elements, passing from the Bessel function to its cut changes the
blocks over the reductions in `Ω` little: the sum over classes `c`, `c'` and `s ∈ Ω` of the squared
norms of the differences of the blocks, divided by the square of the covolume
`ν = S.unipotentCovolume`, is at most `b⁻⁴⁰` times `identitySecondMoment`. -/
lemma secondMoment_sub_cut_le [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (U : Set (S.G E)) {Ω : Set S.ResidueGL} :
    secondMoment (S.amplitudeSum .full U - S.amplitudeSum .cut U) Ω ≤
      (S.b ^ 40)⁻¹ * S.identitySecondMoment := by
  have hν : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb : 1 ≤ S.b := S.one_le_b
  set η : ℝ := S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2 with hη
  -- Bound each row's sum of squares by the square of its sum, then count classes and reductions.
  calc
    _ ≤ (∑ c, ∑ s, ∑ c', ‖S.amplitudeSum .full U c s c' - S.amplitudeSum .cut U c s c'‖ ^ 2) /
        S.unipotentCovolume ^ 2 := by
      grw [secondMoment, filter_subset]
      simp [Finset.sum_div, Finset.sum_comm (s := (Finset.univ : Finset S.ResidueGL))]
    _ ≤ (∑ c : S.Classes, ∑ s : S.ResidueGL, η ^ 2) / S.unipotentCovolume ^ 2 := by
      gcongr with c _ s
      grw [sum_sq_le_sq_sum_of_nonneg (by simp), sum_norm_amplitudeSum_sub_cut_le U c s]
    _ ≤ (S.b ^ 40)⁻¹ * S.identitySecondMoment := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
      grw [(le_div_iff₀ (by positivity)).2 card_residueGL_mul_b_pow_le, identitySecondMoment,
        sourceDim, ← Nat.card_pos.succ_le, ← le_mul_of_one_le_right' NeZero.one_le]
      simp [hη, field]

end New.Filling

end SecondMoment

/-!
## Bound for a block of amplitudes of a stable set

The norm of a block is bounded under `New.Filling.IsAdmissible`, for the cut Bessel functions
(`New.FullOrCut.cut`) and a set `T` stable under the unipotent group on both sides
(`New.Filling.IsStable`).
-/

section SizeOfBlocks

open DoubleCoset MeasureTheory Matrix Finset Set ENNReal

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} {T : Set (S.G E)}

/-- Let `p γ = γ w` with `p` in `U⁰_c` (the elements of the unipotent group `U_c` of the class `c`
that fix the frame) and `w` in `U_c'`. If `𝗀(γ) = S.termDisc γ`, formed from the last two leading
minors of the frame products of `γ`, is nonzero, then `w = 1`. Hence `p = 1`: the stabilizer in
`U⁰_c` of the coset `γ U_c'` is trivial. -/
lemma eq_one_of_mul_eq_mul_of_termDisc_ne_zero {c c' : S.Classes} {γ w p : S.G E}
    (hγ : S.termDisc γ ≠ 0) (hp : p ∈ S.classUnipotent₀ c) (hw : w ∈ S.classUnipotent c')
    (h_eq : p * γ = γ * w) : w = 1 := by
  -- As `p` fixes the frame, `w` fixes the frame of `δ = γ⁻¹`, whose matrix of products with the
  -- standard frame is invertible. So `w` fixes vectors `B` whose dual coordinates form the
  -- identity matrix.
  obtain ⟨hw_unip, -⟩ := hw
  have h_conj : w * γ⁻¹ = γ⁻¹ * p := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h_eq, mul_inv_cancel_right]
  have h_det : (S.frameProducts γ⁻¹).det ≠ 0 := by
    rw [frameProducts, frameGram_inv, det_conjTranspose, star_ne_zero]
    exact ((termDisc_pos_or_eq_zero γ).resolve_right hγ).2
  generalize γ⁻¹ = δ at h_conj h_det
  let toMatrix (g : S.G E) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E := g.val.val
  have h_fix : toMatrix w * frameImage (toMatrix δ) = frameImage (toMatrix δ) := by
    refine frameImage_mul.symm.trans ?_
    rw [h_conj]
    exact frameImage_mul_of_mem_besselU0 hp.2
  have h_inv : (S.frameProducts δ * (S.frameProducts δ)⁻¹).submatrix
      (Fin.castSucc : Fin 𝔰.ϱ → Fin (𝔰.ϱ + 1)) Fin.castSucc = 1 := by
    rw [mul_nonsing_inv _ h_det.isUnit, submatrix_one _ (Fin.castSucc_injective _)]
  apply eq_one_of_mem_besselU_of_fix
    (B := frameImage (toMatrix δ) * (S.frameProducts δ)⁻¹.submatrix id .castSucc) hw_unip
  · rw [← Matrix.mul_assoc, h_fix]
  · simpa [toMatrix, frameGram, splitGram, ← Matrix.ext_iff, Matrix.mul_apply, Matrix.one_apply]
      using h_inv

open scoped Classical in
/-- Let `ρ` choose a representative in each double coset of `U⁰_c = S.classUnipotent₀ c` and
`U_c' = S.classUnipotent c'`, and let `γ` have `S.termDisc γ ≠ 0`. Then exactly one pair `(a, b)` in
these groups carries `γ` to the representative `a γ b⁻¹` of its double coset; this is written as a
sum of indicators equal to 1. -/
lemma tsum_ite_representative_eq_one {c c' : S.Classes}
    {ρ : DoubleCoset.Quotient (S.classUnipotent₀ c) (S.classUnipotent c') → S.G E}
    (hρ : ∀ q : DoubleCoset.Quotient (S.classUnipotent₀ c : Set (S.G E))
      (S.classUnipotent c' : Set (S.G E)),
      DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') (ρ q) = q) {γ : S.G E}
    (hγ : S.termDisc γ ≠ 0) :
    ∑' (a : (S.classUnipotent₀ c).subgroupOf (S.classUnipotent c)) (b : S.classUnipotent c'),
      (if ρ ⟦(a : S.classUnipotent c) * γ * (b : S.G E)⁻¹⟧ =
          (a : S.classUnipotent c) * γ * (b : S.G E)⁻¹ then (1 : ℝ≥0∞) else 0) = 1 := by
  obtain ⟨u, hu, u', hu', h_rep⟩ : ∃ u ∈ S.classUnipotent₀ c, ∃ u' ∈ S.classUnipotent c',
      ρ (DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') γ) = u * γ * u' :=
    (DoubleCoset.eq ..).mp (hρ _).symm
  have rep_eq (a : (S.classUnipotent₀ c).subgroupOf (S.classUnipotent c))
      (b : S.classUnipotent c') :
      ρ ⟦(a : S.classUnipotent c) * γ * (b : S.G E)⁻¹⟧ = u * γ * u' := by
    have h_same : DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') γ =
        DoubleCoset.mk _ _ ((a : S.classUnipotent c) * γ * (b : S.G E)⁻¹) :=
      (DoubleCoset.eq ..).mpr ⟨_, a.prop, _, b⁻¹.prop, rfl⟩
    exact (congrArg ρ h_same.symm).trans h_rep
  simp_rw [rep_eq, ← tsum_prod]
  let a₀ : (S.classUnipotent₀ c).subgroupOf (S.classUnipotent c) := ⟨⟨u, hu.1⟩, hu⟩
  rw [tsum_eq_single (a₀, (⟨u', hu'⟩ : S.classUnipotent c')⁻¹) ?_]
  · simp [a₀]
  rintro ⟨a, b⟩ h_ne
  refine ite_eq_right fun h_eq ↦ h_ne ?_
  have h_conj : u⁻¹ * (a : S.classUnipotent c) * γ = γ * (u' * b) := by
    -- Multiply the equation of the representatives by `u⁻¹` on the left and by `b` on the right.
    simpa [mul_assoc] using congrArg (fun g : S.G E ↦ u⁻¹ * g * (b : S.G E)) h_eq.symm
  have hw : u' * b = 1 :=
    eq_one_of_mul_eq_mul_of_termDisc_ne_zero hγ (mul_mem (inv_mem hu) a.prop)
      (mul_mem hu' b.prop) h_conj
  rw [hw, mul_one, mul_eq_right, inv_mul_eq_one] at h_conj
  exact Prod.ext (Subtype.ext (Subtype.ext h_conj.symm))
    (Subtype.ext (eq_inv_of_mul_eq_one_right hw))

variable [S.IsAdmissible]

/-- **Open cell.** Let `W` be the cut Bessel vector on the archimedean points, so that the kernel
`S.besselKernel .cut γ y` is the tensor `W(y) ⊗ W(γ⁻¹ y)^*`; with `.full` the uncut vector is meant.
A point `y` lies in the cut at the place `v` (`InCut`) if its size `besselLength` is at most
`b ^ (6 n + 2)`, where `b = S.b` is the size parameter and `n = ϱ + 1`. It lies in the box
(`frameBox`) if it moves the frame to vectors `y⁻¹ f_a` of norm at most `ρ = S.frameBoxRadius`. Let
`γ` be near, that is, some `y` has `y` and `γ⁻¹ y` both reduced (`reducedPoints`) and in the cut at
every place, and let `𝗀(γ) = S.termDisc γ ≠ 0`. Let the weight `ω ≤ 1` be measurable, left invariant
under the fixer of the frame, and zero at the points that at some place lie in the cut but not in
the box. Let `ε²` bound the product over `v` of the numbers `pairingBoundSq`: explicit bounds for
the squared local pairing, in terms of the local value of `𝗀`, the radius `ρ`, and the degree and
the dimension of the Bessel system `S.besselSystem v`. Then the integral of `ω` times the cut kernel
has norm at most `ε` plus the integral of `ω` times the norm of the difference of the full and the
cut kernel. -/
theorem enorm_integral_besselKernel_le {γ : S.G E} (h_near : S.IsNear γ)
    (h_disc : S.termDisc γ ≠ 0) {ω : (NumberField.InfinitePlace E → 𝔰.G₁) → ℝ≥0∞}
    (ω_meas : Measurable ω) (ω_le : ∀ y : NumberField.InfinitePlace E → 𝔰.G₁, ω y ≤ 1)
    (ω_inv : ∀ t y : NumberField.InfinitePlace E → 𝔰.G₁,
      (∀ v : NumberField.InfinitePlace E, t v ∈ besselFixer) → ω (t * y) = ω y)
    (ω_box : ∀ (y : NumberField.InfinitePlace E → 𝔰.G₁) (v : NumberField.InfinitePlace E),
      ω y ≠ 0 → InCut (y v) S.b → y v ∈ frameBox S.frameBoxRadius)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h_pairingBound : ∏ v : NumberField.InfinitePlace E,
      pairingBoundSq (S.ratToInf γ v) (S.besselSystem v).deg
      S.frameBoxRadius (Fintype.card (S.besselSystem v).Index) ≤ ε ^ 2) :
    ‖∫ y : NumberField.InfinitePlace E → 𝔰.G₁, (ω y).toReal • S.besselKernel .cut γ y‖ₑ ≤
      .ofReal ε +
      ∫⁻ y : NumberField.InfinitePlace E → 𝔰.G₁,
        ω y * ‖S.besselKernel .full γ y - S.besselKernel .cut γ y‖ₑ := by
  obtain ⟨y₀, y₀_boxed, γy₀_boxed⟩ :
      ∃ y₀ ∈ S.boxedPoints, (S.ratToInf γ)⁻¹ * y₀ ∈ S.boxedPoints := h_near
  have h_kernel (σ : FullOrCut) (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      S.besselKernel σ γ y = BesselSystem.pairKernel S.besselSystem σ (S.ratToInf γ) y := by
    ext
    simp [besselKernel, besselFn, BesselSystem.pairKernel, prod_mul_distrib]
  have h_pos (v : NumberField.InfinitePlace E) :
      0 < RealPlace.gramDiscReal (realFrameGram (S.ratToInf γ v)) := by
    simp [gramDiscReal_realFrameGram_ratToInf, prod_pos, h_disc]
  have h_radius (_ : NumberField.InfinitePlace E) : S.b ^ (6 * 𝔰.n + 2) ≤ S.frameBoxRadius :=
    pow_right_mono₀ S.one_le_b (by nlinarith [S.ten_pow_five_le_varrho])
  -- Apply the bound for one pairing to the weight `φ`, which is `ω` with complex values.
  let φ (z : NumberField.InfinitePlace E → 𝔰.G₁) : ℂ := (ω z).toReal
  have φ_meas : Measurable φ := by fun_prop
  have φ_le (z : NumberField.InfinitePlace E → 𝔰.G₁) : ‖φ z‖ ≤ 1 := by
    simp [φ, toReal_le_of_le_ofReal, ω_le]
  have φ_enorm_le (z : NumberField.InfinitePlace E → 𝔰.G₁) : ‖φ z‖ₑ ≤ ω z := by
    simpa [φ, ← ofReal_norm] using ofReal_toReal_le
  have φ_inv (t z : NumberField.InfinitePlace E → 𝔰.G₁)
      (ht : ∀ v : NumberField.InfinitePlace E, t v ∈ besselFixer) : φ (t * z) = φ z := by
    simp only [φ, ω_inv t z ht]
  have φ_box (z : NumberField.InfinitePlace E → 𝔰.G₁)
      (hz : φ z • BesselSystem.pairKernel S.besselSystem .cut (S.ratToInf γ) z ≠ 0)
      (v : NumberField.InfinitePlace E) : z v ∈ frameBox S.frameBoxRadius := by
    have hω_ne : ω z ≠ 0 := fun h_zero ↦ hz (by simp [φ, h_zero])
    have h_kernel_ne : S.besselKernel .cut γ z ≠ 0 := by
      rw [h_kernel]
      exact right_ne_zero_of_smul hz
    obtain ⟨h_cut, -⟩ := inCut_of_besselKernel_ne_zero h_kernel_ne v
    exact ω_box z v hω_ne h_cut
  obtain ⟨-, h_integral_le⟩ := BesselSystem.enorm_integral_pairKernel_cut_le S.besselSystem h_pos
    (mem_frameBox_of_mem_boxedPoints y₀_boxed) (mem_frameBox_of_mem_boxedPoints γy₀_boxed)
    h_radius φ_meas φ_le φ_inv φ_box
  have h_sqrt_le : √(∏ v : NumberField.InfinitePlace E,
      pairingBoundSq (S.ratToInf γ v) (S.besselSystem v).deg
        S.frameBoxRadius (Fintype.card (S.besselSystem v).Index)) ≤ ε :=
    Real.sqrt_le_iff.2 ⟨hε, h_pairingBound⟩
  simp only [h_kernel, ← Complex.coe_smul]
  refine h_integral_le.trans ?_
  gcongr with z
  exact φ_enorm_le z

/-- Let `U_c` be the unipotent group of the class `c` and `U⁰_c` its subgroup fixing the frame. An
archimedean point `y` is reduced if the entries above the diagonal of the matrix `S.ratTriangle y`
lie in a fixed set of representatives modulo `M 𝓞_E`, and boxed if moreover its size `besselLength`
is at most `b ^ (6 n + 2)` at every infinite place. If the cut Bessel kernel `W(y) ⊗ W(γ⁻¹ y)^*` of
`γ` is nonzero at a reduced point `y`, then the double coset `U⁰_c γ U_c'` contains an element `δ`
that is near and is the chosen element of its smaller double coset `U⁰_c δ U⁰_c'`. -/
lemma exists_isNearRepresentative_of_besselKernel_ne_zero [HasPrimitiveRoot5040 E]
    {c c' : S.Classes} {γ : S.G E}
    {y : NumberField.InfinitePlace E → 𝔰.G₁} (hy : S.besselKernel .cut γ y ≠ 0)
    (h_reduced : S.reducedIndicator y ≠ 0) :
    ∃ δ : S.G E, S.IsNearRepresentative c c' δ ∧
      DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') δ =
        DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') γ := by
  -- Translate `γ⁻¹ y` into the boxed points by `u ∈ U_c'` and take the chosen element of the orbit
  -- of `γ u⁻¹`.
  have h_cut (v : NumberField.InfinitePlace E) :
      InCut (y v) S.b ∧ InCut (((S.ratToInf γ)⁻¹ * y) v) S.b :=
    inCut_of_besselKernel_ne_zero hy v
  obtain ⟨u, hu, u_box⟩ : ∃ u ∈ S.classUnipotent c',
      S.ratToInf u * ((S.ratToInf γ)⁻¹ * y) ∈ S.boxedPoints :=
    exists_classUnipotent_mul_mem_boxedPoints c' fun v ↦ (h_cut v).2
  have h_near : S.IsNear (γ * u⁻¹) :=
    ⟨y, mem_boxedPoints_of_reducedIndicator_ne_zero h_reduced fun v ↦ (h_cut v).1,
      by simpa [mul_assoc] using u_box⟩
  obtain ⟨a, ha, b, ⟨hb_unip, hb_fix⟩, out_eq⟩ : ∃ a ∈ S.classUnipotent₀ c,
      ∃ b ∈ S.classUnipotent₀ c', (DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent₀ c')
        (γ * u⁻¹)).out = a * (γ * u⁻¹) * b :=
    (DoubleCoset.eq ..).1 (DoubleCoset.out_eq' ..).symm
  refine ⟨a * (γ * u⁻¹) * b,
    ⟨h_near.mul_of_mem_besselU0 ha.2 hb_fix, by simp [← out_eq]⟩, ?_⟩
  exact ((DoubleCoset.eq ..).2 ⟨a, ha, u⁻¹ * b, mul_mem (inv_mem hu) hb_unip, by group⟩).symm

omit [S.IsAdmissible] in
/-- The element `𝗀(γ) = |D_{ϱ+1}|² - N² |D_ϱ|²` (`termDisc γ`), formed from the last two leading
minors of the matrix of frame products, is an algebraic integer for a rational `γ` in
`S.termsOver c s c'`. -/
lemma isIntegral_termDisc {c c' : S.Classes} {s : S.ResidueGL} {γ : S.G E}
    (hγ : γ ∈ S.termsOver c s c') : IsIntegral ℤ (S.termDisc γ) := by
  have h_entries : ∀ i k, IsIntegral ℤ (S.frameProducts γ i k) := isIntegral_frameProducts hγ
  have h_det : IsIntegral ℤ (S.frameProducts γ).det := IsIntegral.det h_entries
  have h_minor : IsIntegral ℤ (leadingMinor (S.frameProducts γ) 𝔰.top.castSucc) :=
    IsIntegral.det fun i k ↦ h_entries _ _
  exact (h_det.mul (map_isIntegral_int (starRingEnd E) h_det)).sub
    (((isIntegral_natCast ..).pow 2).mul (h_minor.mul (map_isIntegral_int (starRingEnd E) h_minor)))

/-- If no element `δ` of the double coset `U⁰_c γ U_c'` is near and the chosen element of
`U⁰_c δ U⁰_c'` (`IsNearRepresentative`), then the cut Bessel kernel of `γ` is zero at every reduced
point `y`, that is, wherever `S.reducedIndicator y ≠ 0`. -/
lemma toReal_smul_besselKernel_eq_zero [HasPrimitiveRoot5040 E] {c c' : S.Classes} {γ : S.G E}
    (h_none : ∀ δ : S.G E, S.IsNearRepresentative c c' δ →
      DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') δ ≠
        DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') γ)
    (y : NumberField.InfinitePlace E → 𝔰.G₁) :
    (S.reducedIndicator y).toReal • S.besselKernel .cut γ y = 0 := by
  by_contra hy
  have h_kernel : S.besselKernel .cut γ y ≠ 0 := right_ne_zero_of_smul hy
  obtain ⟨δ, hδ, h_same⟩ := exists_isNearRepresentative_of_besselKernel_ne_zero (c := c) (c' := c')
    h_kernel fun h_zero ↦ hy (by simp [h_zero])
  exact h_none δ hδ h_same

open scoped Classical in
omit [S.IsAdmissible] in
/-- Let `T` be a set of rational elements with `𝗀 = termDisc ≠ 0` that is stable under the rational
unipotent group on both sides, and let `ρ` choose a representative in each double coset
`U⁰_c γ U_c'`, where `U_c = S.classUnipotent c` and `U⁰_c` is its subgroup fixing the frame. Let
`ω` be a partition of unity in boxes for `U_c` modulo `U⁰_c`; the property used is that
`∑ x ∈ U_c, a x * ω (x y) = 1` for every weight `a` whose sum over each coset `U⁰_c x` is one. Then
for `γ ∈ T` the sum of `ω (u y)` over the pairs `(u, u')` in `U_c × U_c'` for which `u γ u'⁻¹` is
the representative of its double coset equals one. -/
lemma tsum_representative_weight_eq_one {c c' : S.Classes}
    {ρ : DoubleCoset.Quotient (S.classUnipotent₀ c) (S.classUnipotent c') → S.G E}
    (hρ : ∀ q : DoubleCoset.Quotient (G := S.G E) (S.classUnipotent₀ c) (S.classUnipotent c'),
      DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') (ρ q) = q)
    {ω : (NumberField.InfinitePlace E → 𝔰.G₁) → ℝ≥0∞} (hω : S.IsBoxPartitionOfUnity c ω)
    (hT : S.IsStable T) (h_disc : ∀ γ ∈ T, S.termDisc γ ≠ 0) {γ : S.G E} (hγ : γ ∈ T)
    (y : NumberField.InfinitePlace E → 𝔰.G₁) :
    ∑' u : S.classUnipotent c × S.classUnipotent c',
      (if ρ ⟦u.1 * γ * u.2⁻¹⟧ = u.1 * γ * u.2⁻¹ then 1 else 0) *
        ω (S.ratToInf u.1 * y) = 1 := by
  let repIndicator (g : S.G E) : ℝ≥0∞ := if ρ ⟦g⟧ = g then 1 else 0
  let repCount (x : S.classUnipotent c) : ℝ≥0∞ :=
    ∑' u : S.classUnipotent c', repIndicator (x * γ * (u : S.G E)⁻¹)
  -- The sum of `repCount` over each coset of `U⁰_c` is one, so the partition property applies.
  have h_coset (x : S.classUnipotent c) :
      ∑' b : (S.classUnipotent₀ c).subgroupOf (S.classUnipotent c), repCount (b.val * x) = 1 := by
    have h_mem : x * γ ∈ T := by simpa using (hT _ (inv_mem x.prop).1 1 (one_mem _) γ).2 hγ
    simpa [repCount, repIndicator, mul_assoc] using
      tsum_ite_representative_eq_one hρ (h_disc _ h_mem)
  have h_sum : ∑' x : S.classUnipotent c, repCount x * ω (S.ratToInf x * y) = 1 :=
    hω.tsum_mul_eq_one _ repCount h_coset
  rw [tsum_prod']
  simpa [repCount, repIndicator, ← ENNReal.tsum_mul_right] using h_sum

variable [HasPrimitiveRoot5040 E]

open scoped Classical in
/-- The bound for a block through the open cell. Let `T` be a set of rational elements, invariant
under the rational unipotent group on both sides, on which `𝗀 = termDisc` does not vanish. The terms
over `(c, s, c')` are the `γ` with `h_c⁻¹ γ h_c'` integral and of reduction `s`, and the cut block
`amplitudeSum` is the sum of their amplitudes, the integrals of the cut Bessel kernel against the
cutoffs of `c` and `c'`. Its norm is at most the covolume `ν = unipotentCovolume` times a sum over
the terms `γ` that are near and are the chosen element of their double coset `U⁰_c γ U⁰_c'`, with
`U⁰_c` the group of the unipotent elements of the class `c` fixing the frame. The summand is
`orbitBound j x`, an explicit constant times `x ^ (-k / 2)`, at the top rank `j = ⊤ = ϱ + 1` and at
`x = termDiscNorm γ`, the product of the `|𝗀(γ)|_v` over the infinite places. -/
lemma enorm_amplitudeSum_le_orbitBound_top (hT : S.IsStable T)
    (h_disc : ∀ γ ∈ T, S.termDisc γ ≠ 0) (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) :
    ‖S.amplitudeSum .cut T c s c'‖ₑ ≤ ∑' γ : ↥(T ∩ S.termsOver c s c'),
      if S.IsNearRepresentative c c' γ then
        ENNReal.ofReal (S.unipotentCovolume * S.orbitBound ⊤ (S.termDiscNorm γ))
      else 0 := by
  -- Unfold so that one term `γ` of each double coset `U⁰_c γ U_c'` contributes, with the weight
  -- `ω y`, the indicator of the reduced points. The open cell bounds its integral.
  let ω : (NumberField.InfinitePlace E → 𝔰.G₁) → ℝ≥0∞ := S.reducedIndicator
  have hω_partition : S.IsBoxPartitionOfUnity c ω := isBoxPartitionOfUnity_reducedIndicator c
  have ω_box (y : NumberField.InfinitePlace E → 𝔰.G₁) (v : NumberField.InfinitePlace E)
      (hy : ω y ≠ 0) (h_cut : InCut (y v) S.b) : y v ∈ frameBox S.frameBoxRadius := by
    simpa only [mul_one] using
      hω_partition.mem_frameBox hy zero_le_one (h_cut.trans_eq (mul_one _).symm)
  -- In each double coset choose a representative, one with `IsNearRepresentative` if there is one.
  choose ρ hρ using fun q : DoubleCoset.Quotient (G := S.G E) (S.classUnipotent₀ c)
    (S.classUnipotent c') ↦
    exists_maximalFor_of_wellFoundedGT (fun γ : S.G E ↦
      DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') γ = q)
        (S.IsNearRepresentative c c') q.exists_rep
  let repIndicator (γ : S.G E) : ℝ≥0∞ := if ρ ⟦γ⟧ = γ then 1 else 0
  let φ (γ : S.G E) (y : NumberField.InfinitePlace E → 𝔰.G₁) : ℝ≥0∞ := repIndicator γ * ω y
  have φ_sum (γ : S.G E) (hγ : γ ∈ T ∩ S.termsOver c s c')
      (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      ∑' u : S.classUnipotent c × S.classUnipotent c',
        φ (u.1 * γ * u.2⁻¹) (S.ratToInf u.1 * y) = 1 :=
    tsum_representative_weight_eq_one (fun q ↦ (hρ q).1) hω_partition hT h_disc hγ.1 y
  obtain ⟨ω_meas, -, -, ω_le, ω_inv⟩ := hω_partition
  have h_cut_sum : HasSum (fun γ : ↥(T ∩ S.termsOver c s c') ↦
      ∫ y, (φ γ y).toReal • S.besselKernel .cut γ y) (S.amplitudeSum .cut T c s c') :=
    (hasSum_amplitudeSum_of_cutoff hT c s c' φ φ_sum (by fun_prop)).1
  have h_tail : ∑' γ : ↥(T ∩ S.termsOver c s c'), ∫⁻ y,
        φ γ y * ‖S.besselKernel .full γ y - S.besselKernel .cut γ y‖ₑ ≤
      ENNReal.ofReal (S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) :=
    (hasSum_amplitudeSum_of_cutoff (side := .full) hT c s c' φ φ_sum (by fun_prop)).2.2
  grw [← h_cut_sum.tsum_eq, eNorm_tsum_le_tsum_eNorm]
  gcongr with γ
  obtain ⟨hγT, hγ_over⟩ := γ.property
  by_cases! h_rep : ρ ⟦γ⟧ ≠ γ
  · simp [φ, repIndicator, h_rep]
  -- Replace the weight by `ω y`, as `γ` is the representative.
  have φ_eq (y : NumberField.InfinitePlace E → 𝔰.G₁) : φ γ y = ω y := by
    simp [φ, repIndicator, h_rep]
  simp only [φ_eq]
  split_ifs with h_nearRep
  · -- `𝗀(γ)` is a nonzero algebraic integer, so its norm is at least `1`. The pairing bound and the
    -- cost of removing the cut are each at most half of the covolume times the orbit bound.
    have hν : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
    obtain ⟨h_near, -⟩ := h_nearRep
    set ε : ℝ := S.unipotentCovolume * S.orbitBound ⊤ (S.termDiscNorm γ) / 2 with h_eps
    have h_one_le : 1 ≤ S.termDiscNorm γ :=
      one_le_prod_norm_Φ (isIntegral_termDisc hγ_over) (h_disc γ hγT)
    have hε : 0 ≤ ε := by simp only [h_eps, orbitBound]; positivity
    calc
      _ ≤ .ofReal ε + ∫⁻ y, ω y * ‖S.besselKernel .full γ y - S.besselKernel .cut γ y‖ₑ :=
        enorm_integral_besselKernel_le h_near (h_disc γ hγT) ω_meas ω_le ω_inv ω_box hε
          (prod_pairingBoundSq_le h_one_le)
      _ ≤ .ofReal ε + .ofReal (S.unipotentCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) := by
        gcongr
        simpa only [φ_eq] using (le_tsum _ γ).trans h_tail
      _ ≤ .ofReal ε + .ofReal ε := by grw [h_near.inv_pow_le_orbitBound h_one_le]
      _ = _ := by rw [← ofReal_add hε hε, add_halves]
  · -- The representative `γ` is maximal for `IsNearRepresentative` in its double coset and fails
    -- it, so no element of the double coset satisfies it, and the integrand vanishes.
    obtain ⟨-, h_maximal⟩ := hρ ⟦γ⟧
    have h_none (δ : S.G E) (hδ : S.IsNearRepresentative c c' δ) :
        DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent c') δ ≠ DoubleCoset.mk _ _ γ.val :=
      fun h_same ↦ h_nearRep (by simpa [h_rep] using h_maximal h_same (fun _ ↦ hδ) hδ)
    simp [ω, toReal_smul_besselKernel_eq_zero h_none]

/-- If the majorant `S.amplitudeMajorant .cut c c' γ` of the amplitude of `γ` over the classes `c`,
`c'` is nonzero, then `γ` is near (`S.IsNear γ`): some archimedean point `y` has both `y` and
`γ⁻¹ y` in `S.boxedPoints`. -/
lemma isNear_of_amplitudeMajorant_ne_zero {c c' : S.Classes} {γ : S.G E}
    (hγ : S.amplitudeMajorant .cut c c' γ ≠ 0) : S.IsNear γ := by
  by_contra h_far
  -- If `γ` is not near, the boxed cutoffs at `y` and at `γ⁻¹ y` are never both nonzero, so the
  -- first factor in the bound of Schur's test vanishes.
  have h_cutoff (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      S.boxCutoff c y = 0 ∨ S.boxCutoff c' ((S.ratToInf γ)⁻¹ * y) = 0 := by
    by_contra! ⟨hy, hγy⟩
    exact h_far ⟨y, mem_of_indicator_ne_zero hy, mem_of_indicator_ne_zero hγy⟩
  have h_integral : S.schurIntegral c c' γ 0 = 0 := by
    rw [schurIntegral, ← lintegral_zero]
    refine lintegral_congr fun y ↦ ?_
    obtain hy | hγy := h_cutoff y
    · simp [hy]
    · simp [schurWeight, hγy]
  have h_schur : S.amplitudeMajorant .cut c c' γ ^ 2 ≤
      S.schurIntegral c c' γ 0 * S.schurIntegral c' c γ⁻¹ 0 := amplitudeMajorant_sq_le 0
  rw [h_integral, zero_mul] at h_schur
  exact pow_ne_zero 2 hγ (nonpos_iff_eq_zero.1 h_schur)

open scoped Classical in
/-- The bound for a block by Schur's test. Write `D_l(γ)` for the leading minors of the matrix of
products of the frame with its image under `γ`, and `f` for the number of infinite places. Let `T`
be stable under the rational unipotent group on both sides, with all elements of cell rank `j`: the
two flags share vectors from the index `j` on, `D_j ≠ 0`, and `𝗀 = termDisc` is nonzero exactly if
`j = ϱ + 1`. Suppose that on `T` the norm `termDiscNorm` of `𝗀` is at most `N ^ f * minorNorm j`,
where `minorNorm j` is the norm of `D_j`, divided by `N ^ (2 f)` at the top rank, and that no
element of `T` over `(c, s, c')` has cell rank `0`. Then the cut block is at most the covolume
`ν = unipotentCovolume` times a sum over the near terms `γ` that are the chosen element of their
double coset `U⁰_c γ U⁰_c'` under the frame-fixing unipotent groups. The summand is
`orbitBound j x`, an explicit constant depending on `j` times `x ^ (-k / 2)`, at
`x = maxGauge j c c' γ`. -/
lemma enorm_amplitudeSum_le_of_termDiscNorm_le (hT : S.IsStable T) {j : Fin (𝔰.ϱ + 2)}
    (h_cell : ∀ γ ∈ T, S.HasCellRank j γ)
    (h_disc_le : ∀ γ ∈ T, S.termDiscNorm γ ≤ S.N ^ numInfPlaces E * S.minorNorm j γ)
    {c : S.Classes} {s : S.ResidueGL} {c' : S.Classes}
    (h_not_rank_zero : ∀ γ ∈ T ∩ S.termsOver c s c', ¬S.HasCellRank 0 γ) :
    ‖S.amplitudeSum .cut T c s c'‖ₑ ≤ ∑' γ : ↥(T ∩ S.termsOver c s c'),
      if S.IsNearRepresentative c c' γ then
        ENNReal.ofReal (S.unipotentCovolume * S.orbitBound j (S.maxGauge j c c' γ))
      else 0 := by
  -- Sum the absolute amplitudes orbit by orbit.
  set X : Set (S.G E) := T ∩ S.termsOver c s c'
  have h_out (g : S.G E) : ∃ u ∈ S.classUnipotent₀ c, ∃ v ∈ S.classUnipotent₀ c',
      (DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent₀ c') g).out = u * g * v :=
    (DoubleCoset.eq ..).1 (DoubleCoset.out_eq' ..).symm
  choose u hu v hv out_eq using h_out
  have rep_mem (γ : X) : u γ * γ.val * v γ ∈ X := by
    obtain ⟨hγT, hγ_over⟩ := γ.property
    -- An element of `U⁰_c` lies in the unipotent group and over the block `(c, 1, c)`.
    obtain ⟨⟨hu_mem, hu_over⟩, -⟩ := hu γ
    obtain ⟨⟨hv_mem, hv_over⟩, -⟩ := hv γ
    exact ⟨(hT (u γ)⁻¹ (inv_mem hu_mem) _ hv_mem _).2 hγT,
      by simpa using termsOver.mul (termsOver.mul hu_over hγ_over) hv_over⟩
  -- `rep γ` is the chosen element of the orbit of `γ`.
  let rep (γ : X) : X := ⟨u γ * γ.val * v γ, rep_mem γ⟩
  have fibre_le (δ : X) : ∑' γ : rep ⁻¹' {δ}, S.amplitudeMajorant .cut c c' γ ≤
      if S.IsNearRepresentative c c' δ then
        ENNReal.ofReal (S.unipotentCovolume * S.orbitBound j (S.maxGauge j c c' δ))
      else 0 := by
    by_cases h_zero : ∑' γ : rep ⁻¹' {δ}, S.amplitudeMajorant .cut c c' γ = 0
    · simp [h_zero]
    -- If the sum is nonzero, some `γ` in the orbit has a nonzero amplitude majorant, so it is near.
    obtain ⟨⟨γ, rfl⟩, hγ⟩ := CompleteLattice.summable.tsum_ne_zero_iff.1 h_zero
    have h_nearRep : S.IsNearRepresentative c c' (rep γ) :=
      ⟨(isNear_of_amplitudeMajorant_ne_zero hγ).mul_of_mem_besselU0 (hu γ).2 (hv γ).2,
        by simp [rep, ← out_eq]⟩
    obtain ⟨hδT, hδ_over⟩ := rep_mem γ
    have hj : j ≠ 0 := fun hj ↦ h_not_rank_zero γ γ.2 (by simpa [hj] using h_cell γ γ.2.1)
    have fibre_sub : Subtype.val '' (rep ⁻¹' {rep γ}) ⊆
        doubleCoset (rep γ : S.G E) (S.classUnipotent₀ c) (S.classUnipotent₀ c') := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : rep γ = u x * x.val * v x := congrArg Subtype.val hx.symm
      rw [hx', doubleCoset_eq_of_mem (mem_doubleCoset.2 ⟨u x, hu x, v x, hv x, rfl⟩)]
      exact mem_doubleCoset_self ..
    rw [ite_eq_left h_nearRep]
    calc
      _ ≤ ∑' x : doubleCoset (rep γ : S.G E) (S.classUnipotent₀ c) (S.classUnipotent₀ c'),
          S.amplitudeMajorant .cut c c' x :=
        (tsum_image _ Subtype.val_injective.injOn).symm.trans_le (tsum_mono_subtype _ fibre_sub)
      _ ≤ _ := tsum_amplitudeMajorant_orbit_le hδ_over (h_cell _ hδT) hj (h_disc_le _ hδT)
  calc
    _ ≤ ∑' γ : X, S.amplitudeMajorant .cut c c' γ :=
      eNorm_tsum_le_tsum_eNorm.trans (tsum_le_tsum fun _ ↦ enorm_amplitude_le ..)
    _ = ∑' δ : X, ∑' γ : rep ⁻¹' {δ}, S.amplitudeMajorant .cut c c' γ := (tsum_fiberwise _ rep).symm
    _ ≤ _ := tsum_le_tsum fibre_le

/-- Write `D_l(γ)` for the leading minors of the matrix of products of the frame with its image
under `γ`, `𝗀 = |D_{ϱ+1}|² - N² |D_ϱ|²`, and `f` for the number of infinite places. Let `T` be
stable under the rational unipotent group on both sides, with all elements of cell rank `j`, and
with no element of cell rank `0` over `(c, s, c')`. Then the cut block is at most the covolume
`ν = unipotentCovolume` times a sum over the near terms `γ` that are the chosen element of their
double coset `U⁰_c γ U⁰_c'` under the frame-fixing unipotent groups. The summand is
`orbitBound j x`, an explicit constant depending on `j` times `x ^ (-k / 2)`, at
`x = maxGauge j c c' γ`. This is the larger of the norm `termDiscNorm` of `𝗀` and
`N ^ f * minorNorm j`, divided by the lattice indices `isotropicRowsIndex j` at `h_c⁻¹ γ h_c'` and
at its inverse. The sum is empty, and the block is `0`, unless `s` agrees: integral unipotent `u`,
`u'` whose reductions satisfy `u s = s u'` have the same value of the character `unipotentChar`. -/
lemma enorm_amplitudeSum_le_orbitBound (hT : S.IsStable T) {j : Fin (𝔰.ϱ + 2)}
    (h_cell : ∀ γ ∈ T, S.HasCellRank j γ) {c : S.Classes} {s : S.ResidueGL} {c' : S.Classes}
    (h_not_rank_zero : ∀ γ ∈ T ∩ S.termsOver c s c', ¬S.HasCellRank 0 γ) :
    ‖S.amplitudeSum .cut T c s c'‖ₑ ≤
      ∑' γ : {γ ∈ T ∩ S.termsOver c s c' | S.Agrees s ∧ S.IsNearRepresentative c c' γ},
        ENNReal.ofReal (S.unipotentCovolume * S.orbitBound j (S.maxGauge j c c' γ)) := by
  classical
  -- On the set `K` of terms where the norm of `𝗀` exceeds `N ^ f * minorNorm j` use the open cell;
  -- off `K` use Schur's test.
  by_cases! hs : ¬S.Agrees s
  · simp [amplitudeSum_eq_zero_of_not_agrees, hT, hs]
  let bound (γ : S.G E) : ℝ≥0∞ :=
    if S.IsNearRepresentative c c' γ then .ofReal
      (S.unipotentCovolume * S.orbitBound j (S.maxGauge j c c' γ))
    else 0
  let K : Set (S.G E) := {γ | S.N ^ numInfPlaces E * S.minorNorm j γ < S.termDiscNorm γ}
  have K_stable : S.IsStable K := by
    simp +contextual [IsStable, K, minorNorm, termDiscNorm,
      frameDisc_frameGram_inv_mul_mul_of_mem_besselU,
      leadingMinor_frameGram_besselU_mul]
  have on_stable : S.IsStable (T ∩ K) := fun u hu u' hu' γ ↦
    and_congr (hT u hu u' hu' γ) (K_stable u hu u' hu' γ)
  have off_stable : S.IsStable (T ∩ Kᶜ) := fun u hu u' hu' γ ↦
    and_congr (hT u hu u' hu' γ) (K_stable u hu u' hu' γ).not
  have disc_ne (γ : S.G E) (hγ : γ ∈ K) : S.termDisc γ ≠ 0 := fun h_zero ↦ hγ.out.not_ge <| by
    rw [show S.termDiscNorm γ = 0 by simp [termDiscNorm, h_zero], minorNorm]
    positivity
  have on_K : ‖S.amplitudeSum .cut (T ∩ K) c s c'‖ₑ ≤
      ∑' γ : ↥(T ∩ K ∩ S.termsOver c s c'), bound γ := by
    refine (enorm_amplitudeSum_le_orbitBound_top on_stable (fun γ hγ ↦ disc_ne γ hγ.2) c s c').trans
      (tsum_le_tsum fun ⟨γ, ⟨hγT, hγK⟩, _⟩ ↦ ?_)
    -- A term with `𝗀 ≠ 0` has the top cell rank, where the indices are `1`.
    obtain rfl : j = ⊤ := by grind [HasCellRank]
    simp [bound, (h_cell γ hγT).maxGauge_eq, isotropicRowsIndex_top, hγK.out.le]
  have off_K : ‖S.amplitudeSum .cut (T ∩ Kᶜ) c s c'‖ₑ ≤
      ∑' γ : ↥(T ∩ Kᶜ ∩ S.termsOver c s c'), bound γ :=
    enorm_amplitudeSum_le_of_termDiscNorm_le off_stable (fun γ hγ ↦ h_cell γ hγ.1)
      (fun γ hγ ↦ not_lt.1 hγ.2) fun γ ⟨⟨hγT, _⟩, hγ_over⟩ ↦ h_not_rank_zero γ ⟨hγT, hγ_over⟩
  calc
    _ ≤ ∑' γ : ↥(T ∩ Kᶜ ∩ S.termsOver c s c' ∪ T ∩ K ∩ S.termsOver c s c'), bound γ := by
      rw [amplitudeSum_eq_inter_compl_add_inter T K,
        CompleteLattice.summable.tsum_union_of_disjoint (by grind) CompleteLattice.summable]
      exact (eNorm_add_le ..).trans (add_le_add off_K on_K)
    _ ≤ ∑' γ : ↥(T ∩ S.termsOver c s c'), bound γ := tsum_mono_subtype bound (by grind)
    _ = _ := by
      rw [_root_.tsum_subtype _ bound,
        _root_.tsum_subtype _ fun γ ↦
          ENNReal.ofReal (S.unipotentCovolume * S.orbitBound j (S.maxGauge j c c' γ))]
      -- Both sums agree, as `s` agrees and `bound` vanishes unless `IsNearRepresentative` holds.
      exact tsum_congr fun γ ↦ by grind [indicator]

/-- For a function `f` on the rational elements, the amplitude sum `S.amplitudeSum side T c s c'` is
the sum over `i` of the amplitude sums `S.amplitudeSum side (T ∩ f ⁻¹' {i}) c s c'` of the
fibres. -/
lemma hasSum_amplitudeSum_fibre {side : FullOrCut} {ι : Type} (f : S.G E → ι) (c : S.Classes)
    (s : S.ResidueGL) (c' : S.Classes) :
    HasSum (fun i : ι ↦ S.amplitudeSum side (T ∩ f ⁻¹' {i}) c s c')
      (S.amplitudeSum side T c s c') := by
  refine ((summable_amplitude ..).hasSum.tsum_fiberwise
    fun γ : ↥(T ∩ S.termsOver c s c') ↦ f γ).congr_fun fun i ↦ ?_
  -- Both sides sum the amplitudes over the same set of terms, written in two ways.
  have h_set : {γ | f γ = i ∧ γ ∈ T ∧ γ ∈ S.termsOver c s c'} =
      T ∩ f ⁻¹' {i} ∩ S.termsOver c s c' := by grind
  simp [amplitudeSum, ← tsum_image, _root_.tsum_subtype, Set.image, h_set]

/-- For a function `f` on the rational elements, the norm of the cut amplitude sum
`S.amplitudeSum .cut T c s c'` is at most the sum over `i` of the norms of the cut amplitude sums of
the fibres `T ∩ f ⁻¹' {i}` at the same `c`, `s`, `c'`. -/
lemma enorm_amplitudeSum_le_tsum_fibre {ι : Type} (f : S.G E → ι) (c : S.Classes) (s : S.ResidueGL)
    (c' : S.Classes) :
    ‖S.amplitudeSum .cut T c s c'‖ₑ ≤ ∑' i : ι, ‖S.amplitudeSum .cut (T ∩ f ⁻¹' {i}) c s c'‖ₑ := by
  grw [← (hasSum_amplitudeSum_fibre f c s c').tsum_eq, eNorm_tsum_le_tsum_eNorm]

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible] in
/-- Every element of `Γ* = S.remainingTerms` has a cell rank, namely `S.cellRank γ`. -/
lemma hasCellRank_cellRank_of_mem {γ : S.G E} (hγ : γ ∈ S.remainingTerms) :
    S.HasCellRank (S.cellRank γ) γ := by
  obtain h_disc | ⟨h_agree, h_disc, -⟩ := mem_remainingTerms_iff.1 hγ
  · exact (hasCellRank_last h_disc).hasCellRank_cellRank
  · obtain ⟨j, hj⟩ := h_agree.exists_hasCellRank h_disc
    exact hj.hasCellRank_cellRank

/-- **Size.** Let `S` be admissible filling data of shape `𝔰` over a CM field `E` with a primitive
root of unity of order 5040. The set `Γ* = S.remainingTerms` consists of the rational `γ` with
`𝗀(γ) = S.termDisc γ ≠ 0`, and of those with `𝗀(γ) = 0` that move the isotropic space `⟨e₁, …, e_ϱ⟩`
and for which the unipotent character takes the same value at unipotent `u`, `u'` with `u γ = γ u'`.
Let `T ⊆ Γ*` be stable under the rational unipotent group on both sides, and fix classes `c`, `c'`
and a reduction `s`. The norm of the cut block is at most the covolume `unipotentCovolume` times the
sum of the sizes of the near representatives. These are the terms of `T` over the block that are
near, are the chosen element of their orbit `U⁰_c γ U⁰_c'` and have a cell rank `j ≤ ϱ + 1`,
provided `s` agrees; otherwise there are none. -/
theorem enorm_amplitudeSum_le_tsum_termSize (hT : S.IsStable T) (h_sub : T ⊆ S.remainingTerms)
    (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) :
    ‖S.amplitudeSum .cut T c s c'‖ₑ ≤
      ∑' γ : S.nearRepresentativesOver T c s c',
        .ofReal (S.unipotentCovolume * S.termSize c c' γ) := by
  -- Sort the terms by their cell rank and bound each part.
  let size (γ : S.G E) : ℝ≥0∞ := .ofReal (S.unipotentCovolume * S.termSize c c' γ)
  grw [enorm_amplitudeSum_le_tsum_fibre S.cellRank c s c', ← tsum_fiberwise _
    fun γ : S.nearRepresentativesOver T c s c' ↦ S.cellRank γ]
  refine tsum_le_tsum fun j ↦ ?_
  let part : Set (S.G E) := T ∩ S.cellRank ⁻¹' {j}
  have h_stable : S.IsStable part := by
    intro u hu u' hu' γ
    have h_iff (i : Fin (𝔰.ϱ + 2)) : S.HasCellRank i (u⁻¹ * γ * u') ↔ S.HasCellRank i γ :=
      S.isStable_hasCellRank i u hu u' hu' γ
    have cellRank_eq : S.cellRank (u⁻¹ * γ * u') = S.cellRank γ := by
      simp only [cellRank, h_iff]
    simp [part, cellRank_eq, hT u hu u' hu' γ]
  have h_cell : ∀ γ ∈ part, S.HasCellRank j γ := by
    rintro γ ⟨hγT, rfl : S.cellRank γ = j⟩
    exact hasCellRank_cellRank_of_mem (h_sub hγT)
  have h_not_rank_zero : ∀ γ ∈ part ∩ S.termsOver c s c', ¬S.HasCellRank 0 γ := by
    rintro γ ⟨⟨hγT, -⟩, -⟩ h_zero
    exact h_zero.normOnePairOccursFrom.notMem_remainingTerms (h_sub hγT)
  grw [enorm_amplitudeSum_le_orbitBound h_stable h_cell h_not_rank_zero]
  -- The terms in this bound are near representatives of `T` with cell rank `j`.
  let near : Set (S.G E) :=
    {γ ∈ part ∩ S.termsOver c s c' | S.Agrees s ∧ S.IsNearRepresentative c c' γ}
  have near_mem (γ : near) : (γ : S.G E) ∈ S.nearRepresentativesOver T c s c' := by
    obtain ⟨γ, ⟨⟨hγT, -⟩, hγ_over⟩, hs, h_nearRep⟩ := γ
    exact ⟨⟨hγT, hγ_over⟩, hs, h_nearRep, hasCellRank_cellRank_of_mem (h_sub hγT)⟩
  have near_rank (γ : near) : S.cellRank γ = j := by
    obtain ⟨γ, ⟨⟨-, h_rank⟩, -⟩, -⟩ := γ
    exact h_rank
  let incl (γ : near) : (fun γ : S.nearRepresentativesOver T c s c' ↦ S.cellRank γ) ⁻¹' {j} :=
    ⟨⟨γ, near_mem γ⟩, near_rank γ⟩
  have incl_injective : incl.Injective := fun γ γ' h ↦ by grind
  calc
    _ = ∑' γ : near, size γ := tsum_congr fun γ ↦ by simp only [size, termSize, near_rank γ]
    _ ≤ _ := tsum_comp_le_tsum_of_injective incl_injective fun γ ↦ size γ.val

end New.Filling

end SizeOfBlocks
