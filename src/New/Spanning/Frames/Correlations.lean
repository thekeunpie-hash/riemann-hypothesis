module

import Mathlib.CategoryTheory.Countable
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.DiscreteSeries.Bruhat.FloorMeasures
public import New.Spanning.Frames.Lengths
import Lib.Base
import Mathlib.MeasureTheory.Group.IntegralConvolution

section
/-!
# Place data, floor measures and depth

A place datum `F` fixes a unit M, a compact set K and a basis adapted to the frame. The group
measure is built floor by floor: floor `l ≤ ϱ` chooses the frame vector f_l on its quadric and an
element of the Heisenberg group along it, and floor ϱ + 1 carries the measure of H. The letters
Y^(l), K and M are those of the head of `New.Spanning.Frames.Lengths`.

Notions from other files:
* G = `T.G` is the unitary group of `T.splitGram`, a hermitian form with ϱ = `𝔰.ϱ` hyperbolic pairs
  e_a, e*_a; its basis vectors are indexed by `𝔰.BesselIndex`, and n = `𝔰.n` is ϱ + 1.
* G^(l) = `floorGroup l` is the group of isometries that fix the basis vectors of floor below l;
  H = `besselH` is G^(ϱ+1).
* R^(l) = `partialUnitriangularGroup l` is the group of isometries that are unitriangular on the
  first l frame vectors, and U = `besselU` is the Bessel unipotent group.
* `orbitPoint b g` is the vector g⁻¹ f_b, where f_b is the frame vector of floor b, and
  `F.floorQuadricMeasure b` is the measure on the quadric through f_b.
* η_l = `heisenbergMeasure l` is the measure of the Heisenberg group of floor l, and `weylLaw l` is
  a measure carried by the inverse Weyl elements of floor l.

## Main definitions and results

* `New.Floors.PlaceData`, `New.Floors.PlaceData.floorMeasure`, `New.Floors.PlaceData.groupMeasure`:
  the data and the measures.
* `New.Floors.PlaceData.IsNear`, `New.Floors.PlaceData.IsStable`,
  `New.Floors.PlaceData.stableProducts`, `New.Floors.PlaceData.depth`,
  `New.Floors.PlaceData.depthWeight`: points near K, stable vectors, their products with e_a, depth
  and the weight.
* `New.Floors.PlaceData.measurePreserving_orbitPoint`: a floor measure maps to the measure of the
  quadric.
* `New.Floors.PlaceData.partialGroupMeasure_mconv_dirac`,
  `New.Floors.PlaceData.lintegral_partialGroupMeasure_weylElem_inv_mul`: invariance on the right,
  and invariance under a Weyl element on the left for the lower floors, for integrals of functions
  fixed on the left by G^(j), when the group measure is Haar.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

@[expose] public section

noncomputable section

namespace New.Floors

section LevelGauge

open Matrix MeasureTheory Measure BesselIndex ENNReal Fintype FloorGroups Place TraceOne Function
  Filter

variable {A : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  (ι : Type) [Fintype ι] [DecidableEq ι] {𝔰 : Shape} (T : 𝔰.Form A) (m : ℕ)
  [IsHermitianUnit T.splitGram] {l i j : ℕ}

/-!
## Place data, floor measures and their invariance

`New.Floors.descConv σ a i` is the convolution `σ (a + i - 1) ∗ ⋯ ∗ σ a`, and `η_l` is
`New.Floors.Place.heisenbergMeasure l`.
-/

/-- The data of a place: a basis of hyperbolic pairs and orthonormal vectors, the measures of the
top floor and of H, the level M (the field `levelUnit`), the close pairs of vectors, the compact set
K of the group and the set of positions. -/
structure PlaceData extends HyperbolicBasis ι T m where
  /-- The measure of the top floor, on G^(ϱ) = `floorGroup 𝔰.ϱ`. -/
  topFloorMeasure : Measure T.G
  /-- A right invariant measure carried by H = `besselH`; see
  `measureH_mem_and_invariant_and_le_one`. -/
  measureH : Measure T.G
  /-- The level M, a unit by which differences of vectors and frequencies are divided. -/
  levelUnit : Aˣ
  /-- The close pairs (ω₁, ω₂) of vectors. In the place data that are used they are the pairs with
  |ω₁|² + |ω₂|² < 1 at a real place, and those with ω₁ in the lattice and ω₂ ≡ ω₁ modulo M at the
  finite places. -/
  closePairs : Set ((𝔰.BesselIndex → A) × (𝔰.BesselIndex → A))
  /-- The compact set K in the unitary group G. -/
  boxSet : Set T.G
  /-- The positions: the elements of G by which the second point of a pair differs from the
  first. -/
  positions : Set T.G
  /-- The measure `topFloorMeasure` is s-finite. -/
  [sFinite_topFloorMeasure : SFinite topFloorMeasure]
  /-- The measure of H is s-finite. -/
  [sFinite_measureH : SFinite measureH]
  /-- The measure of H is not zero. -/
  [neZero_measureH : NeZero measureH]
  /-- `topFloorMeasure` is carried by G^(ϱ), and σ ↦ σ⁻¹ f_ϱ maps it to the measure of the top
  quadric. -/
  topFloorMeasure_mem_and_map_eq :
      (∀ᵐ x : T.G ∂topFloorMeasure, x ∈ floorGroup 𝔰.ϱ) ∧
      topFloorMeasure.map (orbitPoint 𝔰.top) = toHyperbolicBasis.floorQuadricMeasure 𝔰.top
  /-- The measure of H is carried by H, is invariant under right translation by H, and for every g
  gives mass at most 1 to the h with h g ∈ U K. -/
  measureH_mem_and_invariant_and_le_one :
      (∀ᵐ x : T.G ∂measureH, x ∈ besselH) ∧
      (∀ s ∈ besselH, measureH ∗ₘ dirac s = measureH) ∧
      ∀ g : T.G, measureH {h : T.G | ∃ u ∈ besselU, u * (h * g) ∈ boxSet} ≤ 1
  /-- The level is fixed by the involution. -/
  star_levelUnit : star levelUnit.val = levelUnit
  /-- The set of close pairs is open, contains 0 and has compact closure. -/
  isOpen_closePairs_and_zero_mem_and_isCompact_closure :
    IsOpen closePairs ∧ 0 ∈ closePairs ∧ IsCompact (closure closePairs)
  /-- The set K is compact and the set of positions is measurable. -/
  isCompact_boxSet_and_measurableSet_positions : IsCompact boxSet ∧ MeasurableSet positions

variable {ι T m} {ν ρ : Measure T.G} [SFinite ν] [SFinite ρ]
  {s : T.G} {S : Subgroup T.G} {f Φ : T.G → ℝ≥0∞} (F : PlaceData ι T m) (b : Fin 𝔰.n)

namespace PlaceData

attribute [instance] sFinite_topFloorMeasure sFinite_measureH neZero_measureH

/-- The measure `F.topFloorMeasure` of the top floor is carried by G^(ϱ) = `floorGroup 𝔰.ϱ`. -/
lemma ae_topFloorMeasure_mem_floorGroup (F : PlaceData ι T m) : ∀ᵐ x : T.G ∂F.topFloorMeasure,
  x ∈ floorGroup 𝔰.ϱ :=
  F.topFloorMeasure_mem_and_map_eq.left

/-- The map `orbitPoint 𝔰.top`, σ ↦ σ⁻¹ f_ϱ with f_ϱ = z the last frame vector, carries
`F.topFloorMeasure`, the measure of the top floor that is part of the place data `F`, to
`F.floorQuadricMeasure 𝔰.top`, the measure on the top quadric. -/
lemma map_orbitPoint_topFloorMeasure (F : PlaceData ι T m) :
    F.topFloorMeasure.map (orbitPoint 𝔰.top) = F.floorQuadricMeasure 𝔰.top :=
  F.topFloorMeasure_mem_and_map_eq.right

/-- The measure `F.measureH` is carried by H = `besselH`, the fixer of the hyperbolic pairs and the
last frame vector. -/
lemma ae_measureH_mem_besselH (F : PlaceData ι T m) : ∀ᵐ x : T.G ∂F.measureH, x ∈ besselH :=
  F.measureH_mem_and_invariant_and_le_one.left

/-- The measure `F.measureH` is invariant under right translation by H = `besselH`. -/
lemma measureH_mconv_dirac (F : PlaceData ι T m) {s : T.G} (hs : s ∈ besselH) :
    F.measureH ∗ₘ dirac s = F.measureH := by
  obtain ⟨-, h_right, -⟩ := F.measureH_mem_and_invariant_and_le_one
  exact h_right s hs

/-- For every g, the h with h g ∈ U K, that is u h g ∈ K for some u in U, have mass at most 1 for
`F.measureH`. Here U = `besselU` is the Bessel unipotent group and K = `F.boxSet`. -/
lemma measureH_setOf_mul_mem_boxSet_le_one (g : T.G) :
    F.measureH {h : T.G | ∃ u ∈ besselU, u * (h * g) ∈ F.boxSet} ≤ 1 := by
  obtain ⟨-, -, h_mass⟩ := F.measureH_mem_and_invariant_and_le_one
  exact h_mass g

/-- The measure θ_l of floor l on G^(l). For l ≤ ϱ the map `orbitPoint l` carries it to the quadric
measure `F.floorQuadricMeasure l`, and for l < ϱ it lives on the big cell. Floor n = ϱ + 1 carries
the measure of H, and higher floors a unit mass at 1. -/
def floorMeasure (l : ℕ) : Measure T.G :=
  if l < 𝔰.ϱ then weylLaw l ∗ₘ heisenbergMeasure l
  else if l = 𝔰.ϱ then F.topFloorMeasure
  else if l = 𝔰.n then F.measureH
  else dirac 1

/-- Every floor measure is s-finite. -/
instance : SFinite (F.floorMeasure l) := by
  fun_cases floorMeasure
  all_goals infer_instance

/-- `partialGroupMeasure l i` convolves the Heisenberg and floor measures of the i floors from l on.
For l + i = ϱ + 2 it is invariant under right translation by G^(l)
(`partialGroupMeasure_mconv_dirac`). -/
abbrev partialGroupMeasure : ℕ → ℕ → Measure T.G :=
  descConv fun a : ℕ ↦ heisenbergMeasure a ∗ₘ F.floorMeasure a

/-- The measure (η_{ϱ+1}∗θ_{ϱ+1}) ∗ ⋯ ∗ (η₀∗θ₀) on the unitary group, the convolution over all
floors, where η_a = `heisenbergMeasure a` and θ_a = `F.floorMeasure a`. -/
abbrev groupMeasure : Measure T.G := F.partialGroupMeasure 0 (𝔰.ϱ + 2)

/-- The convolution θ_(ϱ+1) ∗ ⋯ ∗ θ_l of the floor measures from l on. It serves to integrate
functions on G^(l) that are left invariant under U ∩ G^(l). -/
@[simp]
abbrev quotientMeasureFrom (l : ℕ) : Measure T.G := descConv F.floorMeasure l (𝔰.ϱ + 2 - l)

/-- A point g is near at j if R^(j) g meets K = `F.boxSet`, where R^(j) =
`partialUnitriangularGroup j`. -/
def IsNear (j : ℕ) (g : T.G) : Prop := ∃ ξ ∈ T.partialUnitriangularGroup j, ξ * g ∈ F.boxSet

/-- The rank 2 m + 2 of a block of orthonormal basis vectors in which the equation of a quadric is
solved. -/
abbrev blockRank (_ : PlaceData ι T m) : ℕ := 2 * m + 2

/-- The indices of the orthonormal basis vectors that remain when two blocks are set aside. These
vectors span the space X'. -/
abbrev FreeIndex : Type := Fin (card ι - 2 * F.blockRank)

/-- The index in ι of a basis vector of X'. These are the first `card ι - 2 * F.blockRank`
orthonormal basis vectors in a fixed numbering of ι. -/
def freeIndex (i : F.FreeIndex) : ι :=
  (equivFin ι).symm (i.castLE (Nat.sub_le (card ι) (2 * F.blockRank)))

/-- The matrix whose columns are the basis vectors of X'; it embeds X' into the space. For a vector
y, we write y_X for the vector of the products of these columns with y. -/
abbrev orthonormalPart : Matrix 𝔰.BesselIndex F.FreeIndex A :=
  fromRows 0 ((F.basisMatrix.toCols₂.toCols₂.toCols₁.submatrix id F.freeIndex).fromRows 0)

/-- A vector ω is short from g and g' if (g⁻¹ ω, g'⁻¹ ω) is a close pair. -/
abbrev IsShortFrom (g g' : T.G) (ω : 𝔰.BesselIndex → A) : Prop :=
  (g⁻¹.val.val *ᵥ ω, g'⁻¹.val.val *ᵥ ω) ∈ F.closePairs

/-- The class of ω in Y^(l) is stable at g and g', with ω as its lift at g: the vector ω is
orthogonal to the e_b, b < l, and (g⁻¹ ω, g'⁻¹ ω') is a close pair for some ω' that agrees with ω
at all indices k with l ≤ `level k` (for l ≤ ϱ, another lift of the class). -/
def IsStable (l : ℕ) (g g' : T.G) (ω : 𝔰.BesselIndex → A) : Prop :=
  IsOrthogonalBelow l ω ∧ ∃ ω' : 𝔰.BesselIndex → A,
    CongrBelow l ω ω' ∧ (g⁻¹.val.val *ᵥ ω, g'⁻¹.val.val *ᵥ ω') ∈ F.closePairs

/-- The set 𝔡_a at the points x and x y: the products ⟨e_a, ω⟩ with the vectors ω of Y^(a) that are
stable at x and x y. In the place data that are used it is a disc at a real place, and at the finite
places a fractional ideal, contained in the integers if x is near at a + 1. -/
def stableProducts (a : Fin 𝔰.ϱ) (x y : T.G) : Set A :=
  (fun ω : 𝔰.BesselIndex → A ↦ ω (eStar a)) ''
    {ω : 𝔰.BesselIndex → A | F.IsStable a x (x * y) ω}

/-- The depth of the vector e_a at the points x and x y: the inverse of the volume of 𝔡_a. In the
place data that are used it is as follows. At the finite places it is the index of the ideal 𝔡_a if
x is near at a + 1. At a real
place it is 1 / π times the infimum of |ζ|² at x plus |ζ|² at x y over the duals ζ of e_a in Y^(a)
(`New.Floors.RealPlaceSizes.depth_eq`). -/
def depth (a : Fin 𝔰.ϱ) (x y : T.G) : ℝ≥0∞ := (volume (F.stableProducts a x y))⁻¹

/-- The exponent s of the depths in `depthWeight`: the rank of X' minus (3 n + 1 + m). -/
abbrev volumeExponent : ℕ := card F.FreeIndex - (3 * 𝔰.n + 1 + m)

/-- The weight of length j at the points x and x y: the product of the powers depth^(-s),
s = `F.volumeExponent`, over the first j vectors e_a. -/
def depthWeight (j : ℕ) (x y : T.G) : ℝ≥0∞ :=
  ∏ a : Fin 𝔰.ϱ with a.val < j, (F.depth a x y)⁻¹ ^ F.volumeExponent

/-- The common vectors: the ω in X' that are killed by the rows of v and are short from g
and g z. -/
def commonVectors (g z : T.G) (v : Matrix (Fin 𝔰.ϱ) F.FreeIndex A) : Set (F.FreeIndex → A) :=
  {ω : F.FreeIndex → A | v *ᵥ ω = 0 ∧ F.IsShortFrom g (g * z) (F.orthonormalPart *ᵥ ω)}

/-- The numbers (⟨ω₁, ω'₁⟩ - ⟨ω₂, ω'₂⟩) / M for two pairs (ω₁, ω₂), (ω'₁, ω'₂) in `closePairs`. In
the place data that are used they lie in the disc of radius 1 at a real place and are integral at
the finite places. -/
def productDifferences : Set A :=
  {c : A | ∃ z ∈ F.closePairs, ∃ z' ∈ F.closePairs,
    c = F.levelUnit⁻¹ * (star z.1 ⬝ᵥ T.splitGram *ᵥ z'.1 - star z.2 ⬝ᵥ T.splitGram *ᵥ z'.2)}

/-- The function φ on X' controls the products with the set W of vectors, and its s-th power,
s = `F.volumeExponent`, has integral at most Λ^(99 n (j+1)) over the vectors of size j for the
scale `S`. -/
structure IsCommonBound (S : Size T) (Λ : ℝ≥0∞) (W : Set (F.FreeIndex → A))
    (φ : (F.FreeIndex → A) → ℝ≥0∞) : Prop where
  /-- The function φ is measurable. -/
  measurable : Measurable φ
  /-- φ(u) bounds 1 / vol ⟨u, W⟩. -/
  inv_volume_le (u : F.FreeIndex → A) :
    (volume ((fun ω : F.FreeIndex → A ↦ star u ⬝ᵥ ω) '' W))⁻¹ ≤ φ u
  /-- φ(u) bounds the volume of the numbers c with ⟨c u, W⟩ inside `productDifferences`. -/
  volume_le (u : F.FreeIndex → A) :
    volume {c : A | ∀ ω ∈ W, star (c • u) ⬝ᵥ ω ∈ F.productDifferences} ≤ φ u
  /-- The integral of φ^s over the vectors of size j is at most Λ^(99 n (j+1)). -/
  lintegral_le (j : ℕ) :
    ∫⁻ u : F.FreeIndex → A in S.vecsOfSize j, φ u ^ F.volumeExponent ≤ Λ ^ (99 * 𝔰.n * (j + 1))

/-- The number |g|^(r+1/2), where r = k + 1 + 2 (ϱ - (l + 1)) is the rank of the vector part of the
Heisenberg group of floor l; by default g is the level M. -/
def floorModulus (l : ℕ) (g := F.levelUnit) : ℝ≥0∞ :=
  P.modulus g ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (l + 1))) * P.modulus g ^ (2⁻¹ : ℝ)

variable {F}

/-- The enumeration of the basis of V_a, the span of the basis vectors of floor at least a: first
the hyperbolic pair e_a, e*_a, then the basis vectors of the higher floors. -/
def floorIndexEnum (a : Fin 𝔰.ϱ) :
    Fin 2 ⊕ {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → 𝔰.BesselIndex :=
  ![.inl a, eStar a] ⊕ᵥ Subtype.val

/-- The Gram matrix of the basis vectors of floor at least l. -/
def upperGram (l : ℕ) :
    Matrix {i : 𝔰.BesselIndex // l ≤ floorOf i} {i : 𝔰.BesselIndex // l ≤ floorOf i} A :=
  T.splitGram.submatrix Subtype.val Subtype.val

/-- The enumeration `floorIndexEnum a` of the basis of V_a has no repetitions. -/
lemma floorIndexEnum_injective (a : Fin 𝔰.ϱ) : Injective (floorIndexEnum a) := by
  -- the only coincidences to exclude are those of `e_a`, `e*_a` with a higher pair
  suffices (∀ c : Fin 𝔰.ϱ, a < c → a ≠ c) ∧ ∀ c : Fin 𝔰.ϱ, a < c → c ≠ a by
    simpa [floorIndexEnum, Injective] using this
  exact ⟨fun c hc ↦ hc.ne, fun c hc ↦ hc.ne'⟩

/-- The enumeration `floorIndexEnum a` lists exactly the basis indices of floor at least a. -/
lemma mem_range_floorIndexEnum (a : Fin 𝔰.ϱ) (i : 𝔰.BesselIndex) :
    i ∈ Set.range (floorIndexEnum a) ↔ a.val ≤ floorOf i := by
  have h_le (c : Fin 𝔰.ϱ) : c = a ∨ a < c ↔ a ≤ c := by rw [le_iff_eq_or_lt, eq_comm]
  obtain c | (k | z) | c := i
  · -- `e_c` is listed if `c = a` or `a < c`
    simp [floorIndexEnum, h_le]
  · -- the middle indices other than `z` have floor `n`
    have ha : a.val ≤ 𝔰.n := by grind
    simp [floorIndexEnum, ha]
  · -- `z` has floor ϱ
    simp [floorIndexEnum]
  · -- `e*_c` is listed if `c = a` or `a < c`
    simp [floorIndexEnum, h_le]

omit [IsHermitianUnit T.splitGram] [TopologicalSpace A] [MeasureSpace A] [Place A] in
/-- In the basis `floorIndexEnum a` of V_a, the form `T.splitGram` is a hyperbolic plane plus the
form `upperGram (a + 1)` on the higher floors. -/
lemma gram_inclMatrix_floorIndexEnum (a : Fin 𝔰.ϱ) :
    (inclMatrix A (floorIndexEnum a))ᴴ * T.splitGram * inclMatrix A (floorIndexEnum a) =
      planeSumGram (upperGram (T := T) (a + 1)) := by
  rw [conjTranspose_inclMatrix_mul_mul_inclMatrix]
  -- the pair of floor `a` is orthogonal to the higher pairs
  suffices (∀ c : Fin 𝔰.ϱ, a < c → a = c → (1 : A) = 0) ∧
      ∀ c : Fin 𝔰.ϱ, a < c → c = a → (1 : A) = 0 by
    simpa [floorIndexEnum, upperGram, ← ext_iff] using this
  exact ⟨fun c hc h ↦ absurd h hc.ne, fun c hc h ↦ absurd h hc.ne'⟩

/-- For a < ϱ, the measure `F.floorQuadricMeasure a.castSucc` on the quadric h(v, v) = 0 of V_a can
be computed in the basis `floorIndexEnum a`. It is the image, under extension by zero, of the
measure `quadricMeasure` with parameter 0 of a hyperbolic plane plus the form `upperGram (a + 1)` on
the higher floors. -/
lemma floorQuadricMeasure_castSucc_eq_map (a : Fin 𝔰.ϱ) :
    F.floorQuadricMeasure a.castSucc =
      (quadricMeasure (upperGram (T := T) (a + 1)) 0).map
        (inclMatrix A (floorIndexEnum a) *ᵥ ·) := by
  -- Disintegrations of `floorVolume a` along `h(v, v)` are unique, and both sides are the member
  -- at `h(e_a, e_a) = 0` of such a disintegration.
  let E : Matrix 𝔰.BesselIndex (Fin 2 ⊕ {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i}) A :=
    inclMatrix A (floorIndexEnum a)
  have h_left : Eᴴ * E = 1 := by
    simpa [submatrix_one _ (floorIndexEnum_injective a)] using
      conjTranspose_inclMatrix_mul_mul_inclMatrix (R := A) 1 (floorIndexEnum a) (floorIndexEnum a)
  have h_vol : volume.map (E *ᵥ ·) = floorVolume a.castSucc :=
    map_inclMatrix_eq_floorVolume _ (floorIndexEnum_injective a) (mem_range_floorIndexEnum a)
  have h_herm : (upperGram (T := T) (a + 1)).IsHermitian :=
    IsHermitian.submatrix IsHermitianUnit.conjTranspose_eq _
  have h_dis :
      IsDisintegration (volume.map (E *ᵥ ·)) T.splitGram fun β : skewAdjoint A ↦
        (quadricMeasure (upperGram (T := T) (a + 1)) β).map (E *ᵥ ·) :=
    (isDisintegration_quadricMeasure (T := upperGram (T := T) (a + 1)) h_herm).map
      (gram_inclMatrix_floorIndexEnum a) h_left
  have h_zero :
      skewUnitMul (T.splitGram (𝔰.besselFrame a.castSucc) (𝔰.besselFrame a.castSucc)) = 0 := by
    ext
    simp
  rw [← h_zero]
  exact (F.isDisintegration_floorVolume _ h_vol).unique h_dis

/-- Let a < ϱ, let t be a unit, u a vector on the floors above a and β skew. The point ((t, t u), β)
of the chart `flatChart` of the quadric h(v, v) = 0 for a hyperbolic plane plus `upperGram (a + 1)`
is sent by `inclMatrix A (floorIndexEnum a)` to the image of e_a under the product of the Heisenberg
element `heisenbergElem a (u, β)` and the Weyl element `floorWeyl a t`. -/
lemma inclMatrix_mulVec_flatChart_eq_heisenbergElem_mulVec (a : Fin 𝔰.ϱ) (t : Aˣ)
    (u : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) (β : skewAdjoint A) :
    inclMatrix A (floorIndexEnum a) *ᵥ
        flatChart (upperGram (T := T) (a + 1)) 0 ((t, t.val • u), β) =
      (heisenbergElem (T := T) a (u, β)).val.val *ᵥ
        (floorWeyl a t.val : T.G).val.val *ᵥ Pi.single (.inl a) 1 := by
  have h_weyl : (floorWeyl a t.val : T.G).val.val *ᵥ Pi.single (.inl a) 1 =
      Pi.single (eStar a) t.val := by
    ext i
    simp [floorWeyl, weylOn, level, ← Pi.single_apply, col_apply']
  -- `c = h(u, u)`, written with the Gram matrix of the higher floors or after extension by zero
  set c : A := star u ⬝ᵥ upperGram (T := T) (a + 1) *ᵥ u with hc
  have h_form : star (inclMatrix A Subtype.val *ᵥ u) ⬝ᵥ T.splitGram *ᵥ inclMatrix A Subtype.val *ᵥ u
      = c := by
    rw [hc, upperGram, ← conjTranspose_inclMatrix_mul_mul_inclMatrix, star_mulVec_dotProduct,
      mulVec_mulVec, mulVec_mulVec]
  -- the coordinates of the chart point, where `h(t u, t u) = t̄ t c`
  have h_chart : flatChart (upperGram (T := T) (a + 1)) 0 ((t, t.val • u), β) =
      ![(β - element * c) * t, t] ⊕ᵥ t.val • u := by
    have h_cancel : Ring.inverse (star t.val) * star t.val = 1 :=
      Ring.inverse_mul_cancel _ t.isUnit.star
    have h_scale : star (t.val • u) ⬝ᵥ upperGram (T := T) (a + 1) *ᵥ t.val • u =
        star t.val * (t * c) := by
      simp [mulVec_smul, hc, mul_left_comm]
    rw [flatChart, h_scale]
    congr 2
    rw [ZeroMemClass.coe_zero]
    linear_combination (-element * t * c) * h_cancel
  have h_incl (x y : A) (w : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) :
      inclMatrix A (floorIndexEnum a) *ᵥ (![x, y] ⊕ᵥ w) =
        Pi.single (eStar a) y + inclMatrix A Subtype.val *ᵥ w + x • Pi.single (.inl a) 1 := by
    ext i
    simp [floorIndexEnum, inclMatrix, mulVec_apply_eq_sum, Pi.single_apply, Matrix.one_apply,
      add_comm, add_assoc]
    -- the two sums differ only in their `Fintype` instances
    congr!
  rw [h_chart, h_incl, mulVec_smul, h_weyl, heisenbergElem_mulVec, h_form]
  simp [inclMatrix_val_mulVec, ↓splitGram_col]

/-- Let f be the b-th vector of the frame (e_0, …, e_{ϱ-1}, z) = `𝔰.besselFrame`. The map
`orbitPoint b`, σ ↦ σ⁻¹ f, carries the measure `F.floorMeasure b` on the isometries fixing the basis
vectors of floor below b to the measure `F.floorQuadricMeasure b` on the quadric h(v, v) = h(f, f)
in the span of the other basis vectors. -/
lemma measurePreserving_orbitPoint {F : PlaceData ι T m} (b : Fin 𝔰.n) :
    MeasurePreserving (orbitPoint b) (F.floorMeasure b) (F.floorQuadricMeasure b) := by
  refine ⟨by fun_prop, b.lastCases (by simp [floorMeasure, map_orbitPoint_topFloorMeasure]) fun a ↦
               ?_⟩
  -- Below floor ϱ, integrate a test function `Φ` in the flat chart `χ` of the quadric. A chart
  -- point is the value of `orbitPoint` at a point of the big cell, the inverse of `floorWeyl a t`
  -- times a Heisenberg element.
  refine ext_of_lintegral _ fun Φ hΦ ↦ ?_
  let V : Type := {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A
  let χ (t : A) (u : V) (β : skewAdjoint A) : 𝔰.BesselIndex → A :=
    inclMatrix A (floorIndexEnum a) *ᵥ flatChart (upperGram (T := T) (a + 1)) 0 ((t, u), β)
  set d : ℕ := 𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)) with hd
  -- both integrals are iterated integrals over `t`, the higher floors and the skew elements
  have h_floor : ∫⁻ v, Φ v ∂(F.floorMeasure a.castSucc).map (orbitPoint a.castSucc) =
      ∫⁻ t : A, modulus t ^ d * ∫⁻ u : V, ∫⁻ β : skewAdjoint A,
        Φ (orbitPoint a.castSucc ((floorWeyl a t : T.G)⁻¹ * heisenbergElem a (u, β)))
          ∂P.skewMeasure := by
    simp (disch := fun_prop) only [floorMeasure, Fin.val_castSucc, Fin.is_lt, ↓reduceIte, mconv,
      heisenbergMeasure, ↓reduceDIte, lintegral_map, lintegral_prod, hd]
    rw [weylLaw, lintegral_map (by fun_prop) (by fun_prop),
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
    rfl
  have h_quadric : ∫⁻ v, Φ v ∂F.floorQuadricMeasure a.castSucc =
      ∫⁻ t : A, ∫⁻ u : V, ∫⁻ β : skewAdjoint A, Φ (χ t u β) ∂P.skewMeasure := by
    rw [floorQuadricMeasure_castSucc_eq_map]
    simp (disch := fun_prop) only [lintegral_map, volume_eq_prod, lintegral_prod, V, χ]
    rw [lintegral_prod _ (by fun_prop)]
  rw [h_floor, h_quadric]
  refine lintegral_congr_of_ae_imp ae_isUnit ?_
  rintro _ ⟨t, rfl⟩
  calc _ = modulus t.val ^ d *
        ∫⁻ u : V, ∫⁻ β : skewAdjoint A, Φ (χ t (t.val • u) β) ∂P.skewMeasure := by
        -- `orbitPoint` inverts, and the inverse of `heisenbergElem a (u, β)` has parameters
        -- `(-u, c - β)` with `c` independent of `β`; both substitutions keep the measure
        rw [← lintegral_neg_eq_self]
        refine congrArg _ (lintegral_congr fun u ↦ ?_)
        let v : 𝔰.BesselIndex → A := inclMatrix A (↑) *ᵥ (-u)
        let c : skewAdjoint A := skewPart (element * star v ⬝ᵥ T.splitGram *ᵥ v)
        have h_point (β : skewAdjoint A) :
            orbitPoint a.castSucc ((floorWeyl a t.val : T.G)⁻¹ * heisenbergElem a (-u, β)) =
              χ t (t.val • u) (c - β) := by
          refine .trans ?_ (inclMatrix_mulVec_flatChart_eq_heisenbergElem_mulVec a t u (c - β)).symm
          rw [mulVec_mulVec]
          simp [orbitPoint, heisenbergElem_inv, c, v]
        simp only [h_point]
        exact lintegral_sub_left_eq_self (fun β : skewAdjoint A ↦ Φ (χ t (t.val • u) β)) c
    _ = ∫⁻ u : V, ∫⁻ β : skewAdjoint A, Φ (χ t u β) ∂P.skewMeasure := by
      -- scaling the higher floors by `t` has modulus `modulus t` to the power of their dimension
      have h_scale : (volume : Measure V).map (t.val • ·) = (modulus t.val ^ d)⁻¹ • volume := by
        simpa [↓card_subtype_succ_le_floorOf_eq, smul_mulVec] using
          map_mulVec_volume _ (t.val • (1 : Matrix {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} _ A))
            (by simp [t.isUnit.pow])
      rw [eq_comm, lintegral_eq_mul_lintegral_map h_scale (by simp) (by simp),
        lintegral_map (by fun_prop) (by fun_prop)]

/-- For a floor `b : Fin 𝔰.n`, that is b ≤ ϱ, and s in G^(b) = `floorGroup b`, the map σ ↦ s σ⁻¹ f,
with f the frame vector of floor b, carries the floor measure `F.floorMeasure b` to the quadric
measure `F.floorQuadricMeasure b`. -/
lemma measurePreserving_mulVec_orbitPoint {s : T.G} {F : PlaceData ι T m} (b : Fin 𝔰.n)
    (hs : s ∈ floorGroup b) :
    MeasurePreserving (s *ᵥ orbitPoint b ·) (F.floorMeasure b) (F.floorQuadricMeasure b) := by
  -- `s` preserves `floorVolume b` and the form, hence the disintegration along the form.
  let M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := s
  have h_incl : MeasurePreserving
      (fun v : {i : 𝔰.BesselIndex // b ≤ floorOf i} → A ↦ inclMatrix A Subtype.val *ᵥ v)
      volume (floorVolume b) :=
    (by fun_prop : Measurable _).measurePreserving volume
  -- extension by zero intertwines `M` with its block on the floors from `b` on
  have h_vol : MeasurePreserving (M *ᵥ ·) (floorVolume b) (floorVolume b) :=
    h_incl.of_semiconj (measurePreserving_floor_block_mulVec hs)
      (inclMatrix_mulVec_floor_block b.is_le hs) (by fun_prop)
  have h_form : Mᴴ * T.splitGram * M = T.splitGram := mem_unitaryGroupOf_iff.1 s.prop
  have h_inv : s⁻¹.val.val * M = 1 := s.val.inv_mul
  have h_image : IsDisintegration ((floorVolume b).map (M *ᵥ ·)) T.splitGram
      fun β : skewAdjoint A ↦ (F.floorQuadricMeasure b β).map (M *ᵥ ·) :=
    (F.isDisintegration_floorVolume b rfl).map h_form h_inv
  have h_same : IsDisintegration ((floorVolume b).map (M *ᵥ ·)) T.splitGram
      fun β : skewAdjoint A ↦ F.floorQuadricMeasure b β :=
    F.isDisintegration_floorVolume b h_vol.map_eq
  have h_quadric :
      MeasurePreserving (M *ᵥ ·) (F.floorQuadricMeasure b) (F.floorQuadricMeasure b) :=
    { measurable := h_vol.measurable, map_eq := h_image.unique h_same }
  exact h_quadric.comp (measurePreserving_orbitPoint b)

/-- The measure θ_l = `F.floorMeasure l` of floor l is concentrated on the group
G^(l) = `floorGroup l`: almost every `x` lies in `floorGroup l`. -/
lemma ae_floorMeasure_mem : ∀ᵐ x : T.G ∂F.floorMeasure l, x ∈ floorGroup l := by
  fun_cases floorMeasure
  · -- below floor ϱ, both factors are carried by G^(l)
    have h_heisenberg : ∀ᵐ x : T.G ∂heisenbergMeasure l, x ∈ floorGroup l :=
      ae_mem_floorUnipotent.mono fun x hx ↦ hx.1
    have h_weyl : ∀ᵐ x : T.G ∂weylLaw l, x ∈ floorGroup l := by
      simp [ae_map_iff measurable_floorWeyl.fun_inv.aemeasurable, measurableSet_floorGroup]
    exact ae_mem_mconv h_weyl h_heisenberg measurableSet_floorGroup
  -- floors ϱ and ϱ + 1 carry `F.topFloorMeasure` and `F.measureH`, the higher ones the Dirac
  -- measure at 1
  case case2 h_floor => simp [ae_topFloorMeasure_mem_floorGroup, h_floor]
  case case3 h_floor => simp [ae_measureH_mem_besselH, h_floor]
  case case4 => simp

/-- Congruence rule for integrals over floor `l`: since `F.floorMeasure l` is carried by the group
G^(l) = `floorGroup l`, the integrand may be changed outside G^(l). -/
@[congr]
lemma lintegral_floorMeasure_congr {μ : Measure T.G} (hμ : F.floorMeasure l = μ)
    (h_eq : ∀ σ ∈ floorGroup l, f σ = Φ σ) :
    lintegral (F.floorMeasure l) f = lintegral μ Φ := by
  rw [← hμ]
  exact lintegral_congr_of_ae_imp ae_floorMeasure_mem h_eq

/-- The measure of floor `𝔰.n = ϱ + 1` is the measure of H. -/
@[simp]
lemma floorMeasure_top : F.floorMeasure 𝔰.n = F.measureH := by simp [floorMeasure]

/-- The convolution θ_{ϱ+1} ∗ ⋯ ∗ θ_l of the floor measures from floor `l` on is the convolution
from floor `l + 1` on, convolved with θ_l = `F.floorMeasure l`. -/
lemma quotientMeasureFrom_eq_succ_mconv :
    F.quotientMeasureFrom l = F.quotientMeasureFrom (l + 1) ∗ₘ F.floorMeasure l := by
  obtain hl | hl : l < 𝔰.ϱ + 2 ∨ 𝔰.ϱ + 2 ≤ l := lt_or_ge l (𝔰.ϱ + 2)
  · rw [quotientMeasureFrom, show 𝔰.ϱ + 2 - l = 𝔰.ϱ + 2 - (l + 1) + 1 by lia, descConv]
  · -- all three measures are the Dirac measure at 1
    have h_dirac : F.floorMeasure l = dirac 1 := by grind [floorMeasure]
    rw [h_dirac, mconv_dirac_one, quotientMeasureFrom, quotientMeasureFrom,
      Nat.sub_eq_zero_of_le hl,
      Nat.sub_eq_zero_of_le (hl.trans l.le_succ), descConv, descConv]

/-- Let l < ϱ = `𝔰.ϱ`, the number of hyperbolic pairs, and let θ_a = `F.floorMeasure a`. Then
θ_{l+i} ∗ ⋯ ∗ θ_l equals `weylLaw l` ∗ (θ_{l+i} ∗ ⋯ ∗ θ_{l+1}) ∗ η_l. Here `weylLaw l` is carried by
the inverses of the elements `floorWeyl l c` that swap the lines of e_l and e*_l, and
η_l = `heisenbergMeasure l` is the Haar measure of the Heisenberg group attached to e_l. -/
lemma descConv_floorMeasure_succ {F : PlaceData ι T m} (h : l < 𝔰.ϱ) :
    descConv F.floorMeasure l (i + 1) =
      (weylLaw l ∗ₘ descConv F.floorMeasure (l + 1) i) ∗ₘ heisenbergMeasure l := by
  -- `weylLaw l` commutes with the higher floors, which are carried by `G^(l+1)`
  have h_comm :
      descConv F.floorMeasure (l + 1) i ∗ₘ weylLaw l =
        weylLaw l ∗ₘ descConv F.floorMeasure (l + 1) i := by
    refine mconv_comm_of_ae ((ae_descConv_mem ae_floorMeasure_mem).mono fun s hs ↦ ?_)
    have h_commute (c : A) : (floorWeyl l c : T.G)⁻¹ * s = s * (floorWeyl l c)⁻¹ :=
      (commute_weylOn (by lia) hs).inv_left.eq
    simp (disch := fun_prop) [dirac_mconv, mconv_dirac, Measure.map_map, comp_def, h_commute]
  rw [descConv, floorMeasure, ite_eq_left h, ← mconv_assoc, h_comm]

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermitianUnit T.splitGram] in
/-- Let j < ϱ and let w_j(c) = `floorWeyl j c` be the Weyl element of floor j with unit parameter
c. The diagonal elements `weylRatio (j + 1) p q` and `weylRatio j p q`, with entries p_a / q_a at
the e_a, differ by a factor that takes w_j((p_j / q_j) c)⁻¹ to w_j(c)⁻¹. -/
lemma weylRatio_succ_mul_floorWeyl_inv (hj : j < 𝔰.ϱ) (p q : ℕ → Aˣ) (c : Aˣ) :
    weylRatio (j + 1) p q * (floorWeyl j ((p j / q j).val * c : A))⁻¹ =
      (weylRatio j p q * (floorWeyl j (c : A))⁻¹ : T.G) := by
  -- Compare the entries: both sides are a diagonal matrix times a monomial matrix. The `simp` call
  -- writes the entries as case distinctions on the floor and level of the two indices.
  ext a b
  simp [coe_weylRatio, floorWeyl, weylOn, division_def, Ring.mul_inverse_rev]
  grind [Units.inv_mul, =_ star_mul, oppositeIndex_involutive_and_floorOf_level]

/-- Let j ≤ ϱ = `𝔰.ϱ`, the number of hyperbolic pairs e_a, e*_a, and let `weylRatio j p q` be the
diagonal isometry that scales e_a by p_a / q_a for a < j. Left translation by it multiplies the
integral of a measurable Φ ≥ 0 for `F.quotientMeasureFrom 0`, the convolution of all the measures
`F.floorMeasure a`, by the product over a < j of |p_a / q_a| ^ (k + 2 (ϱ - a)). Here k = `𝔰.k` and
|·| is the `modulus` of the ring `A`, the factor by which a unit scales its volume. -/
lemma lintegral_weylRatio_mul {Φ : T.G → ℝ≥0∞} {F : PlaceData ι T m} {p q : ℕ → Aˣ} (hj : j ≤ 𝔰.ϱ)
    (hΦ : Measurable Φ) :
    ∫⁻ x : T.G, Φ (weylRatio j p q * x) ∂F.quotientMeasureFrom 0 =
      (∏ a ∈ Finset.range j, modulus (p a / q a).val ^ (𝔰.k + 2 * (𝔰.ϱ - a))) *
        ∫⁻ x : T.G, Φ x ∂F.quotientMeasureFrom 0 := by
  induction j with
  | zero => simp [weylRatio]
  | succ j ih =>
    -- split off the Weyl element of floor `j`; `μ` is the rest of the convolution
    let μ : Measure T.G :=
      descConv F.floorMeasure (j + 1) (𝔰.ϱ - j + 1) ∗ₘ heisenbergMeasure j ∗ₘ
        descConv F.floorMeasure 0 j
    have hμ : F.quotientMeasureFrom 0 = weylLaw j ∗ₘ μ := by
      rw [quotientMeasureFrom, show 𝔰.ϱ + 2 - 0 = j + (𝔰.ϱ - j + 1 + 1) by lia,
        descConv_add, zero_add, descConv_floorMeasure_succ hj, mconv_assoc, mconv_assoc]
    -- integrate first over the parameter `c` of that Weyl element
    have h_split (Ψ : T.G → ℝ≥0∞) (hΨ : Measurable Ψ) :
        ∫⁻ x : T.G, Ψ x ∂F.quotientMeasureFrom 0 =
          ∫⁻ c : A, P.modulus c ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (j + 1))) *
            ∫⁻ y : T.G, Ψ ((floorWeyl j c)⁻¹ * y) ∂μ := by
      rw [hμ, lintegral_mconv hΨ, lintegral_map (by fun_prop) (by fun_prop),
        lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
      simp only [Pi.mul_apply]
    -- rescaling the parameter of the Weyl element by `r` absorbs the new factor
    set r : Aˣ := p j / q j with hr
    have h_shift (c : Aˣ) :
        weylRatio (j + 1) p q * (floorWeyl j (r * c : A))⁻¹ =
          (weylRatio j p q * (floorWeyl j (c : A))⁻¹ : T.G) :=
      weylRatio_succ_mul_floorWeyl_inv hj p q c
    have h_exp : 𝔰.k + 2 * (𝔰.ϱ - j) = 𝔰.k + 1 + 2 * (𝔰.ϱ - (j + 1)) + 1 := by lia
    have hΦ_shift (n : ℕ) : Measurable fun x : T.G ↦ Φ (weylRatio n p q * x) := by fun_prop
    -- by induction it suffices to compare the translations by the elements of length `j + 1`, `j`
    rw [Finset.prod_range_succ_comm, ← hr, mul_assoc, ← ih (by lia), h_split _ (hΦ_shift (j + 1)),
      h_split _ (hΦ_shift j)]
    -- substitute `r * c` for `c` on the left, which costs the factor `modulus r`
    rw [lintegral_eq_mul_lintegral_map (map_mul_volume r) (modulus_ne_zero r) (modulus_ne_top r),
      lintegral_map (by fun_prop) (by fun_prop), ← lintegral_const_mul _ (by fun_prop),
      ← lintegral_const_mul _ (by fun_prop)]
    -- almost every parameter is a unit, where `h_shift` applies
    refine lintegral_congr_ae (ae_isUnit.mono ?_)
    rintro _ ⟨c, rfl⟩
    simp [h_exp, h_shift, mul_pow, ← mul_assoc, pow_succ']

/-- Let S be a subgroup that contains G^(l) = `floorGroup l`, the isometries fixing the basis
vectors of floor below l, and let R^(l) = `partialUnitriangularGroup l` be the group of the
isometries unitriangular on the first l frame vectors. If f ≥ 0 is measurable and left invariant
under R^(l+1) ∩ S, its integral for the measure `F.floorMeasure l` on G^(l) does not change under
right translation by an element s of R^(l) ∩ S. -/
lemma lintegral_floorMeasure_mul_right {s : T.G} {S : Subgroup T.G} {f : T.G → ℝ≥0∞}
    {F : PlaceData ι T m} (hS : floorGroup l ≤ S)
    (hf_inv : (partialUnitriangularGroup (l + 1) ⊓ S).FixesLeft f)
    (hs : s ∈ partialUnitriangularGroup l ⊓ S) (hf : Measurable f := by fun_prop) :
    ∫⁻ x : T.G, f (x * s) ∂F.floorMeasure l = ∫⁻ x : T.G, f x ∂F.floorMeasure l := by
  obtain ⟨hs_unitri, hsS⟩ := Subgroup.mem_inf.mp hs
  obtain ⟨γ, hγ, ν, hν, rfl⟩ := exists_floorGroup_mul_unipotentBelow hs_unitri
  -- The factor ν drops out: x γ ν = ((x γ) ν (x γ)⁻¹) x γ, and f is invariant under the conjugate.
  have h_drop (x : T.G) (hx : x ∈ floorGroup l) : f (x * (γ * ν)) = f (x * γ) := by
    have h_unitri : x * γ * ν * (x * γ)⁻¹ ∈ partialUnitriangularGroup (l + 1) :=
      unipotentBelow_le_partialUnitriangularGroup (conj_mem_unipotentBelow (mul_mem hx hγ) hν)
    have h_mem : x * γ * ν * (x * γ)⁻¹ ∈ S := by
      rw [mul_assoc x γ]
      exact mul_mem (mul_mem (hS hx) hsS) (inv_mem (hS (mul_mem hx hγ)))
    calc f (x * (γ * ν)) = f (x * γ * ν * (x * γ)⁻¹ * (x * γ)) := by
          rw [inv_mul_cancel_right, mul_assoc]
      _ = f (x * γ) := hf_inv _ ⟨h_unitri, h_mem⟩ (x * γ)
  rw [lintegral_floorMeasure_congr rfl h_drop]
  obtain h | rfl | h := lt_trichotomy l 𝔰.n
  · -- On G^(l), `f = f₀ ∘ orbitPoint b`; the points of `x` and of `x γ` differ by the action of
    -- `γ⁻¹`, and both maps carry the floor measure to the same quadric measure.
    let b : Fin 𝔰.n := ⟨l, h⟩
    obtain ⟨f₀, hf₀, hf_eq⟩ : ∃ f₀ : (𝔰.BesselIndex → A) → ℝ≥0∞,
        Measurable f₀ ∧ ∀ x ∈ floorGroup l, f x = f₀ (orbitPoint b x) :=
      exists_factor_orbitPoint b hf fun t ⟨ht_unitri, ht⟩ ↦ hf_inv t ⟨ht_unitri, hS ht⟩
    calc ∫⁻ x : T.G, f (x * γ) ∂F.floorMeasure l
        = ∫⁻ x : T.G, f₀ ((γ⁻¹ : T.G) *ᵥ orbitPoint b x) ∂F.floorMeasure l := by
          refine lintegral_floorMeasure_congr rfl fun x hx ↦ ?_
          rw [hf_eq _ (mul_mem hx hγ), orbitPoint, orbitPoint, mulVec_mulVec, _root_.mul_inv_rev,
            Subgroup.coe_mul, Units.val_mul]
      _ = ∫⁻ v : 𝔰.BesselIndex → A, f₀ v ∂F.floorQuadricMeasure b :=
          (measurePreserving_mulVec_orbitPoint b (inv_mem hγ)).lintegral_comp hf₀
      _ = ∫⁻ x : T.G, f₀ (orbitPoint b x) ∂F.floorMeasure l :=
          ((measurePreserving_orbitPoint b).lintegral_comp hf₀).symm
      _ = ∫⁻ x : T.G, f x ∂F.floorMeasure l := (lintegral_floorMeasure_congr rfl hf_eq).symm
  · -- on the last floor G^(l) is H, under which `F.measureH` is right invariant
    rw [floorMeasure_top, ← lintegral_mconv_dirac, F.measureH_mconv_dirac (by simpa using hγ)]
  · -- above the last floor the group G^(l) is trivial
    have hγ_one : γ = 1 := by simpa [floorGroup_eq_bot h] using hγ
    simp [hγ_one]

/-- The convolution `F.partialGroupMeasure l i` of the Heisenberg and floor measures of the `i`
floors from `l` on is carried by G^(l) = `floorGroup l`, the isometries fixing the basis vectors of
floor below `l`. -/
lemma ae_partialGroupMeasure_mem {F : PlaceData ι T m} :
    ∀ᵐ x : T.G ∂F.partialGroupMeasure l i, x ∈ floorGroup l := by
  have h_heisenberg {a : ℕ} : ∀ᵐ x : T.G ∂heisenbergMeasure a, x ∈ floorGroup a :=
    ae_mem_floorUnipotent.mono fun x hx ↦ hx.1
  exact ae_descConv_mem (ae_mem_mconv h_heisenberg ae_floorMeasure_mem)

/-- Let η_a = `heisenbergMeasure a` and θ_a = `F.floorMeasure a`. If l + i = ϱ + 2, the convolution
(η_{ϱ+1}∗θ_{ϱ+1}) ∗ ⋯ ∗ (η_l∗θ_l) of i factors is invariant under right translation by every s in
G^(l) = `floorGroup l`. -/
lemma partialGroupMeasure_mconv_dirac {s : T.G} {F : PlaceData ι T m} (h : l + i = 𝔰.ϱ + 2)
    (hs : s ∈ floorGroup l) :
    F.partialGroupMeasure l i ∗ₘ dirac s = F.partialGroupMeasure l i := by
  induction i generalizing l s with
  | zero =>
    rw [floorGroup_eq_bot (by lia)] at hs
    rw [hs, mconv_dirac_one]
  | succ i ih =>
    -- Write the measure as `ρ ∗ₘ F.floorMeasure l` and apply `lintegral_floorMeasure_mul_right` to
    -- the `ρ`-average of a test function.
    let ρ : Measure T.G := F.partialGroupMeasure (l + 1) i ∗ₘ heisenbergMeasure l
    have h_split : F.partialGroupMeasure l (i + 1) = ρ ∗ₘ F.floorMeasure l := by
      rw [partialGroupMeasure, descConv, mconv_assoc]
    -- An element `t` of `R^(l+1) ∩ G^(l)` is `u * n` with `u` in `G^(l+1)`, absorbed by induction,
    -- and `n` in the Heisenberg group of floor `l`, absorbed by `heisenbergMeasure l`.
    have hρ_right (t : T.G) (ht : t ∈ partialUnitriangularGroup (l + 1) ⊓ floorGroup l) :
        ρ ∗ₘ dirac t = ρ := by
      obtain ⟨u, hu, n, hn, rfl⟩ := exists_floorGroup_mul_floorUnipotent ht
      dsimp only [ρ]
      rw [← dirac_mconv_dirac, ← mconv_assoc, mconv_assoc (F.partialGroupMeasure (l + 1) i),
        ← dirac_mconv_heisenbergMeasure_comm hu, ← mconv_assoc, ih (by lia) hu, mconv_assoc,
        (heisenbergMeasure_mconv_dirac hn).1]
    refine ext_of_lintegral _ fun f hf ↦ ?_
    let avg (y : T.G) : ℝ≥0∞ := ∫⁻ x : T.G, f (x * y) ∂ρ
    have h_inv : (partialUnitriangularGroup (l + 1) ⊓ floorGroup l).FixesLeft avg :=
      fun t ht g ↦ by
        simp only [avg, ← lintegral_mconv_dirac, ← dirac_mconv_dirac, ← mconv_assoc, hρ_right t ht]
    rw [lintegral_mconv_dirac, h_split, lintegral_mconv_symm (by fun_prop), lintegral_mconv_symm hf]
    simpa only [avg, mul_assoc] using lintegral_floorMeasure_mul_right le_rfl h_inv
      ⟨mem_partialUnitriangularGroup_of_mem_floorGroup hs, hs⟩

/-- The group measure, the convolution over all floors, is right invariant. -/
instance isMulRightInvariant_groupMeasure : F.groupMeasure.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    -- G^(0) is the whole group
    have hg : g ∈ floorGroup 0 := by simp
    rw [← mconv_dirac, groupMeasure, partialGroupMeasure_mconv_dirac (zero_add (𝔰.ϱ + 2)) hg]

/-- Let η_a = `heisenbergMeasure a` and θ_a = `F.floorMeasure a`. The measure
`F.partialGroupMeasure 0 j` = (η_{j−1}∗θ_{j−1}) ∗ ⋯ ∗ (η₀∗θ₀) equals the ascending convolution η₀ ∗
⋯ ∗ η_{j−1} convolved with the descending convolution θ_{j−1} ∗ ⋯ ∗ θ₀. -/
lemma partialGroupMeasure_zero_eq {F : PlaceData ι T m} :
    F.partialGroupMeasure 0 j = ascConv heisenbergMeasure j ∗ₘ descConv F.floorMeasure 0 j := by
  induction j with
  | zero => simp [descConv, ascConv]
  | succ j ih =>
    -- `F.floorMeasure j` is carried by `floorGroup j`, so it commutes with the lower
    -- `heisenbergMeasure`.
    have h_comm :
        F.floorMeasure j ∗ₘ ascConv heisenbergMeasure j =
          ascConv heisenbergMeasure j ∗ₘ F.floorMeasure j :=
      mconv_comm_of_ae (F.ae_floorMeasure_mem.mono ascConv_heisenbergMeasure_dirac_comm)
    calc F.partialGroupMeasure 0 (j + 1)
        = (heisenbergMeasure j ∗ₘ F.floorMeasure j) ∗ₘ F.partialGroupMeasure 0 j := by
          simp only [partialGroupMeasure, descConv_succ]
      _ = heisenbergMeasure j ∗ₘ ((F.floorMeasure j ∗ₘ ascConv heisenbergMeasure j) ∗ₘ
            descConv F.floorMeasure 0 j) := by
          simp only [ih, mconv_assoc]
      _ = ascConv heisenbergMeasure (j + 1) ∗ₘ descConv F.floorMeasure 0 (j + 1) := by
          simp only [h_comm, descConv_succ, ascConv_heisenbergMeasure_succ, mconv_assoc]

/-- The measure θ_l = `F.floorMeasure l` of every floor of the place datum `F` is non-zero. -/
lemma floorMeasure_ne_zero {F : PlaceData ι T m} (l : ℕ) : F.floorMeasure l ≠ 0 := by
  obtain hl | rfl | hl : l < 𝔰.n ∨ l = 𝔰.n ∨ 𝔰.n < l := lt_trichotomy l 𝔰.n
  · -- the measure maps onto a non-zero quadric measure
    have h_map := measurePreserving_orbitPoint (F := F) ⟨l, hl⟩
    have h_quadric : F.floorQuadricMeasure ⟨l, hl⟩ ≠ 0 := by
      simp (disch := fun_prop) [NeZero.ne]
    exact (Measure.map_ne_zero_iff h_map.aemeasurable).1 (h_map.map_eq ▸ h_quadric)
  · rw [floorMeasure_top]
    exact NeZero.ne F.measureH
  · have h_dirac : F.floorMeasure l = dirac 1 := by grind [floorMeasure]
    rw [h_dirac]
    exact dirac_ne_zero

/-- The measure `F.partialGroupMeasure l i` of the place data `F` is non-zero. It is the convolution
of the measures `heisenbergMeasure a` and `F.floorMeasure a` over the `i` floors l ≤ a < l + i.
Floor a < ϱ is the hyperbolic pair e_a, e*_a, floor ϱ is z, and floor ϱ + 1 holds the other middle
vectors. -/
lemma partialGroupMeasure_ne_zero {F : PlaceData ι T m} : F.partialGroupMeasure l i ≠ 0 := by
  have h_heis (a : ℕ) : (heisenbergMeasure a : Measure T.G) ≠ 0 := by
    obtain ha | ha : a < 𝔰.ϱ ∨ 𝔰.ϱ ≤ a := lt_or_ge a 𝔰.ϱ
    · -- it is a factor of `F.floorMeasure a`
      intro h_zero
      apply F.floorMeasure_ne_zero a
      rw [floorMeasure, ite_eq_left ha, h_zero, mconv_zero]
    · rw [heisenbergMeasure_eq_dirac_one ha]
      exact dirac_ne_zero
  -- the total mass of a convolution is the product of the total masses
  have h_univ (μ μ' : Measure T.G) [SFinite μ] [SFinite μ'] :
      (μ ∗ₘ μ') Set.univ = μ Set.univ * μ' Set.univ := by
    simp [mconv_apply_eq_lintegral .univ]
  rw [← measure_univ_ne_zero]
  induction i generalizing l with
  | zero => simp [descConv]
  | succ i ih =>
    have h_mass : F.partialGroupMeasure l (i + 1) Set.univ = F.partialGroupMeasure (l + 1) i
      Set.univ *
        (heisenbergMeasure (T := T) l Set.univ * F.floorMeasure l Set.univ) := by
      rw [partialGroupMeasure, descConv, h_univ, h_univ]
    rw [h_mass]
    refine mul_ne_zero ih ?_
    simp [h_heis, floorMeasure_ne_zero]

/-- Let the measure `F.groupMeasure` on the unitary group, the convolution over all floors, be a
Haar measure and equal `ρ ∗ ν`, with `ρ` carried by the subgroup `S`, right invariant under `S` and
commuting with the unit mass at `s`. Then left translation by `s` does not change the `ν`-integral
of a measurable `Φ ≥ 0` that is invariant under left translation by `S` (`S.FixesLeft Φ`). -/
lemma lintegral_mul_left_eq_of_factor {ν ρ : Measure T.G} [SFinite ν] [SFinite ρ] {s : T.G}
    {S : Subgroup T.G} {Φ : T.G → ℝ≥0∞} {F : PlaceData ι T m} [F.groupMeasure.IsHaarMeasure]
    (h_factor : F.groupMeasure = ρ ∗ₘ ν) (hρ_mem : ∀ᵐ y : T.G ∂ρ, y ∈ S)
    (hρ_right : ∀ t ∈ S, ρ ∗ₘ dirac t = ρ) (hs : dirac s ∗ₘ ρ = ρ ∗ₘ dirac s) (hΦ : Measurable Φ)
    (hΦ_inv : S.FixesLeft Φ) :
    ∫⁻ g : T.G, Φ (s * g) ∂ν = lintegral ν Φ := by
  -- Take `f > 0` integrable for `F.groupMeasure`. For any `μ` with `F.groupMeasure = ρ ∗ₘ μ`, the
  -- integral of `Φ` for `μ` is the integral for `F.groupMeasure` of `Φ * f` divided by the
  -- `ρ`-average of `f`, an expression that does not mention `μ`.
  obtain ⟨f, hf_pos, hf, hf_int⟩ :=
    exists_pos_lintegral_lt_of_sigmaFinite F.groupMeasure top_ne_zero
  let avg (g : T.G) : ℝ≥0∞ := ∫⁻ y : T.G, f (y * g) ∂ρ
  have h_avg (y : T.G) (hy : y ∈ S) (g : T.G) : avg (y * g) = avg g :=
    calc ∫⁻ x : T.G, f (x * (y * g)) ∂ρ
        = ∫⁻ x : T.G, f (x * g) ∂(ρ ∗ₘ dirac y) := by
          rw [lintegral_mconv_dirac]
          simp only [mul_assoc]
      _ = avg g := by rw [hρ_right y hy]
  have hρ : ρ ≠ 0 := by
    rintro rfl
    exact F.partialGroupMeasure_ne_zero (h_factor.trans (zero_mconv ν))
  have h_avg_ne (g : T.G) : avg g ≠ 0 := by
    have hf_ne (x : T.G) : f x ≠ 0 := (hf_pos x).ne'
    simpa (disch := fun_prop) [avg, EventuallyEq, hf_ne] using hρ
  have h_formula (μ : Measure T.G) [SFinite μ] (hμ : F.groupMeasure = ρ ∗ₘ μ) :
      ∫⁻ x : T.G, Φ x / avg x * f x ∂F.groupMeasure = lintegral μ Φ := by
    rw [hμ, lintegral_mconv_symm (by fun_prop)] at hf_int ⊢
    have h_avg_lt : ∀ᵐ g : T.G ∂μ, avg g < ∞ := ae_lt_top (by fun_prop) hf_int.ne
    refine lintegral_congr_ae (h_avg_lt.mono fun g hg ↦ ?_)
    calc ∫⁻ y : T.G, Φ (y * g) / avg (y * g) * f (y * g) ∂ρ
        = ∫⁻ y : T.G, Φ g / avg g * f (y * g) ∂ρ :=
          lintegral_congr_ae (hρ_mem.mono fun y hy ↦ by simp only [hΦ_inv y hy g, h_avg y hy])
      _ = Φ g / avg g * avg g := lintegral_const_mul _ (by fun_prop)
      _ = Φ g := ENNReal.div_mul_cancel (h_avg_ne g) hg.ne
  -- the translate of `ν` by `s` is such a measure too, as `F.groupMeasure` is left invariant
  have h_translate : F.groupMeasure = ρ ∗ₘ (dirac s ∗ₘ ν) := by
    rw [← mconv_assoc, ← hs, mconv_assoc, ← h_factor, dirac_mconv, map_mul_left_eq_self]
  rw [← lintegral_dirac_mconv, ← h_formula _ h_translate, h_formula ν h_factor]

/-- Let `F.groupMeasure`, the convolution of the measures `heisenbergMeasure a` and
`F.floorMeasure a` over all ϱ + 2 floors a (ϱ = `𝔰.ϱ`), be a Haar measure. Let j ≤ ϱ + 2 and let `p`
be a sequence of units. Let w be the inverse of the Weyl element `weylElem j p`, which sends e_a to
p_a e*_a and e*_a to e_a / p̄_a for a < j and fixes the other basis vectors. If Φ ≥ 0 is measurable
and left invariant under G^(j) = `floorGroup j`, the isometries fixing the basis vectors of floor
below j, then Φ(w g) and Φ(g) have the same integral for the convolution `F.partialGroupMeasure 0 j`
over the floors below j. -/
lemma lintegral_partialGroupMeasure_weylElem_inv_mul {Φ : T.G → ℝ≥0∞} {F : PlaceData ι T m}
    [F.groupMeasure.IsHaarMeasure] (p : ℕ → Aˣ) (hΦ : Measurable Φ)
    (hΦ_inv : (floorGroup j).FixesLeft Φ) (hj : j ≤ 𝔰.ϱ + 2 := by lia) :
    ∫⁻ g : T.G, Φ ((weylElem j p)⁻¹ * g) ∂F.partialGroupMeasure 0 j =
      ∫⁻ g : T.G, Φ g ∂F.partialGroupMeasure 0 j := by
  -- Apply `lintegral_mul_left_eq_of_factor` to the floors `j, …, ϱ + 1` of `F.groupMeasure`; they
  -- are carried by `floorGroup j`, which commutes with `weylElem j p`.
  obtain ⟨i, hij⟩ : ∃ i : ℕ, 𝔰.ϱ + 2 = j + i := Nat.exists_eq_add_of_le hj
  have hM : F.groupMeasure = F.partialGroupMeasure j i ∗ₘ F.partialGroupMeasure 0 j := by
    rw [groupMeasure, hij, partialGroupMeasure, descConv_add, zero_add]
  have h_comm : F.partialGroupMeasure j i ∗ₘ dirac (weylElem j p)⁻¹ =
      dirac (weylElem j p)⁻¹ ∗ₘ F.partialGroupMeasure j i := by
    refine mconv_comm_of_ae (ae_partialGroupMeasure_mem.mono fun s hs ↦ ?_)
    have h_commute : (weylElem j p : T.G)⁻¹ * s = s * (weylElem j p)⁻¹ :=
      (commute_weylElem hs).inv_left.eq
    rw [dirac_mconv_dirac, dirac_mconv_dirac, h_commute]
  have h_right (t : T.G) (ht : t ∈ floorGroup j) :
      F.partialGroupMeasure j i ∗ₘ dirac t = F.partialGroupMeasure j i :=
    partialGroupMeasure_mconv_dirac hij.symm ht
  exact lintegral_mul_left_eq_of_factor hM ae_partialGroupMeasure_mem h_right h_comm.symm hΦ hΦ_inv

end PlaceData

end LevelGauge

end New.Floors

end
end
end

/-!
# The scale, near points and partial correlations

The structure `New.Floors.Gauge` collects the few facts about a place that the estimates use. A
correlation is a kernel on pairs of points with a character law; integrating it over the floors from
`l` on gives the partial correlations. The letters G^(l), R^(l), U_(<l) are those of the head of
`New.Spanning.Frames.Lengths`, and K, M those of `New.Spanning.Frames.Levels`.

## Main definitions and results

* `New.Floors.Gauge`, `New.Floors.Gauge.positionsOfSize`: a scale with its constant Λ =
  `Γ.loss`, and the close positions.
* `New.Floors.PlaceData.IsPairingKernel`, `New.Floors.PlaceData.partialCorrelation`: kernels and
  partial correlations.
* `New.Floors.PlaceData.weightedSquare`, `New.Floors.PlaceData.weightedSquareIntegral`: the second
  moments of one frame.
* `New.Floors.Gauge.isBalanced_of_isNear`: near points are balanced.

Notions from other files:
* `New.Floors.PlaceData`: the data of a place, among them the level M = `F.levelUnit`, the compact
  set K = `F.boxSet` of the unitary group G = `T.G`, and the set `F.positions` of the elements by
  which the second point of a pair differs from the first.
* `New.Floors.PlaceData.IsNear`: g is near at j if R^(j) g meets K, for R^(j) =
  `partialUnitriangularGroup j`.
* `New.Floors.PlaceData.floorMeasure`, `New.Floors.PlaceData.quotientMeasureFrom`: the measure of
  floor l on G^(l) = `floorGroup l`, and the convolution of the measures of the floors from l on.
* `New.Floors.Size`: a filtration `ofSize i` of the numbers by size; a vector or a matrix has size i
  if all its entries have.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

@[expose] public section

noncomputable section

namespace New.Floors

section LevelGauge

open Matrix MeasureTheory Measure BesselIndex ENNReal Fintype FloorGroups Place TraceOne Function
  Filter

variable {A : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {ι : Type} [Fintype ι] [DecidableEq ι] {𝔰 : Shape} {T : 𝔰.Form A} {m : ℕ}
  [IsHermitianUnit T.splitGram] (F : PlaceData ι T m)

namespace PlaceData

variable (j : ℕ) (k : T.G → T.G → ℂ) (w x g y : T.G) (K : ℝ≥0∞)

/-- For every g, the integral of c(σ g) for the measure of floor j, over the σ with σ g near at
j + 1 (`IsNear`), is at most the bound `K` (a number, not the compact set `F.boxSet`). -/
def FloorMassLe (c : T.G → ℝ≥0∞) : Prop :=
  ∀ g : T.G,
    ∫⁻ σ : T.G in {σ : T.G | F.IsNear (j + 1) (σ * g)}, c (σ * g) ∂F.floorMeasure j ≤ K

/-- The correlation from floor j on: the integral of k(x g, x y) in x for `F.quotientMeasureFrom j`,
the measure on G that represents the quotient (U ∩ G^(j)) ∖ G^(j), where U = `besselU`. -/
def partialCorrelation : ℂ := ∫ x : T.G, k (x * g) (x * y) ∂F.quotientMeasureFrom j

/-- The rules for a kernel k on G × G and an element w that commutes with G^(j). They hold for the
correlation k(g, y) = ⟪W g, W (w y)⟫ of a Bessel function W. -/
structure IsPairingKernel : Prop where
  /-- The kernel is jointly measurable. -/
  measurable : Measurable ↿k
  /-- For n, n' in U_(<l) = `unipotentBelow l`, putting n before g and n' before y multiplies the
  correlation from floor l + 1 on by ψ((σ₀(w n' w⁻¹) - σ₀(n)) / M), where σ₀ = `simpleRootSum`, ψ is
  the additive character of the place and M = `F.levelUnit` is the level. -/
  equivariance : ∀ {l : ℕ} {n n' : T.G}, n ∈ unipotentBelow l → n' ∈ unipotentBelow l → ∀ g y : T.G,
    F.partialCorrelation (l + 1) k (n * g) (n' * y) =
      ψ (F.levelUnit⁻¹.val * (simpleRootSum (w * n' * w⁻¹) - simpleRootSum n)) *
        F.partialCorrelation (l + 1) k g y
  /-- The element w commutes with G^(j). -/
  conj_eq_self : ∀ s ∈ floorGroup j, w * s * w⁻¹ = s
  /-- The integral of |k(x g, x y)| over the floors from l on has a finite bound that does not
  depend on g and y. -/
  exists_lintegral_le (l : ℕ) :
    ∃ c < ∞, ∀ g y : T.G, ∫⁻ x : T.G, ‖k (x * g) (x * y)‖ₑ ∂F.quotientMeasureFrom l ≤ c
  /-- If the correlation of g and y from floor l on is not zero, then g is near at l. -/
  isNear_of_partialCorrelation_ne_zero : ∀ {l : ℕ} {g y : T.G},
    F.partialCorrelation l k g y ≠ 0 → F.IsNear l g

/-- The function of z that is the inverse of the weight `F.depthWeight j z x` of length j at the
points z and z x if z is near at j, and 0 elsewhere. -/
def invDepthWeight : T.G → ℝ≥0∞ :=
  {z : T.G | F.IsNear j z}.indicator fun z : T.G ↦ (F.depthWeight j z x)⁻¹

/-- The integral over the σ in floor j of the modulus of the correlation of σ g and σ y from floor
j + 1 on. -/
def pivotL1Norm : ℝ≥0∞ :=
  ∫⁻ σ : T.G, ‖F.partialCorrelation (j + 1) k (σ * g) (σ * y)‖ₑ ∂F.floorMeasure j

/-- The weight of length j times the squared modulus of the correlation from floor j + 1 on, both
taken at the points g and g x. -/
abbrev weightedSquare : ℝ≥0∞ := F.depthWeight j g x * ‖F.partialCorrelation (j + 1) k g (g * x)‖ₑ ^
  2

/-- The function b_j(g) = ∫ (a_j + b_{j+1})(σ g) dθ_j(σ) for j < n = `𝔰.n`, and 0 for j ≥ n, where
a_j is `New.Floors.PlaceData.weightedSquare` at the position x and θ_j = `F.floorMeasure j`. -/
def weightedSquareSum (x : T.G) (j : ℕ) (g : T.G) : ℝ≥0∞ :=
  if j < 𝔰.n then
    ∫⁻ σ : T.G,
      F.weightedSquare j k x (σ * g) + weightedSquareSum x (j + 1) (σ * g) ∂F.floorMeasure j
  else
    0

/-- The integral of `F.weightedSquareSum k x j`, the sum of the weighted squared correlations from
floor j on, over the floors below j. -/
def weightedSquareIntegral : ℝ≥0∞ := ∫⁻ g : T.G,
  F.weightedSquareSum k x j g ∂descConv F.floorMeasure 0 j

end PlaceData

/-- The data through which a gauge is used at either kind of place, for the data F: sizes of numbers
for one scale element, together with a number Λ = `loss` whose powers bound moduli and volumes, also
those of the products with close pairs. It is not the length itself: lengths at a point are bounded
by `New.Floors.Size.LengthLeAt`, and at a real place the length is `lengthAt`. The last two fields
are the facts that are proved separately at a real place and at the finite places. -/
structure Gauge extends Size T where
  /-- The constant Λ of the scale: losses are its powers. -/
  loss : ℝ≥0∞
  /-- The set of numbers of size j is compact. -/
  isCompact_ofSize (j : ℕ) : IsCompact (ofSize j)
  /-- Λ is at least 2. -/
  two_le_loss : 2 ≤ loss
  /-- Λ is finite. -/
  loss_ne_top : loss ≠ ∞
  /-- The number m of further hyperbolic pairs is at most 9 n. -/
  pairs_le : m ≤ 9 * 𝔰.n
  /-- The constant `P.kernelBound` in Plancherel's formula is at least 1. -/
  one_le_kernelBound : 1 ≤ P.kernelBound
  /-- The level M has size 1. -/
  levelUnit_mem_ofSize : (F.levelUnit : A) ∈ ofSize 1
  /-- The basis has size 1. -/
  hasMatrixSize_basisMatrix : toSize.HasMatrixSize 1 F.basisMatrix
  /-- The element of trace one, divided by the skew unit, has size 1. -/
  traceOne_div_mem_ofSize : element * skewUnit⁻¹.val ∈ ofSize 1
  /-- The elements of K = `F.boxSet` have size 1. -/
  hasMatrixSize_boxSet ⦃x : T.G⦄ : x ∈ F.boxSet → toSize.HasMatrixSize 1 x.val.val
  /-- For a close pair (ω₁, ω₂), the vectors ω₁ and (ω₁ - ω₂) / M have size 1. -/
  mem_vecsOfSize_of_mem_closePairs ⦃ω₁ ω₂ : 𝔰.BesselIndex → A⦄ : (ω₁, ω₂) ∈ F.closePairs →
    ω₁ ∈ toSize.vecsOfSize 1 ∧ F.levelUnit⁻¹.val • (ω₁ - ω₂) ∈ toSize.vecsOfSize 1
  /-- If 1 / M has size 1, some unit c with inverse of size i + 2 turns any two vectors of size i
  into a close pair. -/
  exists_unit_smul_mem_closePairs (i : ℕ) : F.levelUnit⁻¹.val ∈ ofSize 1 →
    ∃ c : Aˣ, c⁻¹.val ∈ ofSize (i + 2) ∧
      ∀ ω₁ ∈ toSize.vecsOfSize i, ∀ ω₂ ∈ toSize.vecsOfSize i,
        (c.val • ω₁, c.val • ω₂) ∈ F.closePairs
  /-- An invertible number of size j has modulus at most Λ^j. -/
  modulus_le (j : ℕ) (u : Aˣ) : (u : A) ∈ ofSize j → P.modulus u ≤ loss ^ j
  /-- The numbers of size j have volume at most Λ^(j+1). -/
  volume_ofSize_le (j : ℕ) : volume (ofSize j) ≤ loss ^ (j + 1)
  /-- There is room for two blocks among the orthonormal basis vectors. -/
  two_mul_blockRank_le : 2 * F.blockRank ≤ card ι
  /-- The quadrics of a block, of rank p = `F.blockRank`. The volume of A^p disintegrates along the
  standard form into an s-finite kernel, each measure of which gives mass at most Λ^(p (j+1)) to
  the vectors of size j. -/
  exists_blockKernel : ∃ l : ProbabilityTheory.Kernel (skewAdjoint A) (Fin F.blockRank → A),
      ProbabilityTheory.IsSFiniteKernel l ∧ IsDisintegration volume 1 l ∧
      ∀ (β : skewAdjoint A) (j : ℕ), l β (toSize.vecsOfSize j) ≤ loss ^ (F.blockRank * (j + 1))
  /-- Common vectors. For g in K, a position z and ϱ linear forms on X' = `F.FreeIndex → A` (the
  rows of v), let W = `F.commonVectors g z v` be the set of vectors killed by the forms and short
  (`IsShortFrom`) from g and g z. Some φ controls the products ⟨u, ω⟩ with ω ∈ W, in the sense of
  `IsCommonBound`. -/
  exists_commonBound : ∀ g ∈ F.boxSet, ∀ z ∈ F.positions, ∀ v : Matrix (Fin 𝔰.ϱ) F.FreeIndex A,
      ∃ φ : (F.FreeIndex → A) → ℝ≥0∞, F.IsCommonBound toSize loss (F.commonVectors g z v) φ

/-- The constant Λ of a gauge is at least 1. -/
@[simp]
lemma Gauge.one_le_loss (Γ : Gauge F) : 1 ≤ Γ.loss := one_le_two.trans Γ.two_le_loss

/-- The close positions of a gauge Γ for the place datum F: the positions z ∈ `F.positions` for
which the matrix (z - 1) / M has size 1, where M = `F.levelUnit` is the level. -/
def Gauge.positionsOfSize (Γ : Gauge F) : Set T.G :=
  {z ∈ F.positions | Γ.HasMatrixSize 1 (F.levelUnit⁻¹.val • (z.val.val - 1))}

end LevelGauge

end New.Floors

end

section

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Sum Set Function FloorGroups Size Place TraceOne PlaceData
  HyperbolicBasis Finset

variable {A ι : Type} {𝔰 : Shape} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]
  [Place A] [Fintype ι] [DecidableEq ι] {m i j : ℕ} {a : Fin 𝔰.ϱ} {T : 𝔰.Form A}
  [IsHermitianUnit T.splitGram] {F : PlaceData ι T m} {Γ : Gauge F} {b : Fin 𝔰.n} {g x σ ξ : T.G}

namespace PlaceData

/-- Being near at j (some element of R^(j) = `partialUnitriangularGroup j` moves the point into
`F.boxSet`) does not change under left multiplication by an element ξ of R^(j). -/
@[simp]
lemma isNear_mul_iff (hξ : ξ ∈ partialUnitriangularGroup j) :
    F.IsNear j (ξ * g) ↔ F.IsNear j g := by
  constructor
  · rintro ⟨η, hη, h_box⟩
    refine ⟨η * ξ, mul_mem hη hξ, ?_⟩
    rwa [mul_assoc]
  · rintro ⟨η, hη, h_box⟩
    refine ⟨η * ξ⁻¹, mul_mem hη (inv_mem hξ), ?_⟩
    rwa [mul_assoc, inv_mul_cancel_left]

/-- If g is near at i (an element of `partialUnitriangularGroup i` moves it into `F.boxSet`), it is
near at every j ≤ i, since these groups decrease with i. -/
lemma IsNear.anti (h_near : F.IsNear i g) (hji : j ≤ i) : F.IsNear j g := by
  obtain ⟨ξ, hξ, h_box⟩ : ∃ ξ ∈ partialUnitriangularGroup i, ξ * g ∈ F.boxSet := h_near
  exact ⟨ξ, partialUnitriangularGroup_anti hji hξ, h_box⟩

/-- If x lies in G^(j) = `floorGroup j` and x g is near at some i ≥ j (an element of
`partialUnitriangularGroup i` moves it into `F.boxSet`), then g is near at j. -/
lemma IsNear.of_floorGroup_mul (h_near : F.IsNear i (x * g)) (hx : x ∈ floorGroup j)
    (hji : j ≤ i := by first | rfl | lia) :
    F.IsNear j g :=
  (isNear_mul_iff (mem_partialUnitriangularGroup_of_mem_floorGroup hx)).mp (h_near.anti hji)

open Pointwise in
/-- The set of points of the unitary group that are near at `j` for the place datum `F` (some
element of `partialUnitriangularGroup j` moves them into the compact set `F.boxSet`) is
measurable. -/
lemma measurableSet_isNear : MeasurableSet {g : T.G | F.IsNear j g} := by
  -- It is the product of the closed subgroup `partialUnitriangularGroup j` with the compact box, so
  -- closed.
  have h_closed : IsClosed (T.partialUnitriangularGroup j : Set T.G) :=
    isClosed_of_entries_eq_one (H := partialUnitriangularGroup j) .rfl
  have h_box : IsCompact F.boxSet := F.isCompact_boxSet_and_measurableSet_positions.1
  have h_eq : (T.partialUnitriangularGroup j : Set T.G) * F.boxSet = {g : T.G | F.IsNear j g} := by
    ext g
    constructor
    · rintro ⟨ξ, hξ, x, hx, rfl⟩
      refine ⟨ξ⁻¹, inv_mem hξ, ?_⟩
      rwa [inv_mul_cancel_left]
    · rintro ⟨ξ, hξ, hξ_box⟩
      exact ⟨ξ⁻¹, inv_mem hξ, ξ * g, hξ_box, inv_mul_cancel_left ξ g⟩
  rw [← h_eq]
  exact (h_closed.mul_right_of_isCompact h_box).measurableSet

/-- Suppose that on each floor a < n the σ with σ g near at a + 1 (`IsNear`) have mass at most V for
`F.floorMeasure a`, whatever g is. Then for every c the g with g c near at ϱ + 2 have mass at most
V^(n-l) for the measure `F.quotientMeasureFrom l` of the floors from l on. Here n = `𝔰.n` = ϱ + 1,
and ϱ is the number of hyperbolic pairs of the shape `𝔰`. -/
lemma quotientMeasureFrom_isNear_le {V : ℝ≥0∞} (hV : ∀ a : Fin 𝔰.n, F.FloorMassLe a V 1) (l : ℕ)
    (c : T.G) :
    F.quotientMeasureFrom l {g : T.G | F.IsNear (𝔰.ϱ + 2) (g * c)} ≤ V ^ (𝔰.n - l) := by
  -- Induction on the number of floors: peel off the lowest floor `l`, which has mass `≤ V`.
  induction hi : 𝔰.n - l generalizing l c with
  | zero =>
    -- only `F.measureH` is left, where the mass is at most 1, or `F.quotientMeasureFrom l` is a
    -- unit mass
    obtain rfl | hl : l = 𝔰.ϱ + 1 ∨ 𝔰.ϱ + 2 - l = 0 := by lia
    · simp [descConv, IsNear, measureH_setOf_mul_mem_boxSet_le_one, -Subtype.exists]
    · simp [hl, descConv, indicator_apply_le']
  | succ i ih =>
    have hl : l < 𝔰.n := by lia
    have h_meas : MeasurableSet {g : T.G | F.IsNear (𝔰.ϱ + 2) (g * c)} :=
      measurable_mul_const c measurableSet_isNear
    let mass (σ : T.G) : ℝ≥0∞ :=
      F.quotientMeasureFrom (l + 1) {x : T.G | F.IsNear (𝔰.ϱ + 2) (x * (σ * c))}
    let N : Set T.G := {σ : T.G | F.IsNear (l + 1) (σ * c)}
    have h_floor : F.floorMeasure l N ≤ V := by
      simpa [Set.univ_inter] using hV ⟨l, hl⟩ c
    -- if `σ * c` is not near at `l + 1`, no point `x * σ * c` with `x` on the higher floors is near
    have h_support : support mass ⊆ N := by
      have h_ae : ∀ᵐ x : T.G ∂F.quotientMeasureFrom (l + 1), x ∈ floorGroup (l + 1) :=
        ae_descConv_mem ae_floorMeasure_mem
      refine support_subset_iff'.2 fun σ hσ ↦ measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [h_ae] with x hx_floor hx
      exact hσ (IsNear.of_floorGroup_mul hx hx_floor)
    calc F.quotientMeasureFrom l {g : T.G | F.IsNear (𝔰.ϱ + 2) (g * c)}
      _ = ∫⁻ σ : T.G, mass σ ∂F.floorMeasure l := by
        rw [quotientMeasureFrom_eq_succ_mconv, mconv_apply_eq_lintegral h_meas]
        simp only [mass, mem_ofPred_eq, mul_assoc]
      _ = ∫⁻ σ : T.G in N, mass σ ∂F.floorMeasure l :=
        (setLIntegral_eq_of_support_subset h_support).symm
      _ ≤ ∫⁻ _ : T.G in N, V ^ i ∂F.floorMeasure l :=
        lintegral_mono fun σ ↦ ih (l + 1) (σ * c) (by lia)
      _ ≤ V ^ (i + 1) := by grw [setLIntegral_const, h_floor, pow_succ]

end PlaceData

/-- Coordinates of a Heisenberg element. Let n = `heisenbergElem a t` have the parameters
t = (ω, β) on floor a, so that (n - 1) e*_a = ω + (β - τ ⟨ω, ω⟩) e_a, where τ = `element` has trace
one and ω is extended by zero. If v differs from (n - 1) e*_a only in the coordinates e_b, b < a
(`CongrBelow`), and v / u has size i, then ω / u and (β - τ ⟨ω, ω⟩) / u have size i. -/
lemma Size.mem_vecsOfSize_of_congrBelow_heisenbergElem {S : Size T} {u : Aˣ}
    {t : ({k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A) × skewAdjoint A} {v : 𝔰.BesselIndex → A}
    (h_congr : CongrBelow a
      (((heisenbergElem (T := T) a t).val.val - 1) *ᵥ Pi.single (eStar a) 1) v)
    (h_short : u⁻¹.val • v ∈ S.vecsOfSize i) :
    u⁻¹.val • inclMatrix A Subtype.val *ᵥ t.1 ∈ S.vecsOfSize i ∧
    u⁻¹ * (t.2.val - element * star (inclMatrix A Subtype.val *ᵥ t.1) ⬝ᵥ
      T.splitGram *ᵥ inclMatrix A Subtype.val *ᵥ t.1) ∈ S.ofSize i := by
  set ω : 𝔰.BesselIndex → A := inclMatrix A Subtype.val *ᵥ t.1 with hω
  have hω_low (k : 𝔰.BesselIndex) (hk : floorOf k ≤ a) : ω k = 0 := by
    simp [hω, inclMatrix_val_mulVec, hk.not_gt]
  have h_column : ((heisenbergElem (T := T) a t).val.val - 1) *ᵥ Pi.single (eStar a) 1 =
      ω + (t.2.val - element * star ω ⬝ᵥ T.splitGram *ᵥ ω) • Pi.single (inl a) 1 := by
    rw [sub_mulVec, one_mulVec, heisenbergElem_mulVec, ← hω]
    simp [splitGram_col, hω_low, add_assoc]
  rw [h_column] at h_congr
  have h_inl : v (inl a) = t.2.val - element * star ω ⬝ᵥ T.splitGram *ᵥ ω := by
    simp [h_congr (inl a) le_rfl, hω_low]
  refine ⟨fun k ↦ ?_, by simpa [h_inl] using h_short (inl a)⟩
  by_cases hk : floorOf k ≤ a
  · simp [hω_low k hk, S.zero_one_mem_ofSize]
  · have h_ne : k ≠ inl a := fun h ↦ hk (by simp [h])
    have h_level : a ≤ BesselIndex.level k := by grind [floorOf_level_cases k]
    have hv : v k = ω k := by simp [h_congr k h_level, h_ne]
    simpa [hv] using h_short k

omit [StarRing A] [TopologicalSpace A] [MeasureSpace A] [Place A] in
/-- The vector e*_a is orthogonal to the e_b with b < a. -/
lemma isOrthogonalBelow_single_eStar (a : Fin 𝔰.ϱ) :
    IsOrthogonalBelow a (Pi.single (eStar a) (1 : A) : 𝔰.BesselIndex → A) :=
  fun b hb ↦ Pi.single_eq_of_ne (by grind) 1

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermitianUnit T.splitGram] in
/-- For n in G^(a) = `floorGroup a` and ν in U_(<a) = `unipotentBelow a`, the vector (ν n - 1) e*_a
differs from (n - 1) e*_a only in the coordinates e_b, b < a. -/
lemma congrBelow_sub_one_mulVec {n ν : T.G} (hn : n ∈ floorGroup a) (hν : ν ∈ unipotentBelow a) :
    CongrBelow a ((n.val.val - 1) *ᵥ Pi.single (eStar a) 1)
      (((ν * n).val.val - 1) *ᵥ Pi.single (eStar a) 1) := by
  have h_orth : IsOrthogonalBelow a (n.val.val *ᵥ Pi.single (eStar a) (1 : A)) :=
    (isOrthogonalBelow_single_eStar a).mulVec (mem_partialUnitriangularGroup_of_mem_floorGroup hn)
      le_rfl
  intro k hk
  have h_fix : ((ν * n).val.val *ᵥ Pi.single (eStar a) (1 : A)) k =
      (n.val.val *ᵥ Pi.single (eStar a) (1 : A)) k := by
    rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
    exact h_orth.congrBelow_mulVec hν k hk
  rw [sub_mulVec, sub_mulVec, Pi.sub_apply, Pi.sub_apply, h_fix]

/-- Let the Heisenberg element n = `heisenbergElem a t` have the parameters t = (ω, β) on floor a,
with ω extended by zero, and let τ = `element`. If (ν n - 1) e*_a / u has size i for some ν in
U_(<a) = `T.unipotentBelow a`, then ω / u and (β - τ ⟨ω, ω⟩) / u have size i. -/
lemma Size.mem_vecsOfSize_and_mem_ofSize_of_heisenbergElem {S : Size T} {u : Aˣ}
    {t : ({k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A) × skewAdjoint A}
    (h_column : ∃ ν ∈ T.unipotentBelow a, u⁻¹.val • (fun k : 𝔰.BesselIndex ↦
      ((ν * heisenbergElem a t).val.val - 1) k (eStar a)) ∈ S.vecsOfSize i) :
    u⁻¹.val • inclMatrix A Subtype.val *ᵥ t.1 ∈ S.vecsOfSize i ∧
    u⁻¹ * (t.2.val - element * star (inclMatrix A Subtype.val *ᵥ t.1) ⬝ᵥ
      T.splitGram *ᵥ inclMatrix A Subtype.val *ᵥ t.1) ∈ S.ofSize i := by
  obtain ⟨ν, hν, h_short⟩ := h_column
  have h_floor : heisenbergElem (T := T) a t ∈ floorGroup a :=
    (heisenbergElem_mem_floorUnipotent a t).1
  refine mem_vecsOfSize_of_congrBelow_heisenbergElem (congrBelow_sub_one_mulVec h_floor hν) ?_
  rwa [mulVec_single_one]

namespace Gauge

/-- The set of vectors all of whose entries have size `j` for the gauge `Γ` is measurable. -/
lemma measurableSet_vecsOfSize {n : Type} [Fintype n] : MeasurableSet (Γ.vecsOfSize (n := n) j) :=
  .univ_pi' fun _ ↦ (Γ.isCompact_ofSize j).measurableSet

/-- If the isometry g is near at j for the place datum `F`, each vector e_a (`a : Fin 𝔰.ϱ`) with
a < j is balanced at g for the gauge `Γ` of `F` with exponent 5: some lift of e_a is moved by g⁻¹
to a vector of size 5. -/
lemma isBalanced_of_isNear (h_near : F.IsNear j g) (ha : a < j) : Γ.IsBalanced g a 5 := by
  -- If `ξ g` lies in the box, take the lift `ξ⁻¹ e_a`; read at `g`, it is a column of `(ξ g)⁻¹`.
  obtain ⟨ξ, hξ, h_box⟩ : ∃ ξ ∈ partialUnitriangularGroup j, ξ * g ∈ F.boxSet := h_near
  have h_size : Γ.HasMatrixSize 5 (ξ * g)⁻¹.val.val := (Γ.hasMatrixSize_boxSet h_box).inv
  have h_col (k : 𝔰.BesselIndex) : Γ.LengthLeAt g 5 (ξ⁻¹.val.val *ᵥ Pi.single k 1) := by
    intro i
    rw [mulVec_mulVec]
    simpa using h_size i k
  have h_lift : CongrBelow a (Pi.single (inl a) 1) (ξ⁻¹.val.val *ᵥ Pi.single (inl a) 1) := by
    intro k hk
    simpa [Matrix.one_apply, Pi.single_apply] using
      mem_partialUnitriangularGroup.1 (inv_mem hξ) k (inl a) hk (.inl ⟨ha, ha⟩)
  exact ⟨⟨_, h_lift, h_col (inl a)⟩⟩

/-- Coordinates of a frame vector. Let g have size i for the gauge `Γ` of the place datum `F`, let σ
lie in G^(b) = `floorGroup b`, and let σ g be near at b + 1. Then `orbitPoint b σ`, the image under
σ⁻¹ of the frame vector number b, has size i + 6. Size i means that all entries lie in
`Γ.ofSize i`. -/
lemma orbitPoint_mem_vecsOfSize (hσ : σ ∈ floorGroup b) (hg : Γ.HasMatrixSize i g.val.val)
    (h_near : F.IsNear (b + 1) (σ * g)) : orbitPoint b σ ∈ Γ.vecsOfSize (i + 6) := by
  obtain ⟨ξ, hξ, h_box⟩ : ∃ ξ ∈ partialUnitriangularGroup (b + 1), ξ * (σ * g) ∈ F.boxSet := h_near
  intro k
  -- The vector is cut from a column of `σ⁻¹ * ξ⁻¹ = g * (ξ * (σ * g))⁻¹`, of size `i + 5 + 1`.
  have h_size : Γ.HasMatrixSize (i + 6) (σ⁻¹ * ξ⁻¹).val.val := by
    have h_eq : σ⁻¹ * ξ⁻¹ = g * (ξ * (σ * g))⁻¹ := by group
    rw [h_eq, Subgroup.coe_mul, Units.val_mul]
    exact hg.mul (Γ.hasMatrixSize_boxSet h_box).inv
  have h_col : orbitPoint b σ k =
      if floorOf k < b then 0 else (σ⁻¹ * ξ⁻¹).val.val k (𝔰.besselFrame b) := by
    rw [orbitPoint, mulVec_single_one]
    exact floorGroup_apply_besselFrame (inv_mem hσ) (inv_mem hξ) k
  rw [h_col]
  split_ifs
  · simp [zero_one_mem_ofSize]
  · exact h_size k (𝔰.besselFrame b)

/-- The set of close positions of the gauge `Γ` of the place datum `F`, the positions z for which
(z - 1) / M has size 1 with M = `F.levelUnit`, is measurable. -/
lemma measurableSet_positionsOfSize : MeasurableSet Γ.positionsOfSize := by
  have h_positions : MeasurableSet F.positions := F.isCompact_boxSet_and_measurableSet_positions.2
  have h_size : MeasurableSet {z : T.G | Γ.HasMatrixSize 1 (F.levelUnit⁻¹.val • (z.val.val - 1))} :=
    (Γ.isCompact_ofSize 1).matrix.measurableSet.preimage (by fun_prop)
  exact h_positions.inter h_size

end Gauge

end New.Floors

namespace New.Floors.PlaceData

open MeasureTheory Measure ProbabilityTheory FloorGroups Set

variable {R ι : Type} {𝔰 : Shape} [CommRing R] [StarRing R] [TopologicalSpace R] [MeasureSpace R]
  [Place R] [Fintype ι] [DecidableEq ι] {m j l : ℕ} {T : 𝔰.Form R} [IsHermitianUnit T.splitGram]
  {F : PlaceData ι T m} {g y : T.G} {s : T.G} {k : T.G → T.G → ℂ} {d : T.G}

namespace IsPairingKernel

/-! ### The averaged kernel -/

/-- For a pairing kernel `k`, the correlation from floor `l` on is jointly strongly measurable. -/
@[fun_prop]
lemma stronglyMeasurable_partialCorrelation (hk : F.IsPairingKernel j k d) :
    StronglyMeasurable ↿(F.partialCorrelation l k) := by
  have h_meas : Measurable ↿k := hk.measurable
  exact .integral_prod_right (by fun_prop)

/-- If `k` is a pairing kernel at floor `j`, it is one at every floor `l ≥ j`, with the same `d`. -/
lemma mono (hk : F.IsPairingKernel j k d) (h : j ≤ l) : F.IsPairingKernel l k d :=
  { hk with conj_eq_self := fun s hs ↦ hk.conj_eq_self s (floorGroup_anti h hs) }

/-- For a pairing kernel `k`, the integral over the floors from `l` on that defines
`F.partialCorrelation l k g y` converges absolutely. -/
lemma integrable_quotientMeasureFrom (hk : F.IsPairingKernel j k d) (l : ℕ) (g y : T.G) :
    Integrable (fun x : T.G ↦ k (x * g) (x * y)) (F.quotientMeasureFrom l) := by
  obtain ⟨c, hc, h_bound⟩ :
      ∃ c < ⊤, ∀ g y : T.G, ∫⁻ x : T.G, ‖k (x * g) (x * y)‖ₑ ∂F.quotientMeasureFrom l ≤ c :=
    hk.exists_lintegral_le l
  have h_meas : Measurable ↿k := hk.measurable
  exact ⟨Measurable.aestronglyMeasurable (by fun_prop), (h_bound g y).trans_lt hc⟩

/-- For a pairing kernel `k`, the function x ↦ k(x g, x y) is integrable for the convolution of the
measure of the floors from `l + 1` on with the measure of floor `l`. -/
lemma integrable_quotientMeasureFrom_mconv_floorMeasure (hk : F.IsPairingKernel j k d) (l : ℕ)
    (g y : T.G) :
    Integrable (fun x : T.G ↦ k (x * g) (x * y))
      (F.quotientMeasureFrom (l + 1) ∗ₘ F.floorMeasure l) := by
  rw [← F.quotientMeasureFrom_eq_succ_mconv]
  exact hk.integrable_quotientMeasureFrom l g y

/-- For a pairing kernel `k`, the correlation `F.partialCorrelation (l + 1) k (σ * g) (σ * y)` from
floor `l + 1` on is integrable in σ for the measure `F.floorMeasure l` of floor `l`. -/
lemma integrable_partialCorrelation_succ (hk : F.IsPairingKernel j k d) :
    Integrable (fun σ : T.G ↦ F.partialCorrelation (l + 1) k (σ * g) (σ * y))
      (F.floorMeasure l) := by
  have h_prod : Integrable (fun p : T.G × T.G ↦ k (p.1 * p.2 * g) (p.1 * p.2 * y))
      ((F.quotientMeasureFrom (l + 1)).prod (F.floorMeasure l)) :=
    (hk.integrable_quotientMeasureFrom_mconv_floorMeasure l g y).comp_measurable measurable_mul
  simp only [partialCorrelation, ← mul_assoc]
  exact h_prod.integral_prod_right

/-- For a pairing kernel `k`, the correlation `F.partialCorrelation l k g y` from floor `l` on is
the integral of `F.partialCorrelation (l + 1) k (σ * g) (σ * y)` in σ for the measure
`F.floorMeasure l` of floor `l`. -/
lemma partialCorrelation_eq_integral_floorMeasure (hk : F.IsPairingKernel j k d) :
    F.partialCorrelation l k g y =
      ∫ σ : T.G, F.partialCorrelation (l + 1) k (σ * g) (σ * y) ∂F.floorMeasure l := by
  -- `F.quotientMeasureFrom l` is `F.quotientMeasureFrom (l + 1)` convolved with `F.floorMeasure l`;
  -- the claim is Fubini's theorem on the product of the two.
  have h_int : Integrable (fun x : T.G ↦ k (x * g) (x * y))
      (F.quotientMeasureFrom (l + 1) ∗ₘ F.floorMeasure l) :=
    hk.integrable_quotientMeasureFrom_mconv_floorMeasure l g y
  calc F.partialCorrelation l k g y
    _ = ∫ x : T.G, k (x * g) (x * y) ∂(F.quotientMeasureFrom (l + 1) ∗ₘ F.floorMeasure l) := by
      rw [partialCorrelation, F.quotientMeasureFrom_eq_succ_mconv (l := l)]
    _ = ∫ x : T.G, ∫ σ : T.G, k (x * σ * g) (x * σ * y)
          ∂F.floorMeasure l ∂F.quotientMeasureFrom (l + 1) := integral_mconv h_int
    _ = ∫ σ : T.G, ∫ x : T.G, k (x * σ * g) (x * σ * y)
          ∂F.quotientMeasureFrom (l + 1) ∂F.floorMeasure l :=
      integral_integral_swap (h_int.comp_measurable measurable_mul)
    _ = ∫ σ : T.G, F.partialCorrelation (l + 1) k (σ * g) (σ * y) ∂F.floorMeasure l := by
      simp only [partialCorrelation, mul_assoc]

/-- For a pairing kernel `k`, the modulus of the correlation from floor `l` on is at most
`F.pivotL1Norm l k g y`, the integral over floor `l` of the modulus of the correlation from floor
`l + 1` on. -/
lemma enorm_partialCorrelation_le (hk : F.IsPairingKernel j k d) :
    ‖F.partialCorrelation l k g y‖ₑ ≤ F.pivotL1Norm l k g y := by
  rw [hk.partialCorrelation_eq_integral_floorMeasure]
  exact eNorm_integral_le_lintegral_eNorm _

/-- Let `k` satisfy `F.IsPairingKernel j k d` with `j ≤ l`. Then `F.partialCorrelation l k`, the
integral of k(x g, x y) in x for `F.quotientMeasureFrom l`, is unchanged when both arguments are
left translated by the same `s` in R^(l) ∩ G^(j). -/
lemma partialCorrelation_mul_left (hk : F.IsPairingKernel j k d) (hl : j ≤ l)
    (hs : s ∈ partialUnitriangularGroup l ⊓ floorGroup j) :
    F.partialCorrelation l k (s * g) (s * y) = F.partialCorrelation l k g y := by
  -- Descending induction on the floor `l`.
  induction h_floor : 𝔰.ϱ + 2 - l generalizing l s g y with
  | zero =>
    -- Here no averaging is left; `s` lies in `T.besselU = unipotentBelow 𝔰.n` and commutes with
    -- `d`, so the character in `hk.equivariance` is `1`.
    obtain ⟨hs_unitri, hs_floor⟩ : s ∈ partialUnitriangularGroup l ∧ s ∈ floorGroup j :=
      Subgroup.mem_inf.1 hs
    have hs_U : s ∈ T.besselU := partialUnitriangularGroup_add_two_eq_besselU.le
      (partialUnitriangularGroup_anti (by lia) hs_unitri)
    have hs_N : s ∈ unipotentBelow 𝔰.n := by rwa [unipotentBelow_eq_besselU 𝔰.ϱ.le_succ]
    have h_law : F.partialCorrelation (𝔰.n + 1) k (s * g) (s * y) = F.partialCorrelation (𝔰.n + 1) k
      g y := by
      simpa [hk.conj_eq_self s hs_floor] using hk.equivariance hs_N hs_N g y
    -- from floor `l` on, as from floor `𝔰.n + 1 = 𝔰.ϱ + 2` on, the measure is the unit mass at `1`
    simpa [partialCorrelation, descConv, h_floor] using h_law
  | succ i ih =>
    -- `F.partialCorrelation l` is the integral of `Φ`, which is invariant by induction, so by
    -- `lintegral_floorMeasure_mul_right` the translate of `Φ` by `s` has the law of `Φ`.
    let Φ (σ : T.G) : ℂ := F.partialCorrelation (l + 1) k (σ * g) (σ * y)
    have h_inv : ∀ u ∈ partialUnitriangularGroup (l + 1) ⊓ floorGroup j, ∀ σ : T.G,
      Φ (u * σ) = Φ σ := by
      intro u hu σ
      simp only [Φ, mul_assoc]
      exact ih (hl.trans l.le_succ) hu (by lia)
    have h_law : IdentDistrib (fun σ ↦ Φ (σ * s)) Φ (F.floorMeasure l) (F.floorMeasure l) := by
      refine ⟨by fun_prop, by fun_prop, ext_of_lintegral _ fun φ hφ ↦ ?_⟩
      rw [lintegral_map hφ (by fun_prop), lintegral_map hφ (by fun_prop)]
      exact lintegral_floorMeasure_mul_right (f := fun σ ↦ φ (Φ σ)) (floorGroup_anti hl)
        (fun u hu σ ↦ congrArg φ (h_inv u hu σ)) hs
    simpa [hk.partialCorrelation_eq_integral_floorMeasure (l := l), Φ, mul_assoc] using
      h_law.integral_eq

end IsPairingKernel

end New.Floors.PlaceData

end
