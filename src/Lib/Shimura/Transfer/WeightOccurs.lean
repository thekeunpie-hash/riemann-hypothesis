module

import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.PiTensorProduct
import TauCeti.Analysis.Normed.Ring.Ultra
public import Lib.General.LinearAlgebra.IdempotentRadical
public import Lib.Adelic.TraceFormula.ChangingSigns
public import Lib.General.Combinatorics
import Lib.General.LinearAlgebra.MatrixPolynomials
import Lib.Shimura.HeckeTower.Model
import Lib.Shimura.Transfer.MarkedPairs
public import Lib.Shimura.Uniformisation.HolomorphicFamilies
import Mathlib.Algebra.Order.Star.Rat
public import Lib.LocalGL.Iwahori.ParahoricStructure
public import Lib.Shimura.HeckeTower.HeckeData
import Lib.LocalGL.Iwahori.QuadraticRelation
import Lib.PadicComparison.Descent.TestCategory
import TauCeti.LinearAlgebra.Trace.Nilpotent
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Lib.Shimura.TraceFormula.DefiniteTrace
public import Lib.Shimura.Transfer.Lefschetz
public import Lib.Adelic.AutomorphicForms.SmoothAlgebraicForms
import Lib.DiscreteSeries.Character.WeylCharacterFormula
import Lib.GLn.SchurModule.SchurNorm
import Lib.General.NumberTheory.FrobeniusOrbits

section
/-!
# For a function with a cuspidal type at one place, marked and definite orbit sums agree

* `New.Variety.finsum_orbits_eq_zero_of_free_of_blocks`: a sum over orbits vanishes if it vanishes
  on each block of a partition that the group permutes, with finite support there, and the
  stabiliser of each point where it is non-zero is trivial.
* `New.Variety.finsum_markedTerm_eq_finsum_definiteTerm`: the marked and the definite sums agree for
  every weight; `New.Variety.finsum_countTerm_marked_eq_definite` says this in terms of `countTerm`.

Idea: both sums run over the classes of triples `(xK, y, μ)` under `GL n E`. Classes with
irreducible characteristic polynomial are matched by a change of signs. For a reducible one, an
idempotent at the split place gives a unipotent group, whose orbits cut the triples into blocks;
translation along it multiplies the terms by a value of the character that is not 1, so they sum to
zero on each block.

Notions from other files:
* `New.Variety.MarkedTriple`: triples `(xK, y, μ)` of an adelic coset, an element `y` of `GL n E`
  and an index `μ` of an eigenvalue of `y`.
* `New.Variety.countTerm`: the term `f(x⁻¹ y⁻¹ x K) * u(charpoly y, μ)` of the class of
  `(xK, y, μ)` if `IsSignedFrame x (eigenReflection ε y μ)` holds (the sign condition), else `0`;
  `ε = True` gives the marked count and `ε = False` the definite count.
* `New.Variety.conjAtSplit`: places an element of `GL n` over the completion at a split place `w₀`
  in the adelic similitude group; `New.Variety.dualComponent` is a left inverse.
* `New.Variety.IsRegularHecke`: `f(x⁻¹ y⁻¹ x K) ≠ 0` forces the characteristic polynomial of `y` to
  be separable.
* `New.Variety.IsCuspidalType`: for every idempotent matrix `e ≠ 0, 1`, the character `χ` is
  non-trivial on the elements of `J` in the unipotent group `1 + e M_n (1 - e)`.

## Relation to the literature

Known result: Simple trace formula on a definite group, with vanishing non-elliptic terms. This
file proves the comparison of orbit sums that is used, for unitary similitudes at a neat level, with
Haar integrals replaced by finite sums over cosets. The non-elliptic terms cancel for a regular test
function with a cuspidal type at one split place; the elliptic terms match for n odd.
Source: Dummigan, A simple trace formula for algebraic modular forms, Exp. Math. 22 (2013); Arthur
and Clozel, Simple algebras, base change and the advanced theory of the trace formula (1989), ch. 1
§2, after Deligne and Kazhdan.
-/

@[expose] public section

open Function NumberField Matrix Polynomial Set MulAction Pointwise Multiplicative

noncomputable section

namespace New.Variety

/-! ### Sums over blocks and cosets -/

section Orbits

variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

/-- Let `Γ` permute the blocks `π p` of a partition of `X`. If the stabiliser of `p` is trivial,
the points of its block that lie in its orbit are as many as the elements of the stabiliser of
the block. -/
lemma card_block_inter_orbit {π : X → Set X} (h_block : ∀ p q : X, p ∈ π q ↔ π p = π q)
    (h_smul : ∀ (z : Γ) (p : X), π (z • p) = z • π p) {p : X} (hp : stabilizer Γ p = ⊥) :
    Nat.card {s ∈ π p | (⟦s⟧ : orbitRel.Quotient Γ X) = ⟦p⟧} = Nat.card (stabilizer Γ (π p)) := by
  have h_inj : Injective fun z : Γ ↦ z • p := fun a b (hab : a • p = b • p) ↦ by
    have h_mem : a⁻¹ * b ∈ stabilizer Γ p := by simp [mul_smul, ← hab]
    rwa [hp, Subgroup.mem_bot, inv_mul_eq_one] at h_mem
  have h_image : (fun z : Γ ↦ z • p) '' stabilizer Γ (π p) =
      {s ∈ π p | (⟦s⟧ : orbitRel.Quotient Γ X) = ⟦p⟧} := by
    refine subset_antisymm ?_ fun s ⟨hs, h_orbit⟩ ↦ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨(h_block _ p).2 ((h_smul z p).trans hz), orbitRel.Quotient.quotient_smul_eq⟩
    · obtain ⟨z, rfl⟩ : s ∈ orbit Γ p := Quotient.exact h_orbit
      exact ⟨z, (h_smul z p).symm.trans ((h_block _ p).1 hs), rfl⟩
  rw [← h_image, Nat.card_image_of_injective h_inj, SetLike.coe_sort_coe]

/-- Let `Γ` permute the blocks `π p` of a partition of `X`. An orbit `a` meets the block of `s` if
and only if the block of the chosen point of `a` is a translate of the block of `s`. -/
lemma mem_image_block_iff {π : X → Set X} (h_block : ∀ p q : X, p ∈ π q ↔ π p = π q)
    (h_smul : ∀ (z : Γ) (p : X), π (z • p) = z • π p) (s : X) (a : orbitRel.Quotient Γ X) :
    a ∈ Quotient.mk (orbitRel Γ X) '' π s ↔ π a.out ∈ orbit Γ (π s) := by
  rw [mem_orbit_symm]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : Γ, z • (⟦p⟧ : orbitRel.Quotient Γ X).out = p :=
      mem_orbit_symm.1 (Quotient.mk_out (s := orbitRel Γ X) p)
    exact ⟨z, by simpa only [← h_smul, hz] using (h_block p s).1 hp⟩
  · rintro ⟨z, hz⟩
    exact ⟨z • a.out, (h_block _ s).2 ((h_smul z _).trans hz), by simp⟩

/-- Let `Γ` permute the blocks `π p` of a partition of `X`, and let `F` be a function on the orbits.
Suppose that at every point where `F` is not zero the stabiliser is trivial, and that the block of
such a point has finite intersection with the support of `F` and sum zero. Then the sum of `F` over
the orbits is zero. -/
lemma finsum_orbits_eq_zero_of_free_of_blocks {F : orbitRel.Quotient Γ X → ℂ} (π : X → Set X)
    (h_self : ∀ p : X, p ∈ π p) (h_equivariant : ∀ (z : Γ) {p q : X}, p ∈ π q → π (z • p) = z • π q)
    (h_free : ∀ s : X, F ⟦s⟧ ≠ 0 → stabilizer Γ s = ⊥)
    (h_finite : ∀ s : X, F ⟦s⟧ ≠ 0 → (π s ∩ {p : X | F ⟦p⟧ ≠ 0}).Finite)
    (h_sum : ∀ s : X, F ⟦s⟧ ≠ 0 → ∑ᶠ p ∈ π s, F ⟦p⟧ = 0) :
    ∑ᶠ c : orbitRel.Quotient Γ X, F c = 0 := by
  classical
  -- Group the classes `c` by the orbit of the block `π c.out` and show each group sums to zero.
  have h_block (p q : X) : p ∈ π q ↔ π p = π q :=
    ⟨fun h ↦ by simpa using h_equivariant 1 h, fun h ↦ by simpa only [← h] using h_self p⟩
  have h_smul (z : Γ) (p : X) : π (z • p) = z • π p := h_equivariant z (h_self p)
  obtain hF | hF := F.support.finite_or_infinite.symm
  · exact finsum_of_infinite_support hF
  rw [finsum_eq_sum F hF]
  refine Finset.sum_cancels_of_partition_cancels
    ((orbitRel Γ (Set X)).comap fun c ↦ π c.out) fun c hc ↦ ?_
  have hc_ne : F ⟦c.out⟧ ≠ 0 := by rwa [Quotient.out_eq, ← mem_support, ← hF.mem_toFinset]
  set T : Set X := π c.out ∩ {p : X | F ⟦p⟧ ≠ 0}
  -- The action is free on `T`, so all fibres of the map from `T` to the orbits have one size.
  have h_card (p : X) (hp : p ∈ T) : Nat.card {s ∈ T | (⟦s⟧ : orbitRel.Quotient Γ X) = ⟦p⟧} =
      Nat.card (stabilizer Γ (π c.out)) := by
    obtain ⟨hp_mem : p ∈ π c.out, hp_ne : F ⟦p⟧ ≠ 0⟩ := hp
    have h_fibre : {s ∈ T | (⟦s⟧ : orbitRel.Quotient Γ X) = ⟦p⟧} =
        {s ∈ π c.out | (⟦s⟧ : orbitRel.Quotient Γ X) = ⟦p⟧} :=
      Set.ext fun s ↦ and_congr_left fun hs ↦ and_iff_left (by rwa [mem_ofPred_eq, hs])
    rw [h_fibre, ← (h_block p c.out).1 hp_mem,
      card_block_inter_orbit h_block h_smul (h_free p hp_ne)]
  have h_sum_T : ∑ᶠ p ∈ T, F ⟦p⟧ = 0 :=
    (finsum_mem_inter_support (fun p ↦ F ⟦p⟧) (π c.out)).trans (h_sum c.out hc_ne)
  have h_sum_image : ∑ᶠ a ∈ Quotient.mk (orbitRel Γ X) '' T, F a = 0 :=
    finsum_image_eq_zero_of_fibers (h_finite c.out hc_ne) _ h_sum_T fun p hp ↦ by rw [h_card p hp]
  -- On the support of `F`, the image of `T` is the group of `c`.
  have h_image (a : orbitRel.Quotient Γ X) (ha : F a ≠ 0) :
      a ∈ Quotient.mk (orbitRel Γ X) '' T ↔ π a.out ∈ orbit Γ (π c.out) := by
    rw [← mem_image_block_iff h_block h_smul]
    exact ⟨fun h ↦ image_mono inter_subset_left h,
      fun ⟨p, hp, h⟩ ↦ ⟨p, ⟨hp, by rwa [mem_ofPred_eq, h]⟩, h⟩⟩
  rw [← h_sum_image]
  refine (finsum_cond_eq_sum_of_cond_iff F fun {a} ha ↦ ?_).symm
  rw [Finset.mem_filter, hF.mem_toFinset, mem_support, and_iff_right ha]
  exact h_image a ha

/-- The form of `finsum_orbits_eq_zero_of_free_of_blocks` with one hypothesis `h_cancel`: at a point
where `F` is not zero the stabiliser is trivial, and `F` has finite support and sum zero on the
block. -/
lemma finsum_orbits_eq_zero_of_blocks {F : orbitRel.Quotient Γ X → ℂ} (π : X → Set X)
    (h_self : ∀ p : X, p ∈ π p) (h_equivariant : ∀ (z : Γ) {p q : X}, p ∈ π q → π (z • p) = z • π q)
    (h_cancel : ∀ s : X, F ⟦s⟧ ≠ 0 → stabilizer Γ s = ⊥ ∧
      (π s ∩ {p : X | F ⟦p⟧ ≠ 0}).Finite ∧ ∑ᶠ p ∈ π s, F ⟦p⟧ = 0) :
    ∑ᶠ c : orbitRel.Quotient Γ X, F c = 0 :=
  finsum_orbits_eq_zero_of_free_of_blocks π h_self h_equivariant (fun s hs ↦ (h_cancel s hs).1)
    (fun s hs ↦ (h_cancel s hs).2.1) (fun s hs ↦ (h_cancel s hs).2.2)

end Orbits

section Cosets

variable {M X : Type*} [Group M] {L : Subgroup M} {r : M → X} {F : X → ℂ}

/-- Let the fibres of `r` be the cosets of `L`. If translation by `a` multiplies `F ∘ r` by a
constant other than `1`, the sum of `F` over the image of `r` is zero. -/
lemma finsum_mem_range_eq_zero_of_translate (hr : ∀ m m' : M, r m = r m' ↔ m⁻¹ * m' ∈ L)
    {a : M} {c : ℂ} (hc : c ≠ 1) (h_translate : ∀ m : M, F (r (a * m)) = c * F (r m)) :
    ∑ᶠ p ∈ range r, F p = 0 := by
  let r' : M ⧸ L → X :=
    Quotient.lift r fun m m' h ↦ (hr m m').2 (QuotientGroup.leftRel_apply.1 h)
  have h_inj : Injective r' :=
    Quotient.ind₂ fun m m' h ↦ QuotientGroup.eq.2 ((hr m m').1 h)
  have h_sum : c * ∑ᶠ q : M ⧸ L, F (r' q) = ∑ᶠ q : M ⧸ L, F (r' q) := by
    rw [mul_finsum]
    exact finsum_eq_of_bijective (toPerm a) (toPerm a).bijective
      (Quotient.ind fun m ↦ (h_translate m).symm)
  rw [show range r = range r' from QuotientGroup.mk_surjective.range_comp r',
    finsum_mem_range h_inj]
  exact eq_zero_of_mul_eq_self_left hc h_sum

/-- Let the fibres of `r` be the cosets of an open subgroup `L`. If every point of the image of `r`
where `F` is not zero comes from a compact set `C`, there are finitely many such points. -/
lemma finite_range_inter_support [TopologicalSpace M] [IsTopologicalGroup M]
    (hL : IsOpen (L : Set M)) (hr : ∀ m m' : M, r m = r m' ↔ m⁻¹ * m' ∈ L) {C : Set M}
    (hC : IsCompact C) (h_supp : ∀ m : M, F (r m) ≠ 0 → ∃ m' ∈ C, r m' = r m) :
    (range r ∩ {p : X | F p ≠ 0}).Finite := by
  let r' : M ⧸ L → X :=
    Quotient.lift r fun m m' h ↦ (hr m m').2 (QuotientGroup.leftRel_apply.1 h)
  refine ((finite_quotient_image_of_isCompact hL hC).image r').subset ?_
  rintro _ ⟨⟨m, rfl⟩, hm⟩
  obtain ⟨m', hm', h_eq⟩ := h_supp m hm
  exact ⟨m', ⟨m', hm', rfl⟩, h_eq⟩

end Cosets

/-! ### An idempotent that is a polynomial in the element, and its radical -/

section Splitting

variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

/-- Every polynomial `P` over a field has an idempotent `p` modulo `P` such that, if `P` is
separable, not irreducible and not a unit, neither `p` nor `1 - p` is coprime to `P`. -/
lemma exists_idempotent_mod (P : F[X]) :
    ∃ p : F[X], P ∣ p * p - p ∧
      (P.Separable → ¬Irreducible P → ¬IsUnit P → ¬IsCoprime P (1 - p) ∧ ¬IsCoprime P p) := by
  by_cases hP : P.Separable ∧ ¬Irreducible P ∧ ¬IsUnit P
  · -- Factor `P = A * B` into coprime non-units, `u * A + v * B = 1`, and take `p = u * A`.
    obtain ⟨h_sep, h_red, h_unit⟩ := hP
    obtain ⟨A, B, hA, hB, rfl⟩ : ∃ A B : F[X], ¬IsUnit A ∧ ¬IsUnit B ∧ P = A * B :=
      (irreducible_or_factor h_unit).resolve_left h_red
    obtain ⟨u, v, huv⟩ : IsCoprime A B := h_sep.isCoprime
    have h_dvd : A * B ∣ u * A * (u * A) - u * A := ⟨-u * v, by linear_combination u * A * huv⟩
    have h_one_sub : ¬IsCoprime (A * B) (1 - u * A) := fun h ↦ by
      rw [← huv, add_sub_cancel_left] at h
      exact hB (isCoprime_self.1 h.of_mul_left_right.of_mul_right_right)
    have h_self : ¬IsCoprime (A * B) (u * A) := fun h ↦
      hA (isCoprime_self.1 h.of_mul_left_left.of_mul_right_right)
    exact ⟨u * A, h_dvd, fun _ _ _ ↦ ⟨h_one_sub, h_self⟩⟩
  · exact ⟨0, by simp, fun h_sep h_red h_unit ↦ absurd ⟨h_sep, h_red, h_unit⟩ hP⟩

/-- A fixed choice of the idempotent modulo `P` of `exists_idempotent_mod`. -/
def splittingPoly (P : F[X]) : F[X] := (exists_idempotent_mod P).choose

/-- The idempotent `p(g)`, where `p` is the chosen idempotent modulo the characteristic polynomial
of `g`. -/
def splittingIdempotent (g : GL n F) : Matrix n n F := aeval g.val (splittingPoly g.val.charpoly)

/-- The matrix `splittingIdempotent g = p(g)` is idempotent, by the Cayley-Hamilton theorem. -/
lemma isIdempotentElem_splittingIdempotent (g : GL n F) :
    IsIdempotentElem (splittingIdempotent g) := by
  have h_dvd := aeval_dvd g.val (exists_idempotent_mod g.val.charpoly).choose_spec.1
  rwa [aeval_self_charpoly, zero_dvd_iff, map_sub, map_mul, sub_eq_zero] at h_dvd

/-- If the characteristic polynomial of `g` is separable and not irreducible, the idempotent
`splittingIdempotent g` is neither `0` nor `1`. -/
lemma splittingIdempotent_ne_zero_and_ne_one [Nonempty n] {g : GL n F}
    (h_sep : g.val.charpoly.Separable) (h_red : ¬Irreducible g.val.charpoly) :
    splittingIdempotent g ≠ 0 ∧ splittingIdempotent g ≠ 1 := by
  have h_unit : ¬IsUnit g.val.charpoly := not_isUnit_of_natDegree_pos _ (by simp [Fintype.card_pos])
  obtain ⟨h_one_sub, h_self⟩ : ¬IsCoprime g.val.charpoly (1 - splittingPoly g.val.charpoly) ∧
      ¬IsCoprime g.val.charpoly (splittingPoly g.val.charpoly) :=
    (exists_idempotent_mod g.val.charpoly).choose_spec.2 h_sep h_red h_unit
  rw [splittingIdempotent]
  exact ⟨fun h ↦ h_one_sub (isUnit_aeval_iff_isCoprime.1 (by simp [h])),
    fun h ↦ h_self (isUnit_aeval_iff_isCoprime.1 (by simp [h]))⟩

lemma aeval_units_conj (b g : GL n F) (p : F[X]) :
    aeval (b⁻¹ * g * b).val p = b⁻¹.val * aeval g.val p * b.val := by
  have h_semiconj : b.val * (b⁻¹ * g * b).val = g.val * b.val := by simp [← mul_assoc]
  rw [mul_assoc b⁻¹.val, ← aeval_semiconj h_semiconj p, Units.inv_mul_cancel_left]

/-- Conjugating `g` conjugates its idempotent. -/
lemma splittingIdempotent_conj (b g : GL n F) :
    splittingIdempotent (b⁻¹ * g * b) = b⁻¹.val * splittingIdempotent g * b.val := by
  rw [splittingIdempotent, aeval_units_conj, Units.val_mul, Units.val_mul, coe_units_inv,
    charpoly_units_conj', splittingIdempotent]

/-- The parametrisation `Y ↦ 1 + e Y (1 - e)` of the unipotent radical attached to the idempotent
`e = splittingIdempotent g`. Its range is called the radical of `g`. -/
def splittingRadical (g : GL n F) : Multiplicative (Matrix n n F) →* GL n F :=
  radicalHom (isIdempotentElem_splittingIdempotent g)

/-- Conjugating `g` conjugates its radical: if `a` lies in the radical of `g`, then `b⁻¹ a b` lies
in the radical of `b⁻¹ g b`. -/
lemma mem_range_splittingRadical_conj {b g a : GL n F} (ha : a ∈ (splittingRadical g).range) :
    b⁻¹ * a * b ∈ (splittingRadical (b⁻¹ * g * b)).range := by
  obtain ⟨Y, rfl⟩ := ha
  refine ⟨ofAdd (b⁻¹.val * Y.toAdd * b.val), Units.ext ?_⟩
  simp only [splittingRadical, Units.val_mul, coe_radicalHom, splittingIdempotent_conj, toAdd_ofAdd]
  simp [mul_add, add_mul, mul_sub, sub_mul, mul_assoc]

/-- An element `a` of the radical of `g` is recovered from the conjugate `a⁻¹ g a`: its parameter
can be taken to be `p(a⁻¹ g a)`, for the polynomial `p` that gives the idempotent of `g`. -/
lemma splittingRadical_aeval_conj {g a : GL n F} (ha : a ∈ (splittingRadical g).range) :
    splittingRadical g (ofAdd (aeval (a⁻¹ * g * a).val (splittingPoly g.val.charpoly))) = a := by
  -- Write a = 1 + e Y (1 - e). Its inverse fixes e, so the conjugate projector is e a.
  obtain ⟨Y, rfl⟩ := ha
  have he := isIdempotentElem_splittingIdempotent g
  rw [aeval_units_conj, ← splittingIdempotent, ← map_inv, splittingRadical,
    coe_radicalHom_mul_idempotent]
  apply Units.ext
  simp [coe_radicalHom, toAdd_ofAdd, mul_add, mul_assoc, he.mul_self_mul,
    he.one_sub.eq, he.mul_one_sub_self]

/-- A translate `j g` of `g` by an element `j` of its radical is conjugate to `g` under the
radical. -/
lemma exists_splittingRadical_conj {g j : GL n F} (hj : j ∈ (splittingRadical g).range) :
    ∃ D : Multiplicative (Matrix n n F),
      (splittingRadical g D)⁻¹ * g * splittingRadical g D = j * g := by
  -- With `x = j g` and `p(g)` the idempotent of `g`, the parameter `D = p(x) - p(g)` works, by
  -- `semiconjBy_radicalHom_aeval_sub` for the factorisation `x = j g 1`.
  obtain ⟨Y, rfl⟩ := hj
  have he : IsIdempotentElem (splittingIdempotent g) := isIdempotentElem_splittingIdempotent g
  set p : F[X] := splittingPoly g.val.charpoly
  set x : GL n F := splittingRadical g Y * g
  set D : Multiplicative (Matrix n n F) := ofAdd (aeval x.val p - aeval g.val p)
  have h_semiconj : SemiconjBy (splittingRadical g D) x g :=
    semiconjBy_radicalHom_aeval_sub he (h_range := he.eq) (h_fix := he.eq) Y 1
      (by simp [x, splittingRadical])
  exact ⟨D, by rw [mul_assoc, ← h_semiconj.eq, inv_mul_cancel_left]⟩

/-- Conjugating `g` by an element `b` of its radical does not change the radical, as this group is
commutative. -/
lemma range_splittingRadical_conj_self {g b : GL n F} (hb : b ∈ (splittingRadical g).range) :
    (splittingRadical (b⁻¹ * g * b)).range = (splittingRadical g).range := by
  have h_le {g b : GL n F} (hb : b ∈ (splittingRadical g).range) :
      (splittingRadical g).range ≤ (splittingRadical (b⁻¹ * g * b)).range := by
    intro a ha
    have h_comm : Commute a b := by
      obtain ⟨Y, rfl⟩ := ha
      obtain ⟨Z, rfl⟩ := hb
      exact (Commute.all Y Z).map (splittingRadical g)
    have h_fix : b⁻¹ * a * b = a := by rw [mul_assoc, h_comm.eq, inv_mul_cancel_left]
    simpa only [h_fix] using mem_range_splittingRadical_conj (b := b) ha
  -- For the other inclusion, conjugate back by `b⁻¹`, which lies in the radical of `b⁻¹ * g * b`.
  have h_back : b⁻¹⁻¹ * (b⁻¹ * g * b) * b⁻¹ = g := by group
  exact le_antisymm (by simpa only [h_back] using h_le (inv_mem (h_le hb hb))) (h_le hb)

end Splitting

/-- If the characteristic polynomial of `g` is separable and reducible, a cuspidal type `(J, χ)`
has an element `j` in the radical of `g` with `χ j ≠ 1`. -/
lemma IsCuspidalType.exists_mem_range_splittingRadical {F : Type*} {n : Type} [Field F]
    [Fintype n] [DecidableEq n] [Nonempty n] {J : Subgroup (GL n F)} {χ : J →* ℂ}
    (hχ : IsCuspidalType J χ) {g : GL n F} (h_sep : g.val.charpoly.Separable)
    (h_red : ¬Irreducible g.val.charpoly) :
    ∃ j : J, j.val ∈ (splittingRadical g).range ∧ χ j ≠ 1 := by
  obtain ⟨h_ne_zero, h_ne_one⟩ := splittingIdempotent_ne_zero_and_ne_one h_sep h_red
  obtain ⟨j, Y, hj, hχj⟩ : ∃ (j : J) (Y : Matrix n n F),
      1 + splittingIdempotent g * Y * (1 - splittingIdempotent g) = j.val ∧ χ j ≠ 1 :=
    hχ _ (isIdempotentElem_splittingIdempotent g) h_ne_zero h_ne_one
  exact ⟨j, ⟨ofAdd Y, Units.ext hj⟩, hχj⟩

/-! ### The blocks of triples -/

section Blocks

variable {E n : Type} [Field E] [CMBase E] [Fintype n] [DecidableEq n] {K : Subgroup (GL n (𝔸f E))}
  (w₀ : SplitFinPlace E)

variable (K) in
/-- The triple `(xK, y, μ)`. -/
def markedTriple (x : GL n (𝔸f E)) (y : GL n E) (μ : n) : MarkedTriple K n := (↑x, y, μ)

/-- A triple `p = (q, y, μ)` is the triple of the chosen representative of its coset `q`. -/
lemma markedTriple_out (p : MarkedTriple K n) : markedTriple K p.1.out p.2.1 p.2.2 = p :=
  Prod.ext (QuotientGroup.out_eq' p.1) rfl

/-- The triples `(xK, y, μ)` and `(x'K, y', μ)` are equal if and only if `xK = x'K` and `y = y'`. -/
lemma markedTriple_eq_iff {x x' : GL n (𝔸f E)} {y y' : GL n E} {μ : n} :
    markedTriple K x y μ = markedTriple K x' y' μ ↔ x⁻¹ * x' ∈ K ∧ y = y' := by
  simp [markedTriple, MarkedTriple, QuotientGroup.eq]

/-- An element `z` of `GL n E` sends `(xK, y, μ)` to `(z x K, z y z⁻¹, μ)`. -/
lemma smul_markedTriple (z : GL n E) (x : GL n (𝔸f E)) (y : GL n E) (μ : n) :
    z • markedTriple K x y μ = markedTriple K (toFinGL z * x) (z * y * z⁻¹) μ := rfl

/-- Moving the frame `x` to `x k` conjugates `invAutInFrame y x = x⁻¹ y⁻¹ x` by `k`. -/
lemma invAutInFrame_mul (y : GL n E) (x k : GL n (𝔸f E)) :
    invAutInFrame y (x * k) = k⁻¹ * invAutInFrame y x * k := by
  simp [invAutInFrame, mul_assoc]

/-- The element `invAutInFrame y x = x⁻¹ y⁻¹ x` does not change under `(y, x) ↦ (z y z⁻¹, z x)`. -/
lemma invAutInFrame_conj (z y : GL n E) (x : GL n (𝔸f E)) :
    invAutInFrame (z * y * z⁻¹) (toFinGL z * x) = invAutInFrame y x := by
  simp [invAutInFrame, mul_assoc]

/-- The automorphism `y` in the frame `x` at the split place `w₀`: the inverse transpose of the
component of `x⁻¹ y⁻¹ x` at `w₀`. -/
def localAut (y : GL n E) (x : GL n (𝔸f E)) : GL n (LocField w₀.val) :=
  dualComponent w₀ (invAutInFrame y x)

/-- Moving the frame `x` to `x k` conjugates `localAut w₀ y x` by the inverse transpose of the
component of `k` at `w₀`. -/
lemma localAut_mul (y : GL n E) (x k : GL n (𝔸f E)) :
    localAut w₀ y (x * k) = (dualComponent w₀ k)⁻¹ * localAut w₀ y x * dualComponent w₀ k := by
  simp [localAut, invAutInFrame_mul]

/-- Moving the frame `x` by an element `a` placed at `w₀` conjugates `localAut w₀ y x` by `a`. -/
lemma localAut_mul_conjAtSplit (y : GL n E) (x : GL n (𝔸f E)) (a : GL n (LocField w₀.val)) :
    localAut w₀ y (x * conjAtSplit w₀ a) = a⁻¹ * localAut w₀ y x * a := by
  rw [localAut_mul, dualComponent_conjAtSplit]

/-- The matrix of `dualComponent w₀ a` is the transpose of the component of `a⁻¹` at `w₀`. -/
lemma coe_dualComponent (a : GL n (𝔸f E)) :
    (dualComponent w₀ a).val = (a⁻¹.val.map (evalAt w₀.val))ᵀ := rfl

/-- The characteristic polynomial of `localAut w₀ y x` is that of `y`, read in the completion of
`E` at `w₀`. -/
lemma charpoly_localAut (y : GL n E) (x : GL n (𝔸f E)) :
    (localAut w₀ y x).val.charpoly =
      y.val.charpoly.map ((evalAt w₀.val).comp (algebraMap E (𝔸f E))) := by
  have h_inv : (invAutInFrame y x)⁻¹ = x⁻¹ * toFinGL y * x := by simp [invAutInFrame, mul_assoc]
  have h_conj :
      (x⁻¹ * toFinGL y * x).val.charpoly = y.val.charpoly.map (algebraMap E (𝔸f E)) := by
    rw [Units.val_mul, Units.val_mul, coe_units_inv, charpoly_units_conj', ← charpoly_map]
    rfl
  rw [localAut, coe_dualComponent, charpoly_transpose, charpoly_map, h_inv, h_conj,
    Polynomial.map_map]

variable (K) in
/-- The block of `(xK, y, μ)`: the triples `(x a K, y, μ)`, where `a` runs over the radical of
`localAut w₀ y x`, placed at `w₀`. -/
def tripleBlock (x : GL n (𝔸f E)) (y : GL n E) (μ : n) : Set (MarkedTriple K n) :=
  range fun Y : Multiplicative (Matrix n n (LocField w₀.val)) ↦
    markedTriple K (x * conjAtSplit w₀ (splittingRadical (localAut w₀ y x) Y)) y μ

/-- The points of the block of `(xK, y, μ)` are the triples `(x a K, y, μ)` with `a` in the radical
of `localAut w₀ y x`. -/
lemma mem_tripleBlock {x : GL n (𝔸f E)} {y : GL n E} {μ : n} {p : MarkedTriple K n} :
    p ∈ tripleBlock K w₀ x y μ ↔ ∃ a ∈ (splittingRadical (localAut w₀ y x)).range,
      markedTriple K (x * conjAtSplit w₀ a) y μ = p := by
  simp [tripleBlock]

/-- If `K` consists of unitary similitudes, the block of `(xK, y, μ)` does not depend on the
representative `x` of the coset `xK`. -/
lemma tripleBlock_mul_of_mem (hK : K ≤ GU E n) (x : GL n (𝔸f E)) (y : GL n E) (μ : n)
    {k : GL n (𝔸f E)} (hk : k ∈ K) : tripleBlock K w₀ (x * k) y μ = tripleBlock K w₀ x y μ := by
  -- One inclusion suffices, for `x`, `k` and for `x * k`, `k⁻¹`.
  suffices h_subset : ∀ (x k : GL n (𝔸f E)), k ∈ K →
      tripleBlock K w₀ x y μ ⊆ tripleBlock K w₀ (x * k) y μ by
    refine subset_antisymm ?_ (h_subset x k hk)
    simpa only [mul_inv_cancel_right] using h_subset (x * k) k⁻¹ (inv_mem hk)
  intro x k hk p hp
  obtain ⟨a, ha, rfl⟩ := (mem_tripleBlock w₀).1 hp
  set b : GL n (LocField w₀.val) := dualComponent w₀ k with hb
  have h_mem : b⁻¹ * a * b ∈ (splittingRadical (localAut w₀ y (x * k))).range := by
    simpa only [localAut_mul] using mem_range_splittingRadical_conj ha
  have h_conj : k * conjAtSplit w₀ (b⁻¹ * a * b) * k⁻¹ = conjAtSplit w₀ a := by
    rw [conj_conjAtSplit (hK hk), ← hb]
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  refine (mem_tripleBlock w₀).2 ⟨b⁻¹ * a * b, h_mem, markedTriple_eq_iff.2 ⟨?_, rfl⟩⟩
  rw [← h_conj]
  simpa only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left] using inv_mem hk

/-- All points of a block have the same block: for `b` in the radical of `localAut w₀ y x`, the
triples `(x b K, y, μ)` and `(xK, y, μ)` have the same block. -/
lemma tripleBlock_mul_conjAtSplit (x : GL n (𝔸f E)) (y : GL n E) (μ : n)
    {b : GL n (LocField w₀.val)} (hb : b ∈ (splittingRadical (localAut w₀ y x)).range) :
    tripleBlock K w₀ (x * conjAtSplit w₀ b) y μ = tripleBlock K w₀ x y μ := by
  -- Both blocks have the same radical, which contains `b`; so `a ↦ b * a` is a change of parameter.
  ext p
  rw [mem_tripleBlock, mem_tripleBlock, localAut_mul_conjAtSplit,
    range_splittingRadical_conj_self hb]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨b * a, mul_mem hb ha, by rw [map_mul, mul_assoc]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨b⁻¹ * a, mul_mem (inv_mem hb) ha, by rw [mul_assoc, ← map_mul, mul_inv_cancel_left]⟩

/-- An element `z` of `GL n E` carries the block of `(xK, y, μ)` to the block of
`(z x K, z y z⁻¹, μ)`. -/
lemma smul_tripleBlock (z : GL n E) (x : GL n (𝔸f E)) (y : GL n E) (μ : n) :
    z • tripleBlock K w₀ x y μ = tripleBlock K w₀ (toFinGL z * x) (z * y * z⁻¹) μ := by
  simp only [tripleBlock, smul_set_range, smul_markedTriple, localAut, invAutInFrame_conj,
    mul_assoc (toFinGL z)]

/-- The block of a triple `p = (q, y, μ)`, read at the chosen representative of the coset `q`. -/
def blockOf (p : MarkedTriple K n) : Set (MarkedTriple K n) :=
  tripleBlock K w₀ p.1.out p.2.1 p.2.2

/-- If `K` consists of unitary similitudes, the block of `(xK, y, μ)` can be read at `x`. -/
lemma blockOf_markedTriple (hK : K ≤ GU E n) (x : GL n (𝔸f E)) (y : GL n E) (μ : n) :
    blockOf w₀ (markedTriple K x y μ) = tripleBlock K w₀ x y μ := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  change tripleBlock K w₀ (x : GL n (𝔸f E) ⧸ K).out y μ = tripleBlock K w₀ x y μ
  rw [hk, tripleBlock_mul_of_mem w₀ hK x y μ k.property]

lemma mem_blockOf_self (p : MarkedTriple K n) : p ∈ blockOf w₀ p :=
  (mem_tripleBlock w₀).2 ⟨1, one_mem _, by rw [map_one, mul_one, markedTriple_out]⟩

/-- If `K` consists of unitary similitudes, then for `p` in the block of `q` the block of `z • p` is
the translate by `z` of the block of `q`. -/
lemma blockOf_smul (hK : K ≤ GU E n) (z : GL n E) {p q : MarkedTriple K n}
    (hp : p ∈ blockOf w₀ q) : blockOf w₀ (z • p) = z • blockOf w₀ q := by
  obtain ⟨a, ha, rfl⟩ := (mem_tripleBlock w₀).1 hp
  rw [smul_markedTriple, blockOf_markedTriple w₀ hK, ← smul_tripleBlock,
    tripleBlock_mul_conjAtSplit (hb := ha), blockOf]

end Blocks

/-! ### The classes with reducible polynomial -/

section Reducible

variable {E n : Type} [Field E] [CMBase E] [Fintype n] [DecidableEq n] {𝔑 : 𝓞 E}
  {f : heckeAlgebra n ℂ 𝔑} {w₀ : SplitFinPlace E} {ε : Prop} {u : E[X] → n → ℂ} {x : GL n (𝔸f E)}
  {y : GL n E} {μ : n}

/-- If the level `𝔑` is neat (it is non-zero, and an automorphism of a signed frame that lies in the
level is trivial), a triple `(xK, y, μ)` with `K = levelGU n 𝔑` whose frame `x` satisfies the sign
condition `h_sign` has trivial stabiliser in `GL n E`. -/
lemma stabilizer_markedTriple (hN : IsNeat n 𝔑)
    (h_sign : IsSignedFrame x (eigenReflection ε y μ)) :
    stabilizer (GL n E) (markedTriple (levelGU n 𝔑) x y μ) = ⊥ := by
  refine eq_bot_iff.2 fun z hz ↦ ?_
  rw [mem_stabilizer_iff, smul_markedTriple, eq_comm, markedTriple_eq_iff] at hz
  obtain ⟨h_level, h_comm : y = z * y * z⁻¹⟩ := hz
  have h_mem : x⁻¹ * toFinGL z * x ∈ levelGU n 𝔑 := by rwa [mul_assoc]
  have h_fix : ratConj z (eigenReflection ε y μ) = eigenReflection ε y μ := by
    rw [ratConj_eigenReflection, ← h_comm]
  exact hN.2 h_sign h_mem h_fix

/-- Let the Hecke function `f` have type `(J, χ)` at `w₀`: it sends vectors of level `𝔑` to
`χ`-eigenvectors of `J`. Then left translation by `j ∈ J`, placed at `w₀`, multiplies the function
`heckeCosetFn f` on cosets of the level by `χ j⁻¹`. -/
lemma heckeCosetFn_conjAtSplit_mul {J : Subgroup (GL n (LocField w₀.val))} {χ : J →* ℂ}
    (hJ : f.val ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w₀) J χ) (j : J) (t : GL n (𝔸f E)) :
    heckeCosetFn f (conjAtSplit w₀ j * t : GL n (𝔸f E)) = χ j⁻¹ * heckeCosetFn f t := by
  -- The values of `heckeCosetFn f` are the coefficients of `v`, the image under `f` of the trivial
  -- coset, which is a vector of level `levelGU n 𝔑`; evaluate the eigenvector equation at `t`.
  let π := Representation.ofMulAction ℂ (GL n (𝔸f E)) (GL n (𝔸f E) ⧸ levelGU n 𝔑)
  let v : MonoidAlgebra ℂ (GL n (𝔸f E) ⧸ levelGU n 𝔑) :=
    π.asAlgebraHom f (MonoidAlgebra.single (QuotientGroup.mk 1) 1)
  have h_eigen : π (conjAtSplit w₀ j.val⁻¹) v = χ j⁻¹ • v := hJ single_one_mem_levelSpace j⁻¹
  rw [show heckeCosetFn f = v.coeff from rfl]
  calc _ = v.coeff ((conjAtSplit w₀ j.val⁻¹)⁻¹ • (t : GL n (𝔸f E) ⧸ levelGU n 𝔑)) := by
        rw [map_inv, inv_inv, Quotient.smul_mk, smul_eq_mul]
    _ = (π (conjAtSplit w₀ j.val⁻¹) v).coeff t := (Representation.coeff_ofMulAction _ _ _).symm
    _ = χ j⁻¹ * v.coeff t := by
        rw [h_eigen, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]

/-- If the Hecke function `f` is not zero on the coset of `t`, the inverse transpose of the
component of `t` at `w₀` is an integral matrix. -/
lemma dualComponent_mem_matrix {t : GL n (𝔸f E)} (ht : heckeCosetFn f t ≠ 0) :
    (dualComponent w₀ t).val ∈ (LocInt w₀.val : Set (LocField w₀.val)).matrix :=
  fun i j ↦ mem_Ô.1 ((heckeAlgebra.mem_GUPlus_of_ne_zero ht).2 j i) w₀.val

/-- Moving a frame `x` that satisfies the sign condition by an element `a` at `w₀` keeps the sign
condition and the weight, so the term of `(x a K, y, μ)` is the value of `f` times the weight. -/
lemma countTerm_mul_conjAtSplit (h_sign : IsSignedFrame x (eigenReflection ε y μ))
    (a : GL n (LocField w₀.val)) :
    countTerm ε f u ⟦markedTriple (levelGU n 𝔑) (x * conjAtSplit w₀ a) y μ⟧ =
      heckeCosetFn f (invAutInFrame y (x * conjAtSplit w₀ a)) * u y.val.charpoly μ := by
  have h_sign' : IsSignedFrame (x * conjAtSplit w₀ a) (eigenReflection ε y μ) := by
    simpa [isSignedFrame_mul_iff 1 (conjAtSplit_mem_GU a), ratConj_eigenReflection] using h_sign
  exact countTerm_mk.trans (ite_eq_left h_sign')

/-- Let `x⁻¹ y⁻¹ x` be a unitary similitude. Moving the frame `x` by an element `a` at `w₀`
conjugates its factor `localAut w₀ y x` at `w₀` by `a` and leaves the rest alone. -/
lemma invAutInFrame_mul_conjAtSplit (h_mem : invAutInFrame y x ∈ GU E n)
    (a : GL n (LocField w₀.val)) :
    invAutInFrame y (x * conjAtSplit w₀ a) = conjAtSplit w₀ (a⁻¹ * localAut w₀ y x * a) *
      ((conjAtSplit w₀ (localAut w₀ y x))⁻¹ * invAutInFrame y x) := by
  have h_comm : invAutInFrame y x * conjAtSplit w₀ a =
      conjAtSplit w₀ (localAut w₀ y x * a * (localAut w₀ y x)⁻¹) * invAutInFrame y x :=
    eq_mul_of_mul_inv_eq (conj_conjAtSplit h_mem a)
  rw [invAutInFrame_mul, mul_assoc, h_comm]
  simp only [map_mul, map_inv, mul_assoc]

variable (𝔑 w₀ x y μ) in
/-- The point of the block of `(xK, y, μ)` with parameter `Y`, for the principal level
`K = levelGU n 𝔑`. -/
abbrev blockPoint (Y : Multiplicative (Matrix n n (LocField w₀.val))) :
    MarkedTriple (levelGU n 𝔑) n :=
  markedTriple (levelGU n 𝔑) (x * conjAtSplit w₀ (splittingRadical (localAut w₀ y x) Y)) y μ

lemma tripleBlock_eq_range_blockPoint :
    tripleBlock (levelGU n 𝔑) w₀ x y μ = range (blockPoint 𝔑 w₀ x y μ) := rfl

/-- Two parameters `Y`, `Y'` give the same point of the block if and only if the element of the
radical with parameter `Y⁻¹ * Y'`, placed at `w₀`, lies in the level `levelGU n 𝔑`. -/
lemma blockPoint_eq_iff (Y Y' : Multiplicative (Matrix n n (LocField w₀.val))) :
    blockPoint 𝔑 w₀ x y μ Y = blockPoint 𝔑 w₀ x y μ Y' ↔ Y⁻¹ * Y' ∈
      ((levelGU n 𝔑).comap (conjAtSplit w₀)).comap (splittingRadical (localAut w₀ y x)) := by
  simp only [markedTriple_eq_iff, and_true, Subgroup.mem_comap, map_mul, map_inv,
    _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/-- If `𝔑 ≠ 0` and the frame `x` satisfies the sign condition `h_sign`, then `countTerm ε f u`
(the value of `f` times the weight `u`, at classes with the sign condition) is non-zero at only
finitely many points `(x a K, y, μ)` of the block of `(xK, y, μ)`. Here `K = levelGU n 𝔑` and `a`
runs over the radical `1 + e M_n (1 - e)` of `localAut w₀ y x`, placed at `w₀` by `conjAtSplit w₀`;
`localAut w₀ y x` is the inverse transpose of the component of `x⁻¹ y⁻¹ x` at `w₀`, and `e` is its
chosen idempotent. -/
lemma finite_tripleBlock_inter_support (h𝔑 : 𝔑 ≠ 0)
    (h_sign : IsSignedFrame x (eigenReflection ε y μ)) :
    (tripleBlock (levelGU n 𝔑) w₀ x y μ ∩
      {p : MarkedTriple (levelGU n 𝔑) n | countTerm ε f u ⟦p⟧ ≠ 0}).Finite := by
  -- Let `g = localAut w₀ y x` have idempotent `p(g)`. If the term at `a` is not zero then
  -- `a⁻¹ g a` is integral, and `p(a⁻¹ g a)` is a parameter of `a`; these lie in a compact set.
  set g : GL n (LocField w₀.val) := localAut w₀ y x
  set p : (LocField w₀.val)[X] := splittingPoly g.val.charpoly
  have h_compact : IsCompact ((fun M : Matrix n n (LocField w₀.val) ↦ ofAdd (aeval M p)) ''
      (LocInt w₀.val : Set (LocField w₀.val)).matrix) :=
    (isCompact_LocInt w₀.val).matrix.image (continuous_ofAdd.comp p.continuous_aeval)
  rw [tripleBlock_eq_range_blockPoint]
  refine finite_range_inter_support (F := fun q ↦ countTerm ε f u ⟦q⟧) ?_ blockPoint_eq_iff
    h_compact fun Y hY ↦ ?_
  · exact (isOpen_comap_conjAtSplit h𝔑).preimage (continuous_radicalHom _)
  set a : GL n (LocField w₀.val) := splittingRadical g Y
  have h_int : (a⁻¹ * g * a).val ∈ (LocInt w₀.val : Set (LocField w₀.val)).matrix := by
    rw [countTerm_mul_conjAtSplit h_sign] at hY
    rw [← localAut_mul_conjAtSplit]
    exact dualComponent_mem_matrix (left_ne_zero_of_mul hY)
  -- This parameter gives the same element `a` of the radical, so the same point of the block.
  exact ⟨ofAdd (aeval (a⁻¹ * g * a).val p), mem_image_of_mem _ h_int,
    by rw [blockPoint, splittingRadical_aeval_conj ⟨Y, rfl⟩]⟩

/-- Let `f` have type `(J, χ)` at the split place `w₀` (it turns vectors fixed by the level into
`χ`-eigenvectors of `J`), let the frame `x` satisfy the sign condition and let `x⁻¹ y⁻¹ x` be a
unitary similitude. The block of `(xK, y, μ)` consists of the `(x a K, y, μ)` with `a` in the
radical of `localAut w₀ y x`, placed at `w₀`. If `χ` is not trivial at some `j ∈ J` in this radical,
the sum over the block of `countTerm ε f u` (the value of `f` times the weight `u`) is zero. -/
lemma finsum_tripleBlock_eq_zero {J : Subgroup (GL n (LocField w₀.val))} {χ : J →* ℂ}
    (hJ : f.val ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w₀) J χ)
    (h_sign : IsSignedFrame x (eigenReflection ε y μ)) (h_mem : invAutInFrame y x ∈ GU E n)
    {j : J} (hj : j.val ∈ (splittingRadical (localAut w₀ y x)).range) (hχ : χ j ≠ 1) :
    ∑ᶠ p ∈ tripleBlock (levelGU n 𝔑) w₀ x y μ, countTerm ε f u ⟦p⟧ = 0 := by
  -- Write `j g = d⁻¹ g d` with `d` in the radical. Translation by `d` permutes the block and
  -- multiplies each term by `χ j⁻¹ ≠ 1`.
  set g : GL n (LocField w₀.val) := localAut w₀ y x
  obtain ⟨D, hD⟩ := exists_splittingRadical_conj hj
  rw [tripleBlock_eq_range_blockPoint]
  refine finsum_mem_range_eq_zero_of_translate (F := fun p ↦ countTerm ε f u ⟦p⟧) (a := D)
    (c := χ j⁻¹) blockPoint_eq_iff (by simpa using hχ) fun Y ↦ ?_
  set d : GL n (LocField w₀.val) := splittingRadical g D
  set a : GL n (LocField w₀.val) := splittingRadical g Y
  have h_comm : Commute a⁻¹ j.val := by
    obtain ⟨Z, hZ⟩ := hj
    simpa only [hZ] using ((Commute.all Y Z).map (splittingRadical g)).inv_left
  have h_conj : (d * a)⁻¹ * g * (d * a) = j * (a⁻¹ * g * a) :=
    calc _ = a⁻¹ * (d⁻¹ * g * d) * a := by group
      _ = j * (a⁻¹ * g * a) := by simp only [hD, mul_assoc, h_comm.left_comm]
  have h_value : heckeCosetFn f (invAutInFrame y (x * conjAtSplit w₀ (d * a))) =
      χ j⁻¹ * heckeCosetFn f (invAutInFrame y (x * conjAtSplit w₀ a)) := by
    rw [invAutInFrame_mul_conjAtSplit h_mem, invAutInFrame_mul_conjAtSplit h_mem, h_conj, map_mul,
      mul_assoc (conjAtSplit w₀ j.val), heckeCosetFn_conjAtSplit_mul hJ]
  rw [countTerm_mul_conjAtSplit h_sign, countTerm_mul_conjAtSplit h_sign,
    map_mul (splittingRadical g), h_value, mul_assoc]

/-- Let `𝔑` be neat (non-zero, with only trivial automorphisms of signed frames) and let `f` be a
regular Hecke function of level `𝔑` (its terms vanish unless the characteristic polynomial is
separable) with the cuspidal type `(J, χ)` at the split place `w₀` (`f` turns vectors fixed by the
level into `χ`-eigenvectors of `J`, and `χ` is non-trivial on `J` in each proper unipotent
radical). If the weight `u` vanishes on irreducible polynomials, so that only classes with reducible
characteristic polynomial contribute, then `countTerm ε f u` (the value of `f` times `u`, at classes
with the sign condition of `ε`) has sum zero over all classes, for the marked count (`ε` true) and
for the definite count (`ε` false). -/
lemma finsum_countTerm_eq_zero_of_reducible (hN : IsNeat n 𝔑) (h_regular : IsRegularHecke f)
    {J : Subgroup (GL n (LocField w₀.val))} {χ : J →* ℂ} (hχ : IsCuspidalType J χ)
    (hJ : f.val ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w₀) J χ)
    (hu : ∀ P : E[X], Irreducible P → u P = 0) (ε : Prop) :
    ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), countTerm ε f u c = 0 := by
  classical
  have hK : levelGU n 𝔑 ≤ GU E n := inf_le_left
  refine finsum_orbits_eq_zero_of_blocks (blockOf w₀) (mem_blockOf_self w₀) (blockOf_smul w₀ hK)
    fun s hs ↦ ?_
  obtain ⟨x, y, μ, rfl⟩ : ∃ x y μ, markedTriple (levelGU n 𝔑) x y μ = s :=
    ⟨_, _, _, markedTriple_out s⟩
  obtain ⟨h_sign, hf_ne, hu_ne⟩ : IsSignedFrame x (eigenReflection ε y μ) ∧
      heckeCosetFn f (invAutInFrame y x) ≠ 0 ∧ u y.val.charpoly μ ≠ 0 := by
    rwa [markedTriple, countTerm_mk, ite_ne_right_iff, mul_ne_zero_iff] at hs
  -- The characteristic polynomial of `g = localAut w₀ y x` is that of `y`: separable as `f` is
  -- regular, and not irreducible as the weight `u` is not zero at it. So the idempotent of `g` is
  -- not `0` or `1`, and `χ` is not trivial on the radical of `g`.
  have h_sep : (localAut w₀ y x).val.charpoly.Separable := by
    simpa only [charpoly_localAut] using (h_regular hf_ne).map
  have h_red : ¬Irreducible (localAut w₀ y x).val.charpoly := fun h ↦ by
    rw [charpoly_localAut] at h
    exact hu_ne (congrFun (hu _ ((charpoly_monic y.val).irreducible_of_irreducible_map _ _ h)) μ)
  have : Nonempty n := ⟨μ⟩
  obtain ⟨j, hj, hχj⟩ := hχ.exists_mem_range_splittingRadical h_sep h_red
  rw [blockOf_markedTriple w₀ hK]
  exact ⟨stabilizer_markedTriple hN h_sign, finite_tripleBlock_inter_support hN.1 h_sign,
    finsum_tripleBlock_eq_zero hJ h_sign (heckeAlgebra.mem_GUPlus_of_ne_zero hf_ne).1 hj hχj⟩

end Reducible

/-! ### The classes with irreducible polynomial -/

section Irreducible

variable {E n : Type} [Field E] [CMBase E] [Fintype n] [DecidableEq n] {𝔑 : 𝓞 E}

open Classical in
/-- The signs of `eigenReflection ε y μ` at the roots of `y`, place by place: `-1` at the place
`v₀` and the roots other than `μ` if `ε` holds, and `1` in all other cases. -/
def reflectionSigns (ε : Prop) (μ : n) (v : InfinitePlace E) (i : n) : ℤˣ :=
  if v = v₀ ∧ ε ∧ i ≠ μ then -1 else 1

omit [Fintype n] in
/-- In the definite case all signs are `1`. -/
lemma reflectionSigns_false (μ : n) : reflectionSigns (E := E) False μ = 1 :=
  funext₂ fun v i ↦ by simp [reflectionSigns]

/-- In odd rank the marked signs have product one: `-1` occurs `card n - 1` times. -/
lemma prod_reflectionSigns (hn : Odd (Fintype.card n)) (μ : n) :
    ∏ v : InfinitePlace E, ∏ i : n, reflectionSigns True μ v i = 1 := by
  refine Finset.prod_eq_one fun v _ ↦ ?_
  by_cases hv : v = v₀
  · simpa [reflectionSigns, hv, Finset.prod_ite, Finset.filter_ne'] using
      (hn.tsub_odd odd_one).neg_one_pow (α := ℤˣ)
  · simp [reflectionSigns, hv]

/-- The matrix that enters the sign condition at the infinite place `v` is `p(y)` under the
embedding `Φ v`, where `p` takes the values `reflectionSigns ε μ v` at the numbered roots of the
characteristic polynomial of `y`. -/
lemma ite_eigenReflection_eq (ε : Prop) (y : GL n E) (μ : n) (v : InfinitePlace E) :
    (if v = v₀ then eigenReflection ε y μ else 1) =
      aeval (y.val.map (Φ v)) (Lagrange.interpolate Finset.univ (numberedRoots (Φ v) y.val.charpoly)
        fun i : n ↦ (reflectionSigns ε μ v i : ℂ)) := by
  by_cases h : v = v₀ ∧ ε
  · obtain ⟨rfl, hε⟩ := h
    have h_signs : (fun i : n ↦ (reflectionSigns ε μ (v₀ : InfinitePlace E) i : ℂ)) =
        fun i : n ↦ if i = μ then 1 else -1 := by
      ext i
      by_cases hi : i = μ <;> simp [reflectionSigns, hε, hi]
    rw [ite_eq_left rfl, eigenReflection, ite_eq_left hε, h_signs]
  · -- All signs are `1`, and both sides are the identity matrix.
    have h_signs : (fun i : n ↦ (reflectionSigns ε μ v i : ℂ)) = 1 := by
      ext i; simp [reflectionSigns, ← and_assoc, h]
    rw [h_signs, Lagrange.interpolate_one (numberedRoots (Φ v) y.val.charpoly).injective.injOn
      ⟨μ, Finset.mem_univ μ⟩, map_one]
    refine ite_eq_right_iff.2 fun hv ↦ ?_
    rw [eigenReflection, ite_eq_right fun hε ↦ h ⟨hv, hε⟩, map_one]

/-- Let `y` have irreducible characteristic polynomial, and let `x⁻¹ y⁻¹ x` be a frame for the
scalar form `ν • 1`. Then `x` is a signed frame for `eigenReflection ε y μ` (a frame for some
hermitian form with the positivity that this matrix prescribes at `v₀`) if and only if `y` is an
elliptic similitude of multiplier `ν`, with the signs `reflectionSigns ε μ` at its roots, of a form
whose Gram matrix in the frame `x` is `c • 1` for a unit `c` of the integral adeles `Ô ℚ`. -/
lemma isSignedFrame_iff_hasSignType {x : GL n (𝔸f E)} {y : GL n E} {ν : ℚ}
    (h_irr : Irreducible y.val.charpoly) (hν : IsScalarFrame (invAutInFrame y x) ν) (ε : Prop)
    (μ : n) :
    IsSignedFrame x (eigenReflection ε y μ) ↔ HasSignType (reflectionSigns ε μ) ν y
      {m : Matrix n n (𝔸f E) | ∃ c : (Ô ℚ)ˣ, m = finAdeleIncl ℚ E c • 1} x := by
  have : Nonempty n := ⟨μ⟩
  have h_inv : (x⁻¹ * toFinGL y * x)⁻¹ = invAutInFrame y x := by simp [invAutInFrame, mul_assoc]
  have h_fix : ratConj y (eigenReflection ε y μ) = eigenReflection ε y μ := by
    rw [ratConj_eigenReflection, mul_inv_cancel_right]
  -- For a form `β`, both sides have the same frame condition and the same positivity conditions.
  constructor
  · rintro ⟨β, h_frame, h_pos⟩
    obtain ⟨h_form, h_root⟩ :=
      IsSignedFrameFor.similitude_and_root_norm ⟨h_frame, h_pos⟩ (by rwa [h_inv]) h_fix
    exact ⟨β, ⟨h_irr, hν.1.ne', h_form, h_root⟩, h_frame,
      by simpa only [ite_eigenReflection_eq] using h_pos⟩
  · rintro ⟨β, -, h_frame, h_pos⟩
    exact ⟨β, h_frame, by simpa only [ite_eigenReflection_eq] using h_pos⟩

/-- The term of the marked count: `countTerm` with the sign condition on the class of
`(xK, y, μ)` taken for the reflection attached to the marked root `μ` of `y`. -/
abbrev markedTerm (f : heckeAlgebra n ℂ 𝔑) (w : E[X] → n → ℂ) :
    orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n) → ℂ :=
  countTerm True f w

/-- The term of the definite count: `countTerm` with the sign condition on the class of
`(xK, y, μ)` taken with all signs `+1`. -/
abbrev definiteTerm (f : heckeAlgebra n ℂ 𝔑) (w : E[X] → n → ℂ) :
    orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n) → ℂ :=
  countTerm False f w

/-- Let the rank be odd and let `f` be a Hecke function of level `𝔑`. If the weight `u` vanishes on
the polynomials that are not irreducible, so that only classes with irreducible characteristic
polynomial contribute, the sum over all classes of `markedTerm f u` (`f` times `u`, with the signs
of the marked root) is that of `definiteTerm f u` (the same with all signs `+1`): a change of signs
of the frame matches the classes. -/
lemma finsum_markedTerm_eq_of_irreducible (hn : Odd (Fintype.card n)) (f : heckeAlgebra n ℂ 𝔑)
    {u : E[X] → n → ℂ} (hu : ∀ P : E[X], ¬Irreducible P → u P = 0) :
    ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), markedTerm f u c =
      ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), definiteTerm f u c := by
  classical
  -- The marked signs have product one, so they give a permutation `σ` of the classes, induced on
  -- the triples `(xK, y, μ)` by a move `x ↦ U * x` of the frame, with `U` depending on `y`, `μ`.
  obtain ⟨σ, hσ⟩ :=
    exists_hasSignType_mul_iff (reflectionSigns True) (prod_reflectionSigns hn) (levelGU n 𝔑)
  refine finsum_eq_of_bijective σ σ.bijective ?_
  rintro ⟨⟨x⟩, y, μ⟩
  -- `U` changes the signs, commutes with the centraliser of `y`, and induces `σ` on this orbit.
  obtain ⟨U, hU_type, hU_comm, hU_move⟩ := hσ y μ
  have h_move : σ ⟦markedTriple (levelGU n 𝔑) x y μ⟧ =
      ⟦markedTriple (levelGU n 𝔑) (U * x) y μ⟧ := hU_move x
  -- The move keeps the argument of `f`; it remains to match the two sign conditions.
  have h_aut : invAutInFrame y (U * x) = invAutInFrame y x := by
    have h_comm : Commute (toFinGL y)⁻¹ U := by
      simpa using hU_comm y⁻¹ (Commute.refl y).inv_right
    simp [invAutInFrame, mul_assoc, h_comm.left_comm]
  change countTerm True f u ⟦markedTriple (levelGU n 𝔑) x y μ⟧ =
    countTerm False f u (σ ⟦markedTriple (levelGU n 𝔑) x y μ⟧)
  rw [h_move, markedTriple, markedTriple, countTerm_mk, countTerm_mk, h_aut]
  by_cases h_zero : heckeCosetFn f (invAutInFrame y x) * u y.val.charpoly μ = 0
  · rw [h_zero, ite_self, ite_self]
  have h_irr : Irreducible y.val.charpoly :=
    by_contra fun h ↦ right_ne_zero_of_mul h_zero (congrFun (hu _ h) μ)
  obtain ⟨ν, hν : IsScalarFrame (invAutInFrame y x) ν⟩ :=
    (heckeAlgebra.mem_GUPlus_of_ne_zero (left_ne_zero_of_mul h_zero)).1
  refine if_congr ?_ rfl rfl
  rw [isSignedFrame_iff_hasSignType h_irr hν,
    isSignedFrame_iff_hasSignType (ν := ν) h_irr (by rwa [h_aut]),
    ← hU_type, reflectionSigns_false, one_mul]

end Irreducible

/-! ### The comparison -/

section Comparison

variable {E n : Type} [Field E] [CMBase E] [Fintype n] [DecidableEq n] {𝔑 : 𝓞 E}

/-- The marked and the definite orbit sums agree. Assume that `𝔑` is neat and the rank is odd; that
`f` is a regular Hecke function of level `levelGU n 𝔑`; that in every representation `f` sends
vectors of that level to `χ`-eigenvectors of `J`, acting through `conjAtSplit` at the split place
`w₀`, where `(J, χ)` is a cuspidal type (`χ` is non-trivial on `J` within each proper unipotent
radical); and that with weight `1` finitely many classes have a non-zero marked term and finitely
many a non-zero definite term. Then for every weight `w` the sums over all classes of the marked and
of the definite terms are equal. -/
lemma finsum_markedTerm_eq_finsum_definiteTerm (hN : IsNeat n 𝔑) (hn : Odd (Fintype.card n))
    {f : heckeAlgebra n ℂ 𝔑} (h_regular : IsRegularHecke f) {w₀ : SplitFinPlace E}
    {J : Subgroup (GL n (LocField w₀.val))} {χ : J →* ℂ} (hχ : IsCuspidalType J χ)
    (hJ : f.val ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w₀) J χ) (w : E[X] → n → ℂ)
    (h_marked : (markedTerm f 1).support.Finite)
    (h_definite : (definiteTerm f 1).support.Finite) :
    ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), markedTerm f w c =
      ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), definiteTerm f w c := by
  classical
  -- Split `w` into the part `u` on the polynomials that are not irreducible, for which both sums
  -- vanish, and the rest `w - u`, for which a change of signs matches the classes.
  let u (P : E[X]) : n → ℂ := if Irreducible P then 0 else w P
  have h_split (ε : Prop) (h_finite : (countTerm ε f 1).support.Finite) :
      ∑ᶠ c, countTerm ε f w c = ∑ᶠ c, countTerm ε f (w - u) c := by
    have h_red : ∑ᶠ c, countTerm ε f u c = 0 :=
      finsum_countTerm_eq_zero_of_reducible hN h_regular hχ hJ (fun P hP ↦ ite_eq_left hP) ε
    rw [finsum_countTerm_eq_sum u h_finite] at h_red
    simp only [finsum_countTerm_eq_sum _ h_finite, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
      h_red, sub_zero]
  calc ∑ᶠ c, markedTerm f w c = ∑ᶠ c, markedTerm f (w - u) c := h_split True h_marked
    _ = ∑ᶠ c, definiteTerm f (w - u) c :=
      finsum_markedTerm_eq_of_irreducible hn f fun P hP ↦ sub_eq_zero.2 (ite_eq_right hP).symm
    _ = ∑ᶠ c, definiteTerm f w c := (h_split False h_definite).symm

/-- The sums of `countTerm ε f w` over all classes agree for `ε = True` (the marked count) and
`ε = False` (the definite count): the level `𝔑` is neat, the rank is odd, `f` is a regular Hecke
function (its terms vanish unless the characteristic polynomial is separable) of cuspidal type
`(J, χ)` at the split place `w₀`, and with weight `1` finitely many classes have a non-zero term.

Known result: the comparison of orbit sums in the simple trace formula on a definite group. -/
lemma finsum_countTerm_marked_eq_definite (hN : IsNeat n 𝔑) (hn : Odd (Fintype.card n))
    {f : heckeAlgebra n ℂ 𝔑} (h_regular : IsRegularHecke f) {w₀ : SplitFinPlace E}
    {J : Subgroup (GL n (LocField w₀.val))} {χ : J →* ℂ} (hχ : IsCuspidalType J χ)
    (hJ : f.val ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w₀) J χ) (w : E[X] → n → ℂ)
    (h_finite : ∀ ε : Prop, (countTerm ε f 1).support.Finite) :
    ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), countTerm True f w c =
      ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), countTerm False f w c :=
  finsum_markedTerm_eq_finsum_definiteTerm hN hn h_regular hχ hJ w (h_finite True) (h_finite False)

end Comparison

end New.Variety

end
end
end

section
/-!
# Test vectors, and the regular Hecke element that does not kill them

A test vector has a cuspidal type at one split place and is spherical at another.

* `New.Variety.exists_local_hecke_element`: a Hecke element that averages against a character at one
  place.
* `New.Variety.exists_test_function`: the test function `b₁ b₀`, with `b₀` averaging against the
  type at `w₀` and `b₁` acting as a central translate of an injective operator `U_t` at `w₁`.

Conventions: `New.Variety.levelGU` is the principal level `K(𝔑)`, `New.Variety.conjAtSplit` embeds
`GL(E_w)` at a split place `w` into the adelic group, `New.Variety.GU` is the group of similitudes
of the standard form, `New.proIwahori` is the pro-p Iwahori subgroup, and `New.Variety.heckeAlgebra`
is the Hecke algebra inside the group ring, acting through `asAlgebraHom`.

Notions from other files:
* `New.Variety.SplitFinPlace`: The finite places w of E with w̄ ≠ w, that is, those split over the
  maximal real subfield.
* `New.Variety.IsRegularHecke`: f is regular if f(x⁻¹y⁻¹x) ≠ 0, with y in GL_n(E) and x adelic,
  forces the characteristic polynomial of y to be separable.
* `New.Variety.dualComponent`: The inverse transpose of the component at a split place; a left
  inverse of `New.Variety.conjAtSplit`.
* `New.iwahoriHeckeHom`: t ↦ U_t, the mean over `New.proIwahori` composed with the action of a
  dominant diagonal t, on the vectors fixed by `New.proIwahori`.
* `New.Variety.GUPlus`: The monoid of similitudes `g` whose inverse has integral entries, that is,
  which enlarge the standard lattice.

## Relation to the literature

Known; see `Lib.Shimura.TraceFormula.MarkedDefiniteSums` for sources.
-/

@[expose] public section

open NumberField Matrix Polynomial Submodule Set Subgroup Valued

namespace New.Variety

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {𝔑 : 𝓞 E}
  {W : Type} [AddCommGroup W] [Module ℂ W]

/-- `v` is a test vector for `π` at the split places `w₀` and `w₁`: it is nonzero, has the
cuspidal type `(J, χ)` at `w₀` and is spherical at `w₁`. The local groups act through
`conjAtSplit`, and the level at `w` is the preimage of `levelGU (Fin a) 𝔑` under
`conjAtSplit w`. -/
structure IsTestVector (𝔑 : 𝓞 E) (π : Representation ℂ (GL (Fin a) (𝔸f E)) W) (v : W)
    (w₀ w₁ : SplitFinPlace E) {J : Subgroup (GL (Fin a) (LocField w₀.val))} (χ : J →* ℂ) :
    Prop where
  /-- The two places are distinct. -/
  place_ne : w₀.val ≠ w₁.val
  /-- `𝔑` does not lie in the conjugate of `w₀`. -/
  notMem_star_fst : 𝔑 ∉ (star w₀.val).asIdeal
  /-- `𝔑` lies in `w₁`. -/
  mem_snd : 𝔑 ∈ w₁.val.asIdeal
  /-- `𝔑` does not lie in the conjugate of `w₁`. -/
  notMem_star_snd : 𝔑 ∉ (star w₁.val).asIdeal
  /-- The level at `w₀` lies in `J`. -/
  level_le : (levelGU (Fin a) 𝔑).comap (conjAtSplit w₀) ≤ J
  /-- `J` lies in the maximal compact subgroup at `w₀`. -/
  le_localIntGL : J ≤ localIntGL (Fin a) w₀.val
  /-- `χ` is non-trivial on the part of `J` in every unipotent radical. -/
  isCuspidalType : IsCuspidalType J χ
  /-- The level at `w₁` lies in the pro-`p` Iwahori subgroup. -/
  level_le_proIwahori : (levelGU (Fin a) 𝔑).comap (conjAtSplit w₁) ≤ proIwahori
  /-- The vector is nonzero. -/
  ne_zero : v ≠ 0
  /-- `J` acts on `v` by `χ`. -/
  isEigenvector : v ∈ levelSpace (π.comp (conjAtSplit w₀)) J χ
  /-- The maximal compact subgroup at `w₁` fixes `v`. -/
  fixed : v ∈ levelSpace (π.comp (conjAtSplit w₁)) (localIntGL (Fin a) w₁.val)

/-- Averaging at one split place `w` of the CM field `E` whose conjugate does not contain `𝔑`, for a
representation `π` of `GL_a(𝔸f E)` on `W`, with the local group `GL_a(E_w)` acting through
`conjAtSplit w`. Let `J ≤ GL_a(O_w)` contain the local level, let `χ` be a character of `J` trivial
on it, let `t ∈ GL_a(E_w)`, and let `z` be central with `z · conjAtSplit w t` in `GUPlus`. Then some
Hecke element `b` is supported on the elements `conjAtSplit w j * z * conjAtSplit w t` for `j ∈ J`,
sends vectors of level `𝔑` to vectors on which `J` acts by `χ`, and satisfies `(T * π z⁻¹)(b x) = y`
for every endomorphism `T` of `W` and all `x`, `y` with `T(π(conjAtSplit w (j t)) x) = χ j • y` for
all `j ∈ J`. -/
lemma exists_local_hecke_element (π : Representation ℂ (GL (Fin a) (𝔸f E)) W)
    {w : SplitFinPlace E} {J : Subgroup (GL (Fin a) (LocField w.val))} {z : GL (Fin a) (𝔸f E)}
    (hJ : J ≤ localIntGL (Fin a) w.val) (χ : J →* ℂ)
    (hχ : ∀ g : GL (Fin a) (LocField w.val), conjAtSplit w g ∈ levelGU (Fin a) 𝔑 →
      ∃ hg : g ∈ J, χ ⟨g, hg⟩ = 1)
    (hw : 𝔑 ∉ (star w.val).asIdeal) (t : GL (Fin a) (LocField w.val))
    (hz : ∀ g : GL (Fin a) (𝔸f E), Commute g z) (hzt : z * conjAtSplit w t ∈ GUPlus E (Fin a)) :
    ∃ b : heckeAlgebra (Fin a) ℂ 𝔑,
      b.val ∈ spanOn ℂ (range fun j : J ↦ conjAtSplit w j * (z * conjAtSplit w t)) ∧
      b.val ∈ fixedToEigen (levelGU (Fin a) 𝔑) (conjAtSplit w) J χ ∧
      ∀ {x : W} (T : Module.End ℂ W) (y : W),
        (∀ j : J, T (π (conjAtSplit w (j.val * t)) x) = χ j • y) →
          (T * π z⁻¹) (π.asAlgebraHom b x) = y := by
  -- Let `U ≤ J` be the open subgroup of the `j` with `j` and `t⁻¹ j t` both of level `𝔑`. The
  -- element `b` is the average of `(χ j)⁻¹ • [r j]` over representatives `j` of `J ⧸ U`.
  let r (j : J) : GL (Fin a) (𝔸f E) := conjAtSplit w j * (z * conjAtSplit w t)
  have hχ_ne (j : J) : χ j ≠ 0 := (χ.toHomUnits j).ne_zero
  have h𝔑_ne : 𝔑 ≠ 0 := (ne_of_mem_of_not_mem (zero_mem _) hw).symm
  let L : OpenSubgroup (GL (Fin a) (LocField w.val)) :=
    ⟨(levelGU (Fin a) 𝔑).comap (conjAtSplit w), isOpen_comap_conjAtSplit h𝔑_ne⟩
  let L' : OpenSubgroup (GL (Fin a) (LocField w.val)) :=
    L ⊓ L.comap (MulAut.conj t⁻¹) (IsTopologicalGroup.continuous_conj _)
  let U : Subgroup J := L'.subgroupOf J
  -- An open subgroup has finite index in the compact group `localIntGL`, hence in `J`.
  let h_fin : Fintype (J ⧸ U) := U.fintypeOfIndexNeZero fun h_index ↦
    (isCompact_localIntGL _).relIndex_ne_zero L'.isOpen' (relIndex_eq_zero_of_le_right hJ h_index)
  let f (j : J) : ℂ := (χ j * Fintype.card (J ⧸ U))⁻¹
  let b : MonoidAlgebra ℂ (GL (Fin a) (𝔸f E)) := ∑ q : J ⧸ U, f q.out • .single (r q.out) 1
  have h_supp : b ∈ spanOn ℂ (range r) :=
    sum_smul_mem _ _ fun q _ ↦ subset_span ⟨r q.out, mem_range_self q.out, rfl⟩
  -- On a vector `x` of level `𝔑` of any representation `ρ`, `b` acts as the operator `heckeFun`
  -- of `f` on `J` applied to `ρ (r 1) x`, which `U` fixes because `z` is central and `t⁻¹ U t`
  -- has level `𝔑`.
  have h_eigen : b ∈ fixedToEigen (levelGU (Fin a) 𝔑) (conjAtSplit w) J χ := by
    intro V _ _ ρ x hx
    have h_fix : ρ (r 1) x ∈ levelSpace (ρ.comp ((conjAtSplit w).domRestrict J)) U := by
      refine mem_levelSpace.mpr fun k ↦ ?_
      -- `t⁻¹ k t` has level `𝔑`, so it fixes `x`
      have h_fix_k :
          ρ (conjAtSplit w (MulAut.conj t⁻¹ ((k : J) : GL (Fin a) (LocField w.val)))) x = x := by
        simpa using mem_levelSpace.mp hx ⟨_, k.property.right⟩
      simpa [r, ← mul_apply_eq_comp, ← map_mul, mul_assoc, (hz _).left_comm] using
        congrArg (ρ (r 1)) h_fix_k
    have h_right (j : J) (k : U) : f (j * k) = f j := by
      obtain ⟨hk_J, hχ_k⟩ := hχ _ k.property.left
      simp [f, show χ k = 1 from hχ_k]
    have h_left (j : J) (k : (⊤ : Subgroup J)) : χ.domRestrict ⊤ k * f (k * j) = f j := by
      have hk_ne : χ k ≠ 0 := hχ_ne k
      simp [f, field]
    simpa [b, r, heckeFun, finsum_eq_sum_of_fintype] using
      heckeFun_mem_levelSpace (toFinite _) h_right h_left h_fix
  -- `b` is in the Hecke algebra by `mem_heckeAlgebra_of_mem_fixedToEigen`. Each `r j` lies in
  -- `GUPlus` (from `hJ` and `hzt`) and commutes with every `d` that commutes with the image of
  -- `conjAtSplit w` (from `hz`). Invariance under the level at `w` is `h_eigen`, since `χ` is
  -- trivial on that level.
  have h_terms : ∀ g ∈ range r, g ∈ GUPlus E (Fin a) ∧
      ∀ d : GL (Fin a) (𝔸f E), (∀ m : GL (Fin a) (LocField w.val), Commute d (conjAtSplit w m)) →
        Commute d g := by
    rintro _ ⟨j, rfl⟩
    refine ⟨mul_mem ⟨by simp, ?_⟩ hzt, fun d hd ↦ by simp [r, hd _, hz]⟩
    exact (conjAtSplit_mem_intGL_iff.mpr (hJ j.property)).isIntMatrix_inv
  have h_hecke : b ∈ heckeAlgebra (Fin a) ℂ 𝔑 := by
    refine mem_heckeAlgebra_of_mem_fixedToEigen hw h_supp h_terms fun V _ _ ρ x hx l ↦ ?_
    obtain ⟨hl, hχl⟩ := hχ _ l.property
    simpa [hχl] using h_eigen hx ⟨l, hl⟩
  refine ⟨⟨b, h_hecke⟩, h_supp, h_eigen, fun {x} T y hT ↦ ?_⟩
  -- The central `z` cancels, and each term of the average contributes `y / #(J ⧸ U)`.
  have h_card : (Fintype.card (J ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h_term (j : J) :
      f j • T (π z⁻¹ (π (r j) x)) = (Fintype.card (J ⧸ U) : ℂ)⁻¹ • y := by
    have h_cancel : z⁻¹ * r j = conjAtSplit w (j.val * t) := by simp [r, (hz _).left_comm]
    have h_act : π z⁻¹ (π (r j) x) = π (conjAtSplit w (j.val * t)) x := by
      rw [← h_cancel, map_mul π z⁻¹ (r j), mul_apply_eq_comp]
    have h_coeff : f j * χ j = (Fintype.card (J ⧸ U) : ℂ)⁻¹ := by simp [f, hχ_ne]
    rw [h_act, hT j, smul_smul, h_coeff]
  calc (T * π z⁻¹) (π.asAlgebraHom (⟨b, h_hecke⟩ : heckeAlgebra (Fin a) ℂ 𝔑) x)
      = ∑ q : J ⧸ U, f q.out • T (π z⁻¹ (π (r q.out) x)) := by simp [b]
    _ = ∑ _q : J ⧸ U, (Fintype.card (J ⧸ U) : ℂ)⁻¹ • y :=
        Finset.sum_congr rfl fun q _ ↦ h_term q.out
    _ = y := by simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, h_card]

/-- `I t I · I s I ⊆ I (t s) I` for the pro-`p` Iwahori subgroup `I = proIwahori` and dominant
diagonal `t`, `s`. -/
lemma dominant_doubleCoset_mul {w : SplitFinPlace E} {t s : Fin a → (LocField w.val)ˣ}
    (ht : t ∈ dominantTorus) (hs : s ∈ dominantTorus) (k l k' l' : proIwahori) :
    ∃ k'' l'' : proIwahori,
      k.val * diagGL t * l.val * (k'.val * diagGL s * l'.val) =
        k''.val * diagGL (t * s) * l''.val := by
  -- Write `l k' = u · (u⁻¹ l k')`, move `u` left across `t` and the rest right across `s`.
  obtain ⟨u, hu, h_rest⟩ : ∃ u ∈ unitriangular id (LocField w.val) ⊓ proIwahori,
      (diagGL s)⁻¹ * (u⁻¹ * (l * k').val) * diagGL s ∈ proIwahori :=
    exists_unipotent_conj_mem_proIwahori hs (l * k').property
  refine ⟨k * ⟨_, conj_unitriangular_mem_proIwahori ht hu⟩, ⟨_, h_rest⟩ * l', ?_⟩
  simp [mul_assoc]

/-- The adelic elements `g` such that `dualComponent w g`, the inverse transpose of the component
of `g` at `w`, lies in a double coset `I s I`, where `I = proIwahori` and `s` is diagonal and
strictly dominant. -/
def strictlyDominantAt (w : SplitFinPlace E) : Set (GL (Fin a) (𝔸f E)) :=
  {g : GL (Fin a) (𝔸f E) | ∃ s : Fin a → (LocField w.val)ˣ, StrictMono (fun i ↦ v (s i).val) ∧
    ∃ k l : proIwahori, dualComponent w g = k.val * diagGL s * l.val}

/-- The set `New.Variety.strictlyDominantAt w` is closed under products. -/
lemma mul_mem_strictlyDominantAt {w : SplitFinPlace E} {g g' : GL (Fin a) (𝔸f E)}
    (hg : g ∈ strictlyDominantAt w) (hg' : g' ∈ strictlyDominantAt w) :
    g * g' ∈ strictlyDominantAt w := by
  obtain ⟨s, hs, k, l, hg⟩ := hg
  obtain ⟨s', hs', k', l', hg'⟩ := hg'
  refine ⟨s * s', by simpa [Pi.mul_def] using hs.mul hs', ?_⟩
  simpa only [map_mul, hg, hg'] using dominant_doubleCoset_mul hs.monotone hs'.monotone k l k' l'

/-- Let `f` be a Hecke element of level `𝔑` that is a combination of basis elements [g] with
`dualComponent w g` in some `I s I`, for `I = proIwahori` and `s` diagonal strictly dominant.
Suppose `𝔑 ∉ w̄` and the pullback of `levelGU` under `conjAtSplit w` lies in `I`. Then `f` is
regular: for `y ∈ GL_a(E)` and adelic `x`, if f(x⁻¹y⁻¹x) ≠ 0 then the characteristic polynomial of
`y` is separable. -/
lemma isRegularHecke_of_strictlyDominantAt {w : SplitFinPlace E} (hw : 𝔑 ∉ (star w.val).asIdeal)
    (h_lev : (levelGU (Fin a) 𝔑).comap (conjAtSplit w) ≤ proIwahori) {f : heckeAlgebra (Fin a) ℂ 𝔑}
    (hf : f.val ∈ spanOn ℂ (strictlyDominantAt w)) :
    IsRegularHecke f := by
  intro y x hy
  obtain ⟨g, ⟨s, hs, k, l, hg⟩, h_coset⟩ := spanOn.exists_mem_of_cosetFn_ne_zero hf hy
  -- `x⁻¹ y⁻¹ x` differs from `g` by an element of the level, so at `w` it lies in the same double
  -- coset of `proIwahori` as `s`.
  obtain ⟨h_loc, -⟩ := conjAtSplit_dualComponent hw (QuotientGroup.eq.mp h_coset)
  -- As `s` is strictly dominant, such a point is conjugate to a diagonal `s d` with `d` in
  -- `proIwahori`.
  have h_double : k.val * diagGL s * (l.val * dualComponent w (g⁻¹ * (x⁻¹ * toFinGL y⁻¹ * x))) ∈
      iwahoriDoubleCoset s :=
    mul_mem_mul (mul_mem_mul k.prop rfl) (mul_mem l.prop (h_lev h_loc))
  have h_map_one (c : GL (Fin a) (LocField w.val)) :
      GeneralLinearGroup.map (1 : LocField w.val →+* LocField w.val) c = c := rfl
  obtain ⟨c, -, d, hd, h_conj⟩ := exists_inv_mul_mul_map_eq_diagGL_mul hs 1 (by simp) continuous_id
    (fun g ↦ ⟨g, h_map_one g⟩) h_double
  have h_diag :
      (dualComponent w x * c)⁻¹ * dualComponent w (toFinGL y⁻¹) * (dualComponent w x * c) =
        diagGL (s * d) := by
    simpa [← mul_assoc, ← hg, h_map_one] using h_conj
  -- `dualComponent w (toFinGL y⁻¹)` is by definition the transpose of `y` over `LocField w`.
  have h_charpoly : y.val.charpoly.map (algebraMap E (LocField w.val)) =
      ∏ i : Fin a, (X - C ((s * d) i).val) := by
    rw [← charpoly_map, ← charpoly_transpose,
      show (y.val.map (algebraMap E (LocField w.val)))ᵀ = (dualComponent w (toFinGL y⁻¹)).val
        from rfl,
      ← charpoly_units_conj' (dualComponent w x * c), ← charpoly_diagonal]
    congr 1
    simpa [Matrix.mul_inv_rev] using congrArg Units.val h_diag
  rw [← separable_map (algebraMap E (LocField w.val)), h_charpoly, separable_prod_X_sub_C_iff]
  have h_val_eq : (v ∘ fun i ↦ ((s * d) i).val) = fun i ↦ v (s i).val :=
    funext fun i ↦ by simpa using v_diag_eq_one_of_mem_proIwahori hd i
  exact .of_comp (f := v) (by simpa only [h_val_eq] using hs.injective)

/-- The positive powers of a Hecke element whose terms are strictly dominant at `w` are regular, if
the level at `w` lies in `proIwahori` and `𝔑` does not lie in the conjugate of `w`. -/
lemma isRegularHecke_pow_succ_of_strictlyDominantAt {w : SplitFinPlace E}
    (hw : 𝔑 ∉ (star w.val).asIdeal)
    (h_lev : (levelGU (Fin a) 𝔑).comap (conjAtSplit w) ≤ proIwahori) {f : heckeAlgebra (Fin a) ℂ 𝔑}
    (hf : f.val ∈ spanOn ℂ (strictlyDominantAt w)) (m : ℕ) :
    IsRegularHecke (f ^ (m + 1)) := by
  refine isRegularHecke_of_strictlyDominantAt hw h_lev ?_
  rw [SubmonoidClass.coe_pow]
  induction m with
  | zero => rwa [zero_add, pow_one]
  | succ m ih => exact spanOn.mul ih hf fun _ hg _ hg' ↦ mul_mem_strictlyDominantAt hg hg'

/-- Let the level at `w` lie in `proIwahori` and let `𝔑` not lie in the conjugate of `w`. Then some
Hecke element `b` sends vectors of level `𝔑` to vectors fixed by `proIwahori`, kills no nonzero
vector fixed by `proIwahori`, and commutes with every `c` whose terms are similitudes trivial at
`w`; the terms of `b * c` are strictly dominant at `w`. -/
lemma exists_iwahori_hecke_element (π : Representation ℂ (GL (Fin a) (𝔸f E)) W)
    {w : SplitFinPlace E} (hw : 𝔑 ∉ (star w.val).asIdeal)
    (h_lev : (levelGU (Fin a) 𝔑).comap (conjAtSplit w) ≤ proIwahori) :
    ∃ b : heckeAlgebra (Fin a) ℂ 𝔑,
      b.val ∈ fixedToEigen (levelGU (Fin a) 𝔑) (conjAtSplit w) proIwahori 1 ∧
      (∀ x ∈ levelSpace (π.comp (conjAtSplit w)) proIwahori, x ≠ 0 → π.asAlgebraHom b x ≠ 0) ∧
      ∀ c ∈ spanOn ℂ (GU E (Fin a) ⊓ (dualComponent w).ker).carrier,
        Commute c b.val ∧ b.val * c ∈ spanOn ℂ (strictlyDominantAt w) := by
  -- On `proIwahori`-fixed vectors `b` is a central translate of an injective operator `U_t`.
  -- `ρ` is the local group at `w` on the smooth vectors of `π`; `t` is strictly dominant (`ht`).
  let ρ : Rep ℂ (GL (Fin a) (LocField w.val)) := Rep.of (smoothVectorRep (π.comp (conjAtSplit w)))
  obtain ⟨t, ht, hU_inj⟩ := exists_iwahoriHeckeHom_injective ρ (v_uniformizer _)
  -- A central `z = N⁻¹` makes the inverse of `z t` integral.
  obtain ⟨N, hN, h_int⟩ := exists_forall_mul_mem_Ô (conjAtSplit w (diagGL t)).inv.uncurry
  let z : GL (Fin a) (𝔸f E) :=
    (GeneralLinearGroup.scalar _ (principalIdele (.mk0 N (mod_cast hN))))⁻¹
  have z_central (g : GL (Fin a) (𝔸f E)) : Commute g z := (commute_scalar_GL _ g).inv_right
  -- `z` is a similitude, since its inverse, the scalar `N`, scales the standard form by `N * N`
  have hz : z ∈ GU E (Fin a) := by
    refine ⟨N * N, by simpa, 1, gram_inv_of_gram_eq ?_⟩
    simp [smul_one_eq_diagonal, ← Matrix.diagonal_natCast, Matrix.diagonal_mul_diagonal]
  have h_int_ij (i j : Fin a) : (N : 𝔸f E) * (conjAtSplit w (diagGL t))⁻¹ i j ∈ Ô E := h_int (i, j)
  have hzt : z * conjAtSplit w (diagGL t) ∈ GUPlus E (Fin a) :=
    ⟨mul_mem hz (by simp), fun i j ↦ by simpa [z, ← nsmul_eq_mul'] using h_int_ij i j⟩
  obtain ⟨b, hb_supp, hb_type, hb⟩ := exists_local_hecke_element π (J := proIwahori)
    (sep_subset _ _) 1 (fun _ hg ↦ ⟨h_lev hg, rfl⟩) hw (diagGL t) z_central hzt
  refine ⟨b, hb_type, fun x hx hx_ne h_zero ↦ ?_, fun c hc ↦ ⟨?_, ?_⟩⟩
  · have hx_fix (g : GL (Fin a) (LocField w.val)) (hg : g ∈ proIwahori) :
        π (conjAtSplit w g) x = x := by simpa using hx ⟨g, hg⟩
    let x' : levelSpace ρ.ρ proIwahori :=
      ⟨⟨x, Filter.mem_of_superset
        ((isOpen_proIwahori (n := Fin a) (F := LocField w.val)).mem_nhds (one_mem _)) hx_fix⟩,
        fun k ↦ Subtype.ext (hx k)⟩
    -- Extend the `proIwahori`-average to a linear map `T` on `W`; then `T z⁻¹ b x = U_t x ≠ 0`.
    obtain ⟨T, hT⟩ := (Submodule.subtype _ ∘ₗ compactMean ρ.ρ proIwahori).exists_extend
    -- `ρ` acts on the smooth vectors of `π` through `conjAtSplit w`, and `U_t` is the mean
    -- over `proIwahori` of the action of `t`.
    have h_smooth (g : GL (Fin a) (LocField w.val)) (y : ρ) :
        ((ρ.ρ g y : ρ) : W) = π (conjAtSplit w g) y := rfl
    have hU_def : (iwahoriHeckeHom ρ ⟨t, ht.monotone⟩ x' : ρ) =
        compactMean ρ.ρ proIwahori (ρ.ρ (diagGL t) (x' : ρ)) := rfl
    have h_eq : (T * π z⁻¹) (π.asAlgebraHom b x) =
        ((iwahoriHeckeHom ρ ⟨t, ht.monotone⟩ x' : ρ) : W) :=
      hb T _ fun j ↦ by
        simpa [x', h_smooth, hU_def] using LinearMap.congr_fun hT (ρ.ρ (j * diagGL t) x')
    have hU : iwahoriHeckeHom ρ ⟨t, ht.monotone⟩ x' = 0 :=
      Subtype.ext (Subtype.ext (by simpa [h_zero] using h_eq.symm))
    have hx'_zero : x' = 0 := (injective_iff_map_eq_zero _).mp hU_inj x' hU
    -- `x` is the vector underlying `x'`
    exact hx_ne (congrArg (fun u : levelSpace ρ.ρ proIwahori ↦ ((u : ρ) : W)) hx'_zero)
  · refine Commute.span_left (forall_mem_image.mpr fun g hg ↦ .span_right ?_ _ hb_supp) _ hc
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have h_comm : Commute g (conjAtSplit w j * (z * conjAtSplit w (diagGL t))) := by
      simp [commute_conjAtSplit hg, z_central]
    exact h_comm.map _
  · refine spanOn.mul hb_supp hc (forall_mem_range.mpr fun j g hg ↦ ?_)
    have hg_one : dualComponent w g = 1 := MonoidHom.mem_ker.mp hg.2
    -- `dualComponent w (j z t g)` is `j · N t`, since `dualComponent` inverts the scalar `z`; `N t`
    -- is strictly dominant like `t`
    refine ⟨fun i ↦ .mk0 N (mod_cast hN) * t i,
      by simpa [StrictMono, pos_iff_ne_zero, hN], j, 1, ?_⟩
    rw [map_mul, map_mul, map_mul, dualComponent_conjAtSplit, dualComponent_conjAtSplit, hg_one]
    simp [z, dualComponent, invTransposeGL, Equiv.symm, Units.ext_iff, Matrix.map_natCast,
      map_zero]

/-- An element of the Hecke algebra of level `𝔑` sends vectors of level `𝔑` to vectors of level
`𝔑`. -/
private lemma asAlgebraHom_mem_levelSpace_of_mem_levelSpace
    {π : Representation ℂ (GL (Fin a) (𝔸f E)) W} (f : heckeAlgebra (Fin a) ℂ 𝔑) {x : W}
    (hx : x ∈ levelSpace π (levelGU (Fin a) 𝔑)) :
    π.asAlgebraHom f.val x ∈ levelSpace π (levelGU (Fin a) 𝔑) :=
  f.property.2 hx

/-- The test function. Let `π` be a representation of `GL_a(𝔸f E)` on `W`, and let `φ` be a test
vector of level `𝔑` (nonzero, of cuspidal type `(J, χ)` at `w₀` and spherical at `w₁`). Suppose `φ`
is fixed by a Hecke element `c` supported on unitary similitudes whose component at `w₁` is `1`.
Then there is a Hecke element `b` such that no power of `b * c` kills `φ`, and every positive power
is regular (nonzero at `x⁻¹y⁻¹x`, `y ∈ GL_a(E)`, only if `y` has separable characteristic
polynomial). Every positive power also sends vectors of level `𝔑` to vectors on which `J`, through
`conjAtSplit w₀`, acts by `χ`. -/
theorem exists_test_function {w₀ w₁ : SplitFinPlace E}
    {J : Subgroup (GL (Fin a) (LocField w₀.val))} {χ : J →* ℂ}
    {π : Representation ℂ (GL (Fin a) (𝔸f E)) W} {φ : W}
    (hφ_lev : φ ∈ levelSpace π (levelGU (Fin a) 𝔑)) (hφ_test : IsTestVector 𝔑 π φ w₀ w₁ χ)
    {c : heckeAlgebra (Fin a) ℂ 𝔑}
    (hc : c.val ∈ spanOn ℂ (GU E (Fin a) ⊓ (dualComponent w₁).ker).carrier)
    (hcφ : π.asAlgebraHom c φ = φ) :
    ∃ b : heckeAlgebra (Fin a) ℂ 𝔑, ∀ m : ℕ,
      π.asAlgebraHom ((b * c) ^ m).val φ ≠ 0 ∧
      IsRegularHecke ((b * c) ^ (m + 1)) ∧
      ((b * c) ^ (m + 1)).val ∈ fixedToEigen (levelGU (Fin a) 𝔑) (conjAtSplit w₀) J χ := by
  -- Take `b = b₁ b₀`, where `b₀` averages against `χ` over `J` at `w₀` and `b₁` is the element
  -- of `exists_iwahori_hecke_element` at `w₁`.
  -- `χ` is trivial on the level, because the level fixes `φ ≠ 0`.
  have hχ (g : GL (Fin a) (LocField w₀.val)) (hg : conjAtSplit w₀ g ∈ levelGU (Fin a) 𝔑) :
      ∃ h : g ∈ J, χ ⟨g, h⟩ = 1 := by
    refine ⟨hφ_test.level_le hg, smul_left_injective ℂ hφ_test.ne_zero ?_⟩
    -- both `χ ⟨g, _⟩ • φ` and `1 • φ` are the image of `φ` under `conjAtSplit w₀ g`
    exact (mem_levelSpace.mp hφ_test.isEigenvector ⟨g, _⟩).symm.trans
      (mem_levelSpace.mp hφ_lev ⟨_, hg⟩)
  obtain ⟨b₀, hb₀_supp, hb₀_type, hb₀⟩ := exists_local_hecke_element π hφ_test.le_localIntGL χ hχ
    hφ_test.notMem_star_fst 1 Commute.one_right (by simp)
  obtain ⟨b₁, hb₁_type, hb₁_ne, hb₁⟩ :=
    exists_iwahori_hecke_element π hφ_test.notMem_star_snd hφ_test.level_le_proIwahori
  -- `w₁` is neither `w₀` nor its conjugate, so the terms of `b₀ c` are trivial at `w₁`.
  have hw_star : star w₁.val ≠ w₀.val := fun h_eq ↦
    hφ_test.notMem_star_fst (by simpa [← h_eq] using hφ_test.mem_snd)
  have h_term_mem (j : J) :
      conjAtSplit w₀ j * (1 * conjAtSplit w₀ 1) ∈ GU E (Fin a) ⊓ (dualComponent w₁).ker := by
    simp [dualComponent, evalAt_conjAtSplit_of_ne _ hφ_test.place_ne.symm hw_star]
  have hb₀c : b₀.val * c.val ∈ spanOn ℂ (GU E (Fin a) ⊓ (dualComponent w₁).ker).carrier :=
    spanOn.mul hb₀_supp hc (forall_mem_range.mpr fun j g hg ↦ Subgroup.mul_mem _ (h_term_mem j) hg)
  obtain ⟨h_comm_val, h_supp⟩ := hb₁ _ hb₀c
  have h_comm : Commute (b₀ * c) b₁ := Subtype.ext h_comm_val
  have hb₀φ : π.asAlgebraHom b₀ φ = φ := by
    simpa using hb₀ 1 φ (by simpa using hφ_test.isEigenvector)
  -- By induction every power of `b₁ b₀ c` sends `φ` to a nonzero `proIwahori`-fixed vector.
  have h_vec (m : ℕ) :
      π.asAlgebraHom ((b₁ * (b₀ * c)) ^ m).val φ ∈
          levelSpace (π.comp (conjAtSplit w₁)) proIwahori ∧
        π.asAlgebraHom ((b₁ * (b₀ * c)) ^ m).val φ ≠ 0 := by
    induction m with
    | zero => simpa [hφ_test.ne_zero] using fun g hg ↦ hφ_test.fixed ⟨g, hg.1⟩
    | succ m ih =>
      -- `b₀ c` commutes past the power and fixes `φ`.
      have h_succ : π.asAlgebraHom ((b₁ * (b₀ * c)) ^ (m + 1)).val φ =
          π.asAlgebraHom b₁ (π.asAlgebraHom ((b₁ * (b₀ * c)) ^ m).val φ) := by
        simp [pow_succ', ((h_comm.mul_right rfl).pow_right m).right_comm, hcφ, hb₀φ]
      rw [h_succ]
      exact ⟨hb₁_type (asAlgebraHom_mem_levelSpace_of_mem_levelSpace _ hφ_lev), hb₁_ne _ ih.1 ih.2⟩
  refine ⟨b₁ * b₀, fun m ↦ ?_⟩
  rw [mul_assoc]
  refine ⟨(h_vec m).right, isRegularHecke_pow_succ_of_strictlyDominantAt hφ_test.notMem_star_snd
    hφ_test.level_le_proIwahori h_supp m, ?_⟩
  -- The power begins with `b₀`, which produces `χ`-eigenvectors.
  intro V _ _ ρ x hx
  have h_begin : (b₁ * (b₀ * c)) ^ (m + 1) = b₀ * (c * (b₁ * (b₁ * (b₀ * c)) ^ m)) := by
    rw [pow_succ', ← h_comm, mul_assoc, mul_assoc]
  rw [h_begin, MulMemClass.coe_mul, map_mul]
  exact hb₀_type (asAlgebraHom_mem_levelSpace_of_mem_levelSpace _ hx)

end New.Variety
end
end

/-!
# Coefficient systems from weights and the degrees where Hecke eigensystems occur

A weight `κ` gives a coefficient system on `GL_a(E)`. Its Hecke eigensystems occur in the degrees
given by the jumps of `κ`, in the sense of `New.Variety.OccursInWeight`: the local terms of the
Lefschetz side do not all cancel.

`Φ v` is the embedding that the CM type chooses at `v`, and `v₀` is the base infinite place fixed by
`New.CMBase E`.

* `New.Variety.occursInWeight_of_isTestEigenform`: the Hecke eigenvalues of a test eigenform occur,
  if the character of the coefficients is given by a Schur polynomial and powers of the determinant.
* `New.Variety.exists_isCoefficientSystem`: the coefficient system attached to a weight, and the
  occurrence of the eigensystems of its test vectors.

Notions from other files:
* `New.Weight`: For `κ : Weight E` and an infinite place `v` of `E`, `κ.1 v h` is the number of
  columns of height `h` of a Young diagram, and `κ.2 v` is an integer exponent of the determinant.
* `New.Variety.entryConj`: The endomorphism of the unitary group {g : gᴴg = 1} of matrices over R
  indexed by `n` that applies the involution of R to each entry.
* `New.jumps`: The multiset {j − 1 − λ_j} if σ is in the CM type, else {λ_j + a − j}, 1 ≤ j ≤ a,
  with λ the highest weight of κ at σ.
* `New.Space.weightRep`: The representation of the rational unitary group on coordinate vectors of
  weight `(κ.1, κ.2)`, through its components at the infinite places and `New.conjWeylRep`.

## Relation to the literature

Known result: Transfer of eigensystems between unitary inner forms differing at a real place. Only
the occurrence is proved here, namely that the Hecke eigensystem of a definite form occurs, in each
Hodge weight, on the variety for signature (1, n-1), with n odd and a cuspidal type at one split
place. It is proved by comparing two finite counts, without stabilisation. Source: Harris and
Labesse, Conditional base change for unitary groups, Asian J. Math. 8 (2004), Thm 2.1.2; Labesse,
Changement de base CM et séries discrètes (2011), Thm 5.4; count as in Goresky and MacPherson, The
topological trace formula (2003), and Shimura, On the trace formula for Hecke operators, Acta Math.
132 (1974).
-/

@[expose] public section

open NumberField Matrix Polynomial Fintype Finset IsAlgClosed LinearMap Submodule New.QuadField Fin

/-- For `a` odd, `rootCoeffEval` sends the variable `X 0` to minus the product of the `a` roots. -/
lemma New.Variety.rootCoeffEval_X_zero_of_odd {a : ℕ} [NeZero a] (ha : Odd a) {R : Type}
    [CommRing R] (r : Fin a → R) :
    rootCoeffEval (a := a) (univ.val.map r) (MvPolynomial.X 0) = -univ.prod r := by
  simp [rootCoeffEval, coeff_zero_eq_eval_zero, eval_prod, prod_neg, ha.neg_one_pow, -univ_val_map]

/-- Let `E` be a CM field containing ℚ(i√d₀), and let `w₁` be a finite place of `E` that is split
over the maximal real subfield and divides the level `𝔑`. Any product of the Hecke elements
`τ_{w,j}` (`tauHecke`, in the Hecke algebra of level `K(𝔑)`) at places `w` safe for `𝔑` (among other
things, `𝔑 ∉ w` and `𝔑` lies in no place over the conjugate of the place below `w`) lies in the span
of the group elements `[g]` with `g` a unitary similitude (`gᴴ g` a scalar finite idele of ℚ) whose
component at `w₁` is trivial. Here the component is taken via `dualComponent w₁`, the inverse
transpose of the `w₁`-component in `GL_a(E_{w₁})`. -/
lemma New.Variety.prod_map_tauHecke_mem_spanOn {E : Type} [Field E] [NumberField E] [IsCMField E]
    {a d₀ : ℕ} [HasQuadSubfield d₀ E] {𝔑 : 𝓞 E} {w₁ : SplitFinPlace E} (hw₁ : 𝔑 ∈ w₁.val.asIdeal)
    (L : List (SafePlace 𝔑 × ℕ)) :
    (L.map tauHecke).prod.val ∈ spanOn ℂ (GU E (Fin a) ⊓ (dualComponent w₁).ker).carrier := by
  induction L with
  | nil => exact subset_span ⟨1, Subgroup.one_mem _, by simp [MonoidAlgebra.one_def]⟩
  | cons s L ih =>
    obtain ⟨⟨v, -, h_notMem, h_notMem_conj⟩, j⟩ := s
    refine spanOn.mul heckeSum_mem_spanOn ih ?_
    rintro _ ⟨U, rfl⟩ g
    refine Subgroup.mul_mem _ ⟨(invHeckeIsogeny_mem_GUPlus _ U).1, ?_⟩
    -- Both factors of `invHeckeIsogeny` are trivial at `w₁` since `w₁ ∣ 𝔑` and `v` is safe.
    have h_below_ne : (w₁ : FinPlace E).below (QuadField d₀) ≠
        star ((v : FinPlace E).below (QuadField d₀)) := fun h ↦ h_notMem_conj _ h hw₁
    suffices (invHeckeIsogeny (v : SplitFinPlace E) U).map (evalAt (w₁ : FinPlace E)) = 1 by
      simp [dualComponent, this]
    rw [invHeckeIsogeny, map_mul,
      evalAt_conjAtSplit_of_ne (hu := fun h ↦ h_notMem (by rwa [← h]))
        (hu' := fun h ↦ h_below_ne (by rw [← h, below_star, star_star])),
      mul_one, uniformizerNorm, ← map_pow, ← map_inv, ← map_pow, ← map_inv]
    exact evalAt_centralScalar_of_ne h_below_ne _

/-- A word `L` in the Hecke operators `tauHecke` at safe places acts on a common eigenvector `φ`
of the operators `heckeSum`, with eigenvalues `θ`, by the product of the eigenvalues of its
letters. -/
lemma New.Variety.asAlgebraHom_prod_map_tauHecke_apply {E : Type} [Field E] [NumberField E]
    [IsCMField E] {a d₀ : ℕ} [HasQuadSubfield d₀ E] {W : Type} [AddCommGroup W] [Module ℂ W]
    {𝔑 : 𝓞 E} {π : Representation ℂ (GL (Fin a) (𝔸f E)) W} {φ : W} {θ : SafePlace 𝔑 → ℕ → ℂ}
    (h_eig : ∀ (w : SafePlace 𝔑) (j : ℕ), π.asAlgebraHom (heckeSum (Fin a) ℂ w.val j) φ = θ w j • φ)
    (L : List (SafePlace 𝔑 × ℕ)) :
    π.asAlgebraHom (L.map tauHecke).prod.val φ = (L.map ↿θ).prod • φ := by
  induction L with
  | nil => simp
  | cons s L ih =>
    have h_head : π.asAlgebraHom (tauHecke s).val φ = ↿θ s • φ := h_eig s.1 s.2
    simp [ih, h_head, smul_smul, mul_comm, -SubmonoidClass.coe_list_prod]

/-- The local terms of a regular element `y`, summed over the marked eigenvalue. Let `q` be the
Schur polynomial of `l` at `Φ v₀`, and `(-X 0) ^ m` (for `a` odd, the `m`-th power of the product of
the roots) at the conjugate of `Φ v₀` and at the `Φ v` with `v ≠ v₀`. Let `μ k` be the numbered
roots of `y` at `Φ v₀`. The `k`-th term is the `k`-th Lagrange basis polynomial of the `μ` at
`μ k * X`, times the product over `σ` of `q σ` at `lieRoots`. These are the roots `r` of `σ y`,
taken as `r X` if the eigenline of `r` lies in the Lie algebra and as `r` otherwise: at `Φ v₀` only
the marked root, at its conjugate all but one, at the other `Φ v` all, at their conjugates none.
Then the sum is the product over `σ` of the values of `q σ` at the eigenvalues of `σ y`, times
`∑ k, X ^ l k` shifted by a fixed power of `X`. -/
lemma New.Variety.sum_basis_comp_mul_prod_rootCoeffEval_eq {E : Type} [Field E] [CMBase E] {a : ℕ}
    [NeZero a] (ha : Odd a) {q : (E →+* ℂ) → MvPolynomial (Fin a) ℤ} {l : Fin a → ℕ} {m : ℕ}
    (hq : q (Φ v₀) = genericSchur l) (hq_conj : q (star (Φ v₀)) = (-MvPolynomial.X 0) ^ m)
    (hq_other : ∀ v : InfinitePlace E, v ≠ v₀ → q (Φ v) = (-MvPolynomial.X 0) ^ m)
    {y : GL (Fin a) E} (hy : y.val.charpoly.Separable) :
    ∑ k : Fin a,
        (Lagrange.basis univ (numberedRoots (Φ v₀) y.val.charpoly) k).comp
            (X * C (numberedRoots (Φ v₀) y.val.charpoly k)) *
          ∏ σ : E →+* ℂ, rootCoeffEval
            (lieRoots y.val.charpoly (numberedRoots (Φ v₀) y.val.charpoly k) σ) (q σ) =
      C (∏ σ : E →+* ℂ, rootCoeffEval (y.val.charpoly.map σ).roots (q σ)) *
        ∑ k : Fin a, X ^ (m * (a - 1 + a * (Core.numInfPlaces E - 1)) + l k) := by
  -- Evaluate the factor at each embedding. Only the one at `Φ v₀` depends on the marked root `r k`,
  -- and there the sum over `k` is `sum_lagrange_smul_rootCoeffEval`; the others are constants
  -- times powers of `X`.
  set P : E[X] := y.val.charpoly
  set r : Fin a ↪ ℂ := numberedRoots (Φ v₀) P
  let s (σ : E →+* ℂ) : ℂ := rootCoeffEval (P.map σ).roots (q σ)
  have h_roots (σ : E →+* ℂ) : (P.map σ).roots = univ.val.map (numberedRoots σ P : Fin a ↪ ℂ) :=
    roots_eq_map_numberedRoots hy σ
  -- At `Φ v₀` only the marked root is multiplied by `X`.
  have h_marked (k : Fin a) : lieRoots P (r k) (Φ v₀) =
      univ.val.map fun k' : Fin a ↦ (if k' = k then X else 1) * C (r k') := by
    simp [lieRoots, IsLieRoot, h_roots, r, -ite_mul, -univ_val_map]
  -- At its conjugate `a - 1` roots are multiplied by `X`.
  have h_conj (k : Fin a) : rootCoeffEval (lieRoots P (r k) (star (Φ v₀))) (q (star (Φ v₀))) =
      X ^ (m * (a - 1)) * C (s (star (Φ v₀))) := by
    simp only [s, lieRoots, hq_conj, roots_map_conjugate]
    -- `ite_mul` is left out so that the factors `if … then X else 1` stay whole for `prod_ite`
    simp [IsLieRoot, h_roots, rootCoeffEval_X_zero_of_odd ha, -ite_mul,
      (RingHom.injective _).eq_iff,
      prod_ite, filter_ne', mul_pow, r, ← pow_mul', prod_mul_distrib, -univ_val_map]
  -- At another place `v` all `a` roots at `Φ v` are multiplied by `X`, and none at its conjugate.
  have h_other (k : Fin a) (v : {v // v ≠ v₀}) :
      rootCoeffEval (lieRoots P (r k) (Φ v.val)) (q (Φ v.val)) = X ^ (m * a) * C (s (Φ v.val)) := by
    simp [s, hq_other v v.prop, lieRoots, IsLieRoot, v.prop, h_roots,
      rootCoeffEval_X_zero_of_odd ha,
      mul_pow, prod_mul_distrib, -univ_val_map]
    -- what is left is `A ^ m * (X ^ a) ^ m = X ^ (m * a) * A ^ m`
    ring
  have h_other_conj (k : Fin a) (v : {v // v ≠ v₀}) :
      rootCoeffEval (lieRoots P (r k) (star (Φ v.val))) (q (star (Φ v.val))) =
        C (s (star (Φ v.val))) := by
    simp [s, lieRoots, IsLieRoot, v.prop, ← rootCoeffEval_map]
  have h_sum_marked : ∑ k : Fin a, (Lagrange.basis univ r k).comp (X * C (r k)) *
      rootCoeffEval (lieRoots P (r k) (Φ v₀)) (q (Φ v₀)) = C (s (Φ v₀)) * ∑ k : Fin a, X ^ l k := by
    simpa only [h_marked, s, h_roots, hq, smul_eq_mul, comp_eq_aeval] using
      sum_lagrange_smul_rootCoeffEval l r
  -- The factors at the embeddings other than `Φ v₀` do not depend on `k`: they give `X ^ N * C c`.
  set N : ℕ := m * (a - 1 + a * (Core.numInfPlaces E - 1)) with hN
  set c : ℂ := s (star (Φ v₀)) * ∏ v : {v // v ≠ v₀}, s (Φ v.val) * s (star (Φ v.val)) with hc
  have h_prod (k : Fin a) : ∏ σ : E →+* ℂ, rootCoeffEval (lieRoots P (r k) σ) (q σ) =
      X ^ N * C c * rootCoeffEval (lieRoots P (r k) (Φ v₀)) (q (Φ v₀)) := by
    simp [hN, hc, prod_embeddings_eq_prod_pairs, prod_eq_mul_prod_subtype_ne _ v₀, h_conj, h_other,
      h_other_conj, prod_mul_distrib]
    ring
  have h_const : ∏ σ : E →+* ℂ, s σ = s (Φ v₀) * c := by
    rw [hc, prod_embeddings_eq_prod_pairs, prod_eq_mul_prod_subtype_ne _ v₀, mul_assoc]
  calc _ = X ^ N * C c * ∑ k : Fin a, (Lagrange.basis univ r k).comp (X * C (r k)) *
        rootCoeffEval (lieRoots P (r k) (Φ v₀)) (q (Φ v₀)) := by
        simp only [h_prod, mul_sum, mul_left_comm]
    _ = C (∏ σ : E →+* ℂ, s σ) * ∑ k : Fin a, X ^ (N + l k) := by
        simp only [h_sum_marked, h_const, pow_add, ← mul_sum, map_mul]
        ring

/-- Comparison of trace formulas, for `a` odd and `𝔑` neat. Let the trace of `ξ y⁻¹` at regular `y`
be the product of the values of `q σ` at the eigenvalues of `σ y` (`q` as in
`sum_basis_comp_mul_prod_rootCoeffEval_eq`), and let `f` be regular of cuspidal type `χ` at `w₀`. If
`f` is null (`New.Variety.IsNullHecke`) in the weight `l j + m (a - 1 + a (n - 1))`, `n` the number
of infinite places of `E`, then `f` has trace zero on the definite forms with coefficients in
`ξ`. -/
lemma New.Variety.trace_definiteForms_rep_eq_zero_of_isNullHecke {E : Type} [Field E] [CMBase E]
    {a : ℕ} [NeZero a] (ha : Odd a) {W : Type} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    {ξ : Representation ℂ (GL (Fin a) E) W} {q : (E →+* ℂ) → MvPolynomial (Fin a) ℤ}
    {l : Fin a → ℕ} {m : ℕ}
    (h_char : ∀ y : GL (Fin a) E, y.val.charpoly.Separable →
      (ξ y⁻¹).trace ℂ W = ∏ σ : E →+* ℂ, rootCoeffEval (y.val.charpoly.map σ).roots (q σ))
    (hq : q (Φ v₀) = genericSchur l) (hq_conj : q (star (Φ v₀)) = (-MvPolynomial.X 0) ^ m)
    (hq_other : ∀ v : InfinitePlace E, v ≠ v₀ → q (Φ v) = (-MvPolynomial.X 0) ^ m)
    {𝔑 : 𝓞 E} (hN : IsNeat (Fin a) 𝔑)
    {f : heckeAlgebra (Fin a) ℂ 𝔑} (h_reg : IsRegularHecke f) {w₀ : SplitFinPlace E}
    {J : Subgroup (GL (Fin a) (LocField w₀.val))} {χ : J →* ℂ} (hχ : IsCuspidalType J χ)
    (h_type : f.val ∈ fixedToEigen (levelGU (Fin a) 𝔑) (conjAtSplit w₀) J χ) {j : Fin a}
    (h_null : IsNullHecke (∑ σ : E →+* ℂ, (q σ).totalDegree + 1)
      (m * (a - 1 + a * (Core.numInfPlaces E - 1)) + l j) f) :
    (definiteForms.rep 𝔑 ξ f).trace ℂ (definiteForms 𝔑 ξ) = 0 := by
  classical
  -- The definite trace formula writes the trace as an orbit sum weighted by the `X ^ d`
  -- coefficients of the local terms, divided by `mult`. By `finsum_countTerm_marked_eq_definite`
  -- this equals the marked orbit sum, which `h_null` kills.
  set d : ℕ := m * (a - 1 + a * (Core.numInfPlaces E - 1)) + l j
  have h_fin : (countTerm True f 1).support.Finite := (h_null h_reg 1).left
  have h_sum (α : Fin (∑ σ, (q σ).totalDegree + 1) → 𝓞 E) :
      ∑ᶠ c, countTerm True f (fun P μ ↦ (localTerm (2 * α) P μ).coeff d) c = 0 :=
    (h_null h_reg α).right
  -- `X ^ d` occurs `mult` times in the sum of powers of `X` in
  -- `sum_basis_comp_mul_prod_rootCoeffEval_eq`.
  let mult : ℕ := #{k | l j = l k}
  have h_mult : (mult : ℂ) ≠ 0 := by simp [mult]
  let lagrange (P : E[X]) (k : Fin a) : ℂ[X] :=
    (Lagrange.basis univ (numberedRoots (Φ v₀) P) k).comp (X * C (numberedRoots (Φ v₀) P k))
  let w (P : E[X]) (k : Fin a) : ℂ :=
    (lagrange P k * ∏ σ, rootCoeffEval (lieRoots P (numberedRoots (Φ v₀) P k) σ) (q σ)).coeff d /
      mult
  have h_weight (y : GL (Fin a) E) (hy : y.val.charpoly.Separable) :
      (ξ y⁻¹).trace ℂ W = ∑ k, w y.val.charpoly k := by
    rw [← sum_div, ← finsetSum_coeff, sum_basis_comp_mul_prod_rootCoeffEval_eq ha hq hq_conj
      hq_other hy, ← h_char y hy,
      eq_div_iff h_mult]
    simp [d, mult]
  have h_both : ∀ ε : Prop, (countTerm ε f 1).support.Finite :=
    Prop.forall.mpr ⟨finite_support_countTerm_definite hN f 1, h_fin⟩
  have h_trace : (definiteForms.rep 𝔑 ξ f).trace ℂ (definiteForms 𝔑 ξ) =
      ∑ᶠ c, countTerm True f w c := by
    calc _ = ∑ᶠ c, countTerm False f w c :=
          trace_definiteForms_eq_finsum_countTerm ξ hN h_reg h_weight
      _ = _ :=
          (finsum_countTerm_marked_eq_definite hN (by simpa using ha) h_reg hχ h_type w h_both).symm
  rw [h_trace]
  -- Both sums run over the finite set `h_fin.toFinset`, and the constant `mult` cancels.
  simp_rw [finsum_countTerm_eq_sum _ h_fin, ← sum_coe_sort h_fin.toFinset, w, mul_div_assoc',
    ← sum_div, div_eq_zero_iff, h_mult, or_false] at h_sum ⊢
  -- A class `c` has a characteristic polynomial `P c` and a marked root, numbered `μ c`. Now
  -- `h_sum` says that the linear form `L` (multiply by the Lagrange factor, take the `X ^ d`
  -- coefficient, sum over classes) kills the products `∏ (1 - σ (2 α) t)`, `t` in `lieRoots`, for
  -- all `α`; by `map_prod_rootCoeffEval_eq_zero` it then kills the products of the `q σ`.
  -- `c.val.out` is a triple (frame, element `y`, marked index), as in `countTerm`
  let P (c : h_fin.toFinset) : E[X] := c.val.out.snd.fst.val.charpoly
  let μ (c : h_fin.toFinset) : Fin a := c.val.out.snd.snd
  let L : (h_fin.toFinset → ℂ[X]) →ₗ[ℂ] ℂ :=
    dotProductBilin ℂ ℂ (fun c : h_fin.toFinset ↦ countTerm True f 1 c) ∘ₗ
      (lcoeff ℂ d).compLeft h_fin.toFinset ∘ₗ mulLeft ℂ fun c ↦ lagrange (P c) (μ c)
  have h_card (c : h_fin.toFinset) (σ : E →+* ℂ) :
      (lieRoots (P c) (numberedRoots (Φ v₀) (P c) (μ c)) σ).card = a := by
    simp [P, lieRoots, card_roots_eq_natDegree]
  have h_degree (σ : E →+* ℂ) :
      (q σ).totalDegree ≤ Fintype.card (Fin (∑ τ, (q τ).totalDegree + 1)) := by
    simp [sum_eq_add_sum_subtype_ne _ σ, add_assoc]
  change L (fun c ↦ ∏ σ, rootCoeffEval
    (lieRoots (P c) (numberedRoots (Φ v₀) (P c) (μ c)) σ) (q σ)) = 0
  exact map_prod_rootCoeffEval_eq_zero h_degree algebraicIndependent_embedding_two_mul h_card L
    h_sum

/-- `φ` is a definite form of level `𝔑` with coefficients in `ξ`, a test vector, and an
eigenvector of the Hecke operators at the safe places with eigenvalues `θ`. -/
structure New.Variety.IsTestEigenform {E : Type} [Field E] [CMBase E] {a d₀ : ℕ}
    [HasQuadSubfield d₀ E] {W : Type} [AddCommGroup W] [Module ℂ W] (𝔑 : 𝓞 E)
    (ξ : Representation ℂ (GL (Fin a) E) W) (φ : GL (Fin a) (𝔸f E) → W)
    (θ : SafePlace 𝔑 → ℕ → ℂ) : Prop where
  /-- `φ` is a form on the definite frames. -/
  mem_definiteForms : φ ∈ definiteForms 𝔑 ξ
  /-- `φ` is a test vector at some split places `w₀`, `w₁`, for some type `(J, χ)` at `w₀`. -/
  exists_isTestVector : ∃ (w₀ w₁ : SplitFinPlace E)
    (J : Subgroup (GL (Fin a) (LocField w₀.val))) (χ : J →* ℂ),
    IsTestVector 𝔑 (rightRegular ℂ (GL (Fin a) (𝔸f E)) W) φ w₀ w₁ χ
  /-- The `j`-th Hecke operator at `w` multiplies `φ` by `θ w j`. -/
  heckeSum_apply (w : SafePlace 𝔑) (j : ℕ) :
    (rightRegular ℂ (GL (Fin a) (𝔸f E)) W).asAlgebraHom (heckeSum (Fin a) ℂ w.val j) φ =
      θ w j • φ

/-- Let `a` be odd and `𝔑` neat. Suppose the trace of `ξ y⁻¹` at regular `y` is the product over `σ`
of the values of `q σ` at the eigenvalues of `σ y`, where `q` is the Schur polynomial of `l` at
`Φ v₀` and `(-X 0) ^ m` at the other `Φ v` and at the conjugate of `Φ v₀`. Let `θ` be the Hecke
eigenvalues at the safe places of a test eigenform of level `𝔑` with coefficients in `ξ`. Then `θ`
occurs (`New.Variety.OccursInWeight`, with parameter `∑ σ, deg (q σ) + 1`) in the weight
`l j + m (a - 1 + a (n - 1))` for every `j`, where `n` is the number of infinite places of `E`:
every combination `p` of `tauHecke` words with `p θ = 1` has a Hecke multiple `b p` that is not null
in that weight. -/
lemma New.Variety.occursInWeight_of_isTestEigenform {E : Type} [Field E] [CMBase E] {a d₀ : ℕ}
    [HasQuadSubfield d₀ E] [NeZero a] (ha : Odd a) {W : Type} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] {ξ : Representation ℂ (GL (Fin a) E) W}
    {q : (E →+* ℂ) → MvPolynomial (Fin a) ℤ} {l : Fin a → ℕ} {m : ℕ}
    (h_char : ∀ y : GL (Fin a) E, y.val.charpoly.Separable →
      (ξ y⁻¹).trace ℂ W = ∏ σ : E →+* ℂ, rootCoeffEval (y.val.charpoly.map σ).roots (q σ))
    (hq : q (Φ v₀) = genericSchur l) (hq_conj : q (star (Φ v₀)) = (-MvPolynomial.X 0) ^ m)
    (hq_other : ∀ v : InfinitePlace E, v ≠ v₀ → q (Φ v) = (-MvPolynomial.X 0) ^ m)
    {𝔑 : 𝓞 E} (hN : IsNeat (Fin a) 𝔑)
    {φ : GL (Fin a) (𝔸f E) → W} {θ : SafePlace 𝔑 → ℕ → ℂ} (h_form : IsTestEigenform 𝔑 ξ φ θ)
    (j : Fin a) :
    OccursInWeight a (∑ σ : E →+* ℂ, (q σ).totalDegree + 1) θ
      (m * (a - 1 + a * (Core.numInfPlaces E - 1)) + l j) := by
  -- Suppose all `b * p` are null in this weight, where the polynomial `p` in the Hecke operators
  -- fixes `φ`. For the test function `b` all positive powers of `b * p` then have trace zero, so
  -- `b * p` acts nilpotently on forms; but none of its powers kills `φ`.
  have hφ : φ ∈ definiteForms 𝔑 ξ := h_form.mem_definiteForms
  obtain ⟨w₀, w₁, J, χ, h_test⟩ := h_form.exists_isTestVector
  -- `p` is the combination `∑ c L • L` of words `L ∈ s` in the Hecke operators, with
  -- `∑ c L * θ(L) = 1` (`hc`); `h_null` says that every `b * p` is null in this weight
  intro s c hc h_null
  set p : heckeAlgebra (Fin a) ℂ 𝔑 := ∑ L ∈ s, c L • (L.map tauHecke).prod with hp
  -- `coe_list_prod` is left out of the two `simp` calls: it would rewrite the coerced products to
  -- `List.map (Subtype.val ∘ tauHecke)`, which the lemmas on words no longer match
  have h_supp : p.val ∈ spanOn ℂ (GU E (Fin a) ⊓ (dualComponent w₁).ker).carrier := by
    simp [hp, prod_map_tauHecke_mem_spanOn h_test.mem_snd, sum_mem, smul_mem,
      -SubmonoidClass.coe_list_prod]
  have h_fix : (rightRegular ℂ (GL (Fin a) (𝔸f E)) W).asAlgebraHom p.val φ = φ := by
    simp [hp, asAlgebraHom_prod_map_tauHecke_apply h_form.heckeSum_apply, hc, smul_smul,
      ← Finset.sum_smul, -SubmonoidClass.coe_list_prod]
  -- No power of `b * p` kills `φ`; the positive ones are regular and of type `χ` at `w₀`.
  obtain ⟨b, hb⟩ : ∃ b : heckeAlgebra (Fin a) ℂ 𝔑, ∀ m : ℕ,
      (rightRegular ℂ (GL (Fin a) (𝔸f E)) W).asAlgebraHom ((b * p) ^ m).val φ ≠ 0 ∧
        IsRegularHecke ((b * p) ^ (m + 1)) ∧
        ((b * p) ^ (m + 1)).val ∈ fixedToEigen (levelGU (Fin a) 𝔑) (conjAtSplit w₀) J χ :=
    exists_test_function (Submodule.mem_inf.mp hφ).right h_test h_supp h_fix
  have h_finite_forms : Module.Finite ℂ (definiteForms 𝔑 ξ) := finite_definiteForms ξ hN
  have h_nilpotent : IsNilpotent (definiteForms.rep 𝔑 ξ (b * p)) := by
    refine LinearMap.isNilpotent_iff_forall_trace_pow_eq_zero.2 fun k hk ↦ ?_
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    obtain ⟨-, h_reg, h_type⟩ := hb k
    rw [← map_pow]
    refine trace_definiteForms_rep_eq_zero_of_isNullHecke ha h_char hq hq_conj hq_other hN h_reg
      h_test.isCuspidalType h_type
      (j := j) ?_
    rw [pow_succ, ← mul_assoc]
    exact h_null _
  obtain ⟨k, hk⟩ := h_nilpotent
  have h_kill : definiteForms.rep 𝔑 ξ ((b * p) ^ k) ⟨φ, hφ⟩ = 0 := by
    rw [map_pow, hk, LinearMap.zero_apply]
  exact (hb k).left (congrArg Subtype.val h_kill)

/-- Inverting nonzero numbers `r i` and reversing their order in a generalized Vandermonde
determinant amounts to replacing the exponents `w j` by `a - 1 - w j.rev`, up to the factor
`(∏ r) ^ (1 - a)`. -/
lemma New.Variety.det_inv_rev_zpow {a : ℕ} {r : Fin a → ℂ} (h_ne : ∀ i : Fin a, r i ≠ 0)
    (w : Fin a → ℤ) :
    (of fun i j : Fin a ↦ (r i.rev)⁻¹ ^ w j).det =
      univ.prod r ^ (1 - a : ℤ) * (of fun i j : Fin a ↦ r i ^ (a - 1 - w j.rev)).det := by
  rw [← det_zpow_add h_ne, ← det_submatrix_equiv_self revPerm
    (of fun i j : Fin a ↦ r i ^ ((1 - a : ℤ) + (a - 1 - w j.rev)))]
  simp [← add_sub_assoc, submatrix]

/-- The bialternant formula with integer exponents: if `l = m + k`, then the Schur polynomial of `l`
at nonzero numbers `r i`, times the Vandermonde determinant, is `(∏ r) ^ m * det (r i ^ k j)`. -/
lemma New.Variety.rootCoeffEval_genericSchur_mul_det_zpow {a : ℕ} {r : Fin a → ℂ}
    (h_ne : ∀ i : Fin a, r i ≠ 0)
    {l : Fin a → ℕ} {m : ℕ} {k : Fin a → ℤ} (hl : ∀ j : Fin a, (l j : ℤ) = m + k j) :
    rootCoeffEval (univ.val.map r) (genericSchur l) * (of fun i j : Fin a ↦ r i ^ (j : ℤ)).det =
      univ.prod r ^ m * (of fun i j : Fin a ↦ r i ^ k j).det := by
  have h_exponents :
      (of fun i j : Fin a ↦ r i ^ l j) = of fun i j : Fin a ↦ r i ^ ((m : ℤ) + k j) := by
    simp_rw [← zpow_natCast, hl]
  have h_vandermonde : vandermonde r = of fun i j : Fin a ↦ r i ^ (j : ℤ) := by
    simp [vandermonde]
  rw [← h_vandermonde, rootCoeffEval_genericSchur_mul_det, h_exponents, det_zpow_add h_ne,
    zpow_natCast]

open scoped Classical in
/-- Weyl's character formula for a twist of `weylRep κ.1 κ.2`, for `a` odd. At the places `v` with
`p v` the regular element `y` enters through `Φ v y⁻¹`, at the others through the transpose of
its conjugate. The character, times the `m`-th power of the norm of `det y`, is the product of the
values of `q σ` at the eigenvalues of `σ y`. Above each place one `q σ` gives `det ^ m`; the other
is a Schur polynomial whose exponents come from those, `u v`, of Weyl's formula. -/
lemma New.Variety.mul_trace_weylRep_eq_prod_rootCoeffEval {E : Type} [Field E] [CMType E] {a : ℕ}
    [NeZero a]
    (ha : Odd a) (κ : Weight E) (p : InfinitePlace E → Prop) {u : InfinitePlace E → Fin a → ℤ}
    (hu : ∀ (v : InfinitePlace E) (j : Fin a),
      u v j = κ.2 v + ↑(diagramWeight (rankAt fun _ : InfinitePlace E ↦ Fin a) κ.1 (v, j.rev) + j))
    {q : (E →+* ℂ) → MvPolynomial (Fin a) ℤ} {l : (E →+* ℂ) → Fin a → ℕ} {m : ℕ}
    (hl_pos : ∀ v : InfinitePlace E, p v → ∀ j : Fin a, (l (Φ v) j : ℤ) = m + (a - 1 - u v j.rev))
    (hq_pos : ∀ v : InfinitePlace E, p v → q (Φ v) = genericSchur (l (Φ v)))
    (hq_conj_pos : ∀ v : InfinitePlace E, p v → q (star (Φ v)) = (-.X 0) ^ m)
    (hl_neg : ∀ v : InfinitePlace E, ¬p v → ∀ j : Fin a, (l (star (Φ v)) j : ℤ) = m + u v j)
    (hq_neg : ∀ v : InfinitePlace E, ¬p v → q (Φ v) = (-.X 0) ^ m)
    (hq_conj_neg : ∀ v : InfinitePlace E, ¬p v → q (star (Φ v)) = genericSchur (l (star (Φ v))))
    {y : GL (Fin a) E} (hy : y.val.charpoly.Separable) :
    (∏ σ : E →+* ℂ, σ y.val.det) ^ m *
        (weylRep κ.1 κ.2 fun v : InfinitePlace E ↦
          if p v then y⁻¹.map (Φ v) else transposeGL (y.map (star (Φ v)))).trace =
      ∏ σ : E →+* ℂ, rootCoeffEval (y.val.charpoly.map σ).roots (q σ) := by
  -- Number the eigenvalues `r σ` of `σ y`, and the eigenvalues `x v` of the component at `v`.
  let r (σ : E →+* ℂ) : Fin a ↪ ℂ := numberedRoots σ y.val.charpoly
  have h_roots (σ : E →+* ℂ) : (y.val.charpoly.map σ).roots = univ.val.map (r σ) :=
    roots_eq_map_numberedRoots hy σ
  have h_ne (σ : E →+* ℂ) (i : Fin a) : r σ i ≠ 0 :=
    spectrum.ne_zero_of_mem_of_unit (mem_spectrum_of_isRoot_charpoly (isRoot_numberedRoots hy σ i))
  have h_det (σ : E →+* ℂ) : σ y.val.det = univ.prod (r σ) := by
    simp [RingHom.map_det, det_eq_prod_roots_charpoly, charpoly_map, h_roots, List.prod_ofFn]
  have hx_inj (v : InfinitePlace E) :
      Function.Injective fun i : Fin a ↦ if p v then (r (Φ v) i.rev)⁻¹ else r (star (Φ v)) i := by
    intro i j
    by_cases hv : p v <;> simp [hv]
  let x (v : InfinitePlace E) : Fin a ↪ ℂ :=
    ⟨fun i ↦ if p v then (r (Φ v) i.rev)⁻¹ else r (star (Φ v)) i, hx_inj v⟩
  have hx_root (v : InfinitePlace E) (i : Fin a) : IsRoot
      (if p v then y⁻¹.map (Φ v) else transposeGL (y.map (star (Φ v)))).val.charpoly (x v i) := by
    by_cases hv : p v
    · -- `coe_units_inv` and `IsRoot.def` are erased because with them simp rewrites the goal past
      -- `mem_spectrum_iff_isRoot_charpoly`.
      simpa [x, hv, -coe_units_inv, -IsRoot.def, ← mem_spectrum_iff_isRoot_charpoly] using
        isRoot_numberedRoots hy (Φ v) i.rev
    · simpa [x, hv] using isRoot_numberedRoots hy (star (Φ v)) i
  -- Multiply by the Vandermonde determinants of the `x v`, apply Weyl's formula, and compare the
  -- factors place by place.
  apply mul_right_cancel₀
    (prod_ne_zero_iff.mpr fun v (_hv : v ∈ univ) ↦ det_vandermonde_ne_zero_iff.mpr (x v).injective)
  -- Weyl's formula turns the trace times the Vandermonde determinants into a product over the
  -- places `v` of determinants in the `x v`, with the exponents `u v`.
  simp_rw [mul_assoc, trace_weylRep _ _ hx_root, ← hu]
  -- The other side is a product over the embeddings; they come in pairs `Φ v`, `star (Φ v)`.
  simp_rw [h_det, h_roots, prod_embeddings_eq_prod_pairs, ← prod_pow, ← prod_mul_distrib]
  refine prod_congr rfl fun v _ ↦ ?_
  rw [show vandermonde (x v) = of fun i j : Fin a ↦ x v i ^ (j : ℤ) by simp [vandermonde]]
  by_cases hv : p v
  · -- Both determinants in the inverted eigenvalues give the same factor `(∏ r) ^ (1 - a)`.
    have h_bialternant : rootCoeffEval (univ.val.map (r (Φ v))) (genericSchur (l (Φ v))) *
        (of fun i j : Fin a ↦ r (Φ v) i ^ (j : ℤ)).det = univ.prod (r (Φ v)) ^ m *
        (of fun i j : Fin a ↦ r (Φ v) i ^ (a - 1 - u v j.rev)).det :=
      rootCoeffEval_genericSchur_mul_det_zpow (h_ne (Φ v)) (hl_pos v hv)
    have h_rev (j : Fin a) : (a - 1 - j.rev : ℤ) = j := by simp [Fin.val_rev]
    simp only [hq_pos v hv, hq_conj_pos v hv, x, hv, ite_true, Function.Embedding.coeFn_mk, h_rev,
      map_pow, map_neg, det_inv_rev_zpow (h_ne (Φ v)), rootCoeffEval_X_zero_of_odd ha, neg_neg,
      prod_mul_distrib]
    -- What is left is `h_bialternant` times the factors that the two sides share.
    linear_combination
      -univ.prod (r (star (Φ v))) ^ m * univ.prod (r (Φ v)) ^ (1 - a : ℤ) * h_bialternant
  · have h_bialternant :
        rootCoeffEval (univ.val.map (r (star (Φ v)))) (genericSchur (l (star (Φ v)))) *
        (of fun i j : Fin a ↦ r (star (Φ v)) i ^ (j : ℤ)).det = univ.prod (r (star (Φ v))) ^ m *
        (of fun i j : Fin a ↦ r (star (Φ v)) i ^ u v j).det :=
      rootCoeffEval_genericSchur_mul_det_zpow (h_ne (star (Φ v))) (hl_neg v hv)
    simp only [hq_neg v hv, hq_conj_neg v hv, x, hv, ite_false, Function.Embedding.coeFn_mk,
      map_pow, map_neg, rootCoeffEval_X_zero_of_odd ha, neg_neg, prod_mul_distrib]
    linear_combination -univ.prod (r (Φ v)) ^ m * h_bialternant

/-- In the representation `weylRep κ.1 κ.2` of weight `κ` (`New.weylRep`), a family whose component
at `v` is the scalar `t ^ ε v` acts by a power of `t`: the exponent is the sum of the `ε v` times
the degree of the weight at `v`. -/
lemma New.Variety.weylRep_of_scalar {E : Type} [Field E] [NumberField E] {a : ℕ} (κ : Weight E)
    {t : ℂ} (ht : t ≠ 0) {ε : InfinitePlace E → ℤ} {g : InfinitePlace E → GL (Fin a) ℂ}
    (hg : ∀ v : InfinitePlace E, (g v).val = t ^ ε v • 1) :
    weylRep κ.1 κ.2 g =
      t ^ (∑ v : InfinitePlace E, ε v * (a * κ.2 v + ∑ h ∈ Finset.range a, h * κ.1 v h)) • 1 := by
  -- On each component the scalar `t ^ ε v` acts through the Schur functor by its degree; the
  -- exponents add up.
  simp [weylRep, hg, schur_smul, Units.smul_def, smul_smul, ← zpow_natCast, ← _root_.zpow_mul,
    ← DiscreteSeries.zpow_sum_of_ne_zero ht, ← zpow_add₀ ht, mul_add, sum_add_distrib, mul_assoc]

open scoped Classical in
/-- The complex embeddings of `QuadField d₀` are `s₀` and its conjugate. -/
lemma New.Variety.pair_star_eq_univ {d₀ : ℕ} [Fact (d₀ % 4 = 3)] (s₀ : QuadField d₀ →+* ℂ) :
    ({star s₀, s₀} : Finset (QuadField d₀ →+* ℂ)) = univ := by
  exact eq_univ_of_card _ (by simp [Embeddings.card, finrank_eq_two])

private lemma New.Variety.eq_star_or_eq {d₀ : ℕ} [Fact (d₀ % 4 = 3)] (s s₀ : QuadField d₀ →+* ℂ) :
    s = star s₀ ∨ s = s₀ := by
  classical
  simpa [← pair_star_eq_univ s₀] using mem_univ s

/-- Exactly one of `s` and its conjugate is `s₀`. -/
lemma New.Variety.conjugate_eq_iff_ne {d₀ : ℕ} [Fact (d₀ % 4 = 3)] (s s₀ : QuadField d₀ →+* ℂ) :
    ComplexEmbedding.conjugate s = s₀ ↔ s ≠ s₀ := by
  change star s = s₀ ↔ s ≠ s₀
  rcases eq_star_or_eq s s₀ with rfl | rfl <;> simp

open scoped Classical in
/-- An embedding of `E` restricts to `s₀` or to its conjugate. -/
lemma New.Variety.apply_eq_ite_comp_eq {E : Type} [Field E] {d₀ : ℕ} [Fact (d₀ % 4 = 3)]
    (i : QuadField d₀ →+* E) (s₀ : QuadField d₀ →+* ℂ) (σ : E →+* ℂ) (x : QuadField d₀) :
    σ (i x) = if σ.comp i = s₀ then s₀ x else star s₀ x := by
  have h_ne : star s₀ ≠ s₀ := by simp
  rw [← RingHom.comp_apply σ i x]
  rcases eq_star_or_eq (σ.comp i) s₀ with h_star | h_self
  · simp [h_star, h_ne]
  · simp [h_self]

open scoped Classical in
/-- An extension to `GL (Fin a) E` of the embedding of the unitary group at the infinite places:
`z` goes to `Φ v z` if `p v` holds, and to the inverse transpose of its conjugate if not. -/
noncomputable def New.Variety.extendedEmbedding {E : Type} [Field E] [CMType E] {a : ℕ}
    (p : InfinitePlace E → Prop) : GL (Fin a) E →* InfinitePlace E → GL (Fin a) ℂ :=
  MonoidHom.mk' (fun z v ↦ if p v then z.map (Φ v) else transposeGL (z⁻¹.map (star (Φ v))))
    (by simp +contextual [funext_iff, apply_ite, Units.ext_iff])

/-- The matrices of weight `κ` along `extendedEmbedding p`, twisted by the `-m`-th power of the
norm of the determinant. -/
noncomputable def New.Variety.twistedWeylMatrix {E : Type} [Field E] [CMType E] {a : ℕ}
    (κ : Weight E) (p : InfinitePlace E → Prop) (m : ℕ) :
    GL (Fin a) E →* Matrix (WeylIndex (Fin a) κ.1) (WeylIndex (Fin a) κ.1) ℂ where
  toFun z := (∏ σ : E →+* ℂ, σ z⁻¹.val.det) ^ m • weylRep κ.1 κ.2 (extendedEmbedding p z)
  map_one' := by simp
  map_mul' := by simp [prod_mul_distrib, smul_smul, mul_pow]

/-- The representation given by the matrices `twistedWeylMatrix κ p m`. -/
noncomputable def New.Variety.twistedWeylRep {E : Type} [Field E] [CMType E] {a : ℕ}
    (κ : Weight E) (p : InfinitePlace E → Prop) (m : ℕ) :
    Representation ℂ (GL (Fin a) E) (WeylIndex (Fin a) κ.1 → ℂ) :=
  toLinAlgEquiv'.toMonoidHom.comp (twistedWeylMatrix κ p m)

/-- For unitary `y`, `twistedWeylRep κ p m y` is the action of `ȳ` in weight `κ`. -/
lemma New.Variety.weightRep_entryConj_eq_twistedWeylRep {E : Type} [Field E] [CMType E] {a : ℕ}
    (κ : Weight E) (p : InfinitePlace E → Prop) (m : ℕ) (y : U (1 : Matrix (Fin a) (Fin a) E)) :
    (stdSpace E (Fin a)).weightRep κ.1 κ.2 (entryConj y) = twistedWeylRep κ p m y.val := by
  -- The determinant has norm one, and both branches of the embedding at `v` are `Φ v y`; on the
  -- other side `entryConj` and `stdSpace_weightRep_apply` each conjugate the entries once.
  have h_unitary : y.val.valᴴ * 1 * y.val.val = 1 := mem_unitaryGroupOf_iff.1 y.prop
  have h_norm (v : InfinitePlace E) :
      Φ v y.val.val.det * starRingEnd ℂ (Φ v y.val.val.det) = 1 := by
    simpa [mul_comm] using congrArg (fun M : Matrix (Fin a) (Fin a) E ↦ Φ v M.det) h_unitary
  have h_embedding : extendedEmbedding p y.val =
      fun v ↦ .map ((Φ v).comp (starRingEnd E)) (entryConj y).val := by
    ext v
    simp [extendedEmbedding, entryConj, invTransposeGL, transposeGL, starRingEnd_apply (R := E),
      apply_ite, Matrix.ite_apply, ← map_inv, inv_eq_left_inv h_unitary]
  refine LinearMap.ext fun w ↦ (stdSpace_weightRep_apply (entryConj y) w).trans ?_
  simp [twistedWeylRep, twistedWeylMatrix, prod_embeddings_eq_prod_pairs, h_norm, h_embedding]

/-- Let `E` be a CM field with chosen embeddings `Φ v`, let `i : ℚ(i√d₀) →+* E`, and let `s₀` be a
complex embedding of ℚ(i√d₀). Let `p v` mean that `Φ v` extends `s₀`, and consider the
representation `twistedWeylRep κ p m` of `GL_a(E)` given by the matrices `twistedWeylMatrix κ p m`
for the weight `κ`. Then there is one integer `A` such that, for every `x` in `(QuadField d₀)ˣ`, the
scalar matrix `i(x̄)` acts by `s̄₀ x ^ (-A) * s₀ x ^ (-μ)`, where `μ` is `m * a` times the number of
infinite places of `E`. -/
lemma New.Variety.exists_twistedWeylRep_scalar {E : Type} [Field E] [CMType E] {a d₀ : ℕ}
    [Fact (d₀ % 4 = 3)] (i : QuadField d₀ →+* E) (s₀ : QuadField d₀ →+* ℂ) (κ : Weight E) (m : ℕ) :
    ∃ A : ℤ, ∀ x : (QuadField d₀)ˣ,
      twistedWeylRep κ (fun v : InfinitePlace E ↦ (Φ v).comp i = s₀) m
          (GeneralLinearGroup.scalar (Fin a) (star (x.map i))) =
        (star s₀ x ^ (-A) * s₀ x ^ (-(m * a * Core.numInfPlaces E : ℕ) : ℤ)) • 1 := by
  classical
  -- The twist gives `(s₀ x * star s₀ x)⁻¹ ^ μ`, and the weight gives `star s₀ x ^ B`.
  let p (v : InfinitePlace E) : Prop := (Φ v).comp i = s₀
  let ε (v : InfinitePlace E) : ℤ := if p v then 1 else -1
  let B : ℤ := ∑ v, ε v * (a * κ.2 v + ∑ h ∈ range a, h * κ.1 v h)
  set μ : ℕ := m * a * Core.numInfPlaces E with hμ
  refine ⟨μ - B, fun x ↦ ?_⟩
  set z : GL (Fin a) E := GeneralLinearGroup.scalar (Fin a) (star (x.map i)) with hz
  have h_embedding (v : InfinitePlace E) :
      (extendedEmbedding p z v).val = star s₀ x ^ ε v • 1 := by
    by_cases hv : (Φ v).comp i = s₀ <;>
      simp [extendedEmbedding, hz, ε, p, hv, apply_eq_ite_comp_eq i s₀, conjugate_eq_iff_ne,
        smul_one_eq_diagonal, ← map_inv]
  have h_weight : weylRep κ.1 κ.2 (extendedEmbedding p z) = star s₀ x ^ B • 1 :=
    weylRep_of_scalar κ (by simp) h_embedding
  have h_pair (v : InfinitePlace E) :
      starRingEnd ℂ (Φ v (i x)) * starRingEnd ℂ (star (Φ v) (i x)) = s₀ x * star s₀ x := by
    by_cases hv : (Φ v).comp i = s₀ <;>
      simp [hv, apply_eq_ite_comp_eq i s₀, conjugate_eq_iff_ne, mul_comm]
  have h_norm : ∏ σ : E →+* ℂ, starRingEnd ℂ (σ (i x)) =
      (s₀ x * star s₀ x) ^ Core.numInfPlaces E := by
    simp only [prod_embeddings_eq_prod_pairs, h_pair, Finset.prod_const, card_univ]
  have h_twist : (∏ σ : E →+* ℂ, σ z⁻¹.val.det) ^ m = (s₀ x * star s₀ x)⁻¹ ^ μ := by
    -- With `mul_inv_rev`, simp inverts the product in the other order, against the right side.
    simp [hz, prod_pow, h_norm, hμ, -_root_.mul_inv_rev, ← pow_mul, mul_comm, mul_left_comm,
      mul_assoc]
  have h_exponent :
      (s₀ x * star s₀ x)⁻¹ ^ μ * star s₀ x ^ B = star s₀ x ^ (-(μ - B)) * s₀ x ^ (-μ : ℤ) := by
    simp [zpow_sub₀, div_eq_mul_inv, mul_pow, mul_comm, mul_assoc]
  simp only [twistedWeylRep, twistedWeylMatrix, MonoidHom.comp_apply, MonoidHom.coe_mk,
    OneHom.coe_mk, p, h_weight, h_twist, smul_smul, h_exponent]
  simp

/-- Let `i` embed the imaginary quadratic field `QuadField d₀` in `E`, and let `s₀` be a complex
embedding of `QuadField d₀`. The representation `ξ` extends the weight `κ` to `GL (Fin a) E`. The
centre acts through the exponents `A`, with `A s₀ = μ`. The eigenvalues of the test eigenforms with
coefficients in `ξ` occur in the weights `z + μ`, for `z` a jump of `κ` at an embedding over `s₀`
(`New.Variety.OccursInWeight` with the parameter `N + 1`). -/
structure New.Variety.IsCoefficientSystem {E : Type} [Field E] [CMType E] {a d₀ : ℕ}
    [HasQuadSubfield d₀ E] (i : QuadField d₀ →+* E) (s₀ : QuadField d₀ →+* ℂ) (κ : Weight E)
    (ξ : Representation ℂ (GL (Fin a) E) (WeylIndex (Fin a) κ.1 → ℂ)) (μ N : ℕ)
    (A : (QuadField d₀ →+* ℂ) → ℤ) : Prop where
  /-- The central exponent at `s₀` is `μ`. -/
  exponent_self : A s₀ = μ
  /-- For unitary `y`, `ξ y` is the action of `ȳ` in weight `κ`. -/
  weightRep_entryConj (y : U (1 : Matrix (Fin a) (Fin a) E)) :
    (stdSpace E (Fin a)).weightRep κ.1 κ.2 (entryConj y) = ξ y.val
  /-- For `x` in `(QuadField d₀)ˣ`, the scalar `x̄` acts by `∏ s, s x ^ (-A s)`. -/
  map_scalar (x : (QuadField d₀)ˣ) :
    ξ (GeneralLinearGroup.scalar (Fin a) (star (x.map i))) =
      (∏ s : QuadField d₀ →+* ℂ, s x ^ (-A s)) • 1
  /-- The jumps of `κ` at embeddings over `s₀` are at least `-μ`. -/
  jump_add_nonneg {σ : E →+* ℂ} (hσ : σ.comp i = s₀) {z : ℤ} (hz : z ∈ jumps κ a σ) : 0 ≤ z + μ
  /-- Let `z` be a jump of `κ` at `σ` over `s₀`, for the given CM type. Let `Ψ` be any CM type with
  base place `v₀` whose only embedding over `s₀` is `σ`, at `v₀`. Then the eigenvalues of every
  test eigenform of neat level for `Ψ` occur in weight `z + μ`. -/
  occursInWeight {σ : E →+* ℂ} (hσ : σ.comp i = s₀) {z : ℤ} (hz : z ∈ jumps κ a σ)
    [Ψ : CMBase E] (hv₀ : Ψ.Φ v₀ = σ) (hΨ : ∀ v : InfinitePlace E, v ≠ v₀ → (Ψ.Φ v).comp i ≠ s₀)
    {𝔑 : 𝓞 E} (hN : IsNeat (Fin a) 𝔑) {φ : GL (Fin a) (𝔸f E) → WeylIndex (Fin a) κ.1 → ℂ}
    {θ : SafePlace 𝔑 → ℕ → ℂ} (h_form : IsTestEigenform 𝔑 ξ φ θ) :
    OccursInWeight a (N + 1) θ (z + μ).toNat

open scoped Classical in
/-- The trace of `twistedWeylRep κ p m` at `y⁻¹` is the left side of
`mul_trace_weylRep_eq_prod_rootCoeffEval`: the `m`-th power of the norm of `det y` times the trace
of `weylRep κ.1 κ.2` at the family that is `Φ v y⁻¹` where `p v` holds and the transpose of the
conjugate of `y` elsewhere. -/
private lemma New.Variety.trace_twistedWeylRep_inv {E : Type} [Field E] [CMType E] {a : ℕ}
    (κ : Weight E) (p : InfinitePlace E → Prop) (m : ℕ) (y : GL (Fin a) E) :
    (twistedWeylRep κ p m y⁻¹).trace ℂ (WeylIndex (Fin a) κ.1 → ℂ) =
      (∏ σ : E →+* ℂ, σ y.val.det) ^ m *
        (weylRep κ.1 κ.2 fun v : InfinitePlace E ↦
          if p v then y⁻¹.map (Φ v) else transposeGL (y.map (star (Φ v)))).trace := by
  change (Matrix.toLin' ((∏ σ : E →+* ℂ, σ y.val.det) ^ m • weylRep κ.1 κ.2 fun v ↦
    if p v then y⁻¹.map (Φ v) else transposeGL (y.map (star (Φ v))))).trace ℂ _ = _
  rw [trace_toLin'_eq, trace_smul, smul_eq_mul]

/-- Let `a` be odd, `i` an embedding of the imaginary quadratic field `QuadField d₀` in `E` and `s₀`
a complex embedding of `QuadField d₀`. A weight `κ` extends to a representation `ξ` of
`GL (Fin a) E` on which the scalars from `(QuadField d₀)ˣ` (through `i`) act through exponents `A`
with `A s₀ = μ`, and whose test eigenforms occur in the weights `z + μ` for `z` a jump of `κ` at an
embedding over `s₀`, for some `N` (`New.Variety.IsCoefficientSystem`). The proof compares traces
directly and does not pass through automorphic representations of `GL_n`.

In the literature the same occurrence follows from the description, due to Labesse and to
Moeglin–Waldspurger, of automorphic representations of unitary groups via `GL_n`. -/
lemma New.Variety.exists_isCoefficientSystem {E : Type} [Field E] [CMType E] {a d₀ : ℕ}
    [HasQuadSubfield d₀ E] (ha : Odd a) (i : QuadField d₀ →+* E) (s₀ : QuadField d₀ →+* ℂ)
    (κ : Weight E) :
    ∃ (ξ : Representation ℂ (GL (Fin a) E) (WeylIndex (Fin a) κ.1 → ℂ)) (μ N : ℕ)
      (A : (QuadField d₀ →+* ℂ) → ℤ), IsCoefficientSystem i s₀ κ ξ μ N A := by
  classical
  -- Twist the representation of weight `κ` so that its character is a product over all embeddings
  -- `σ` of polynomials `q σ` in the eigenvalues: a Schur polynomial with natural exponents `l σ` if
  -- `σ` extends `s₀`, and `det ^ m` if not. Then `occursInWeight_of_isTestEigenform` applies.
  have ha_ne : NeZero a := NeZero.of_pos ha.pos
  -- `u v` are the exponents in Weyl's formula, `k σ` the exponents for the eigenvalues at `σ`;
  -- adding a large `m` turns them into natural numbers `l σ`.
  let u (v : InfinitePlace E) (j : Fin a) : ℤ :=
    κ.2 v + ↑(diagramWeight (rankAt fun _ : InfinitePlace E ↦ Fin a) κ.1 (v, j.rev) + j)
  let k (σ : E →+* ℂ) (j : Fin a) : ℤ :=
    if σ = Φ (.mk σ) then a - 1 - u (.mk σ) j.rev else u (.mk σ) j
  obtain ⟨m, hm_bound⟩ := Finite.exists_le (Int.natAbs ∘ k.uncurry)
  let l (σ : E →+* ℂ) (j : Fin a) : ℕ := (m + k σ j).toNat
  have hl (σ : E →+* ℂ) (j : Fin a) : (l σ j : ℤ) = m + k σ j := by
    have h_abs : (k σ j).natAbs ≤ m := hm_bound (σ, j)
    exact Int.toNat_of_nonneg (by omega)
  let p (v : InfinitePlace E) : Prop := (Φ v).comp i = s₀
  let q (σ : E →+* ℂ) : MvPolynomial (Fin a) ℤ :=
    if σ.comp i = s₀ then genericSchur (l σ) else (-.X 0) ^ m
  let ξ : Representation ℂ (GL (Fin a) E) (WeylIndex (Fin a) κ.1 → ℂ) := twistedWeylRep κ p m
  -- The exponents and polynomials at `Φ v` and at its conjugate, as
  -- `mul_trace_weylRep_eq_prod_rootCoeffEval` needs them.
  have hl_pos (v : InfinitePlace E) (j : Fin a) :
      (l (Φ v) j : ℤ) = m + (a - 1 - u v j.rev) := by simp [hl, k]
  have hq_conj_pos (v : InfinitePlace E) (hv : p v) : q (star (Φ v)) = (-.X 0) ^ m := by
    simp [q, show (Φ v).comp i = s₀ from hv]
  have hl_neg (v : InfinitePlace E) (j : Fin a) :
      (l (star (Φ v)) j : ℤ) = m + u v j := by simp [hl, k]
  have hq_conj_neg (v : InfinitePlace E) (hv : ¬p v) :
      q (star (Φ v)) = genericSchur (l (star (Φ v))) := by
    simp [q, show ¬(Φ v).comp i = s₀ from hv, conjugate_eq_iff_ne]
  have h_char (y : GL (Fin a) E) (hy : y.val.charpoly.Separable) :
      (ξ y⁻¹).trace ℂ (WeylIndex (Fin a) κ.1 → ℂ) =
        ∏ σ, rootCoeffEval (y.val.charpoly.map σ).roots (q σ) := by
    rw [trace_twistedWeylRep_inv κ p m y]
    exact mul_trace_weylRep_eq_prod_rootCoeffEval ha κ p (u := u) (l := l) (fun _ _ ↦ rfl)
      (fun v _ ↦ hl_pos v) (fun _ hv ↦ ite_eq_left hv) hq_conj_pos
      (fun v _ ↦ hl_neg v) (fun _ hv ↦ ite_eq_right hv) hq_conj_neg hy
  let μ : ℕ := m * a * Core.numInfPlaces E
  obtain ⟨A, h_scalar⟩ := exists_twistedWeylRep_scalar (a := a) i s₀ κ m
  -- Each jump at `σ` is some `k σ j = l σ j - m`, so adding `μ` gives the weight in
  -- `occursInWeight_of_isTestEigenform`.
  have h_jump (σ : E →+* ℂ) : ∀ z ∈ jumps κ a σ, ∃ j : Fin a,
      z + μ = (m * (a - 1 + a * (Core.numInfPlaces E - 1)) + l σ j : ℕ) := by
    refine Multiset.forall_mem_map_iff.mpr fun n hn ↦ ?_
    let n' : Fin a := ⟨n, Multiset.mem_range.mp hn⟩
    refine ⟨if σ = Φ (.mk σ) then n' else n'.rev, ?_⟩
    simp [hl, k, u, μ, n', diagramWeight_apply, Fintype.card_pos]
    -- What is left is index arithmetic with products of casts, which `omega` cannot expand;
    -- `grind` closes it once the context is cleared, and does not finish with the whole context.
    clear * - hn
    grind
  refine ⟨ξ, μ, ∑ σ, (q σ).totalDegree, fun s ↦ if s = s₀ then μ else A,
    { exponent_self := ite_eq_left rfl
      weightRep_entryConj := weightRep_entryConj_eq_twistedWeylRep κ _ m
      map_scalar := fun x ↦ ?_
      jump_add_nonneg := fun _hσ z hz ↦ ?_
      occursInWeight := fun hσ z hz ↦ ?_ }⟩
  · rw [h_scalar, ← pair_star_eq_univ s₀]
    simp [μ, mul_comm]
  · obtain ⟨j, hj⟩ := h_jump _ z hz
    omega
  · obtain ⟨j, hj⟩ := h_jump _ z hz
    rintro Ψ rfl hΨ 𝔑 hN φ θ h_form
    rw [hj, Int.toNat_natCast]
    refine occursInWeight_of_isTestEigenform ha h_char (ite_eq_left hσ) (ite_eq_right ?_)
      (fun v hv ↦ ite_eq_right (hΨ v hv)) hN
      h_form j
    simpa [conjugate_eq_iff_ne] using hσ
