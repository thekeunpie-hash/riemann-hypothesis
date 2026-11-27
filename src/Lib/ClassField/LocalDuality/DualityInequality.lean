module

public import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Sheaves.Presheaf
public import Lib.Speed
import Lib.ClassField.Places.DecompositionCyclotomic
public import Lib.ClassField.Places.ProfiniteGalois
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.LocalRing.Quotient
public import Lib.ClassField.GaloisCohomology.KummerCyclicClasses
import Lib.ClassField.Places.LocalFields
public import Lib.General.Algebra.CartanMap

section
/-!
# Coker/ker indices and Tate's index formula for cyclic actions of prime order

For a map `f` of abelian groups, `New.cokerKerIndex f` is the rational number `#coker f / #ker f`.
`(l : End ℤ A)` denotes multiplication by the natural number `l` on `A`. The file gives counting
tools for this index and for equivariant maps into finite projective `𝔽_l[Δ]`-modules.

## Main definitions and results

* `New.cokerKerIndex`: the rational number `#coker f / #ker f`; it is `0` if either group is
  infinite, so `cokerKerIndex f ≠ 0` says that both are finite.
* `New.cokerKerIndex_natCast_eq_of_ne_zero`: the index of `l` is unchanged under maps with finite
  kernel and cokernel.
* `New.card_hom_lattice_eq_card_equivariant`: `A / torsion` and a finite `Δ`-set `Z` have equally
  many equivariant maps to a finite projective `𝔽_l[Δ]`-module. This needs `A` finitely generated,
  of rank at most `#Z`, and with an equivariant map `A → ℝ^Z` whose image spans `ℝ^Z`.
* `New.Tate.index_formula`: computes the index of the norm group in the fixed points of an
  automorphism `σ` with `σ ^ l = 1`, `l` prime, from the indices of multiplication by `l`. It
  assumes that the kernel of the norm is the image of `σ - 1`, and it takes the place of the
  Herbrand quotient.
* `New.tate_index_formula_norm`: `New.Tate.index_formula` for a Galois-stable subgroup `U` of `Lˣ`
  with `H¹(Gal(L/K), U) = 0`, where `L / K` is Galois of prime degree. The hypothesis `hH1` gives
  this vanishing through Hilbert's Theorem 90.

## Relation to the literature

Known; see `Lib.ClassField.GreenbergWiles.CocycleCounts` and
`Lib.ClassField.GaloisCohomology.KummerCyclicClasses` for sources.
-/

@[expose] public section

/-! ## The coker/ker index and equivariant maps from lattices to projective modules -/

namespace New

variable {l : ℕ}
  {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C)

open Nat Function LinearMap Submodule Module Matrix AddSubgroup Representation MonoidAlgebra

attribute [local instance low] Fintype.ofFinite

/-- For a linear map f : A → B, the rational number #coker f / #ker f; it is 0 if either group
is infinite. -/
noncomputable def cokerKerIndex : ℚ := Nat.card (B ⧸ f.range) / Nat.card f.ker

/-- (a) The index of `g ∘ f` is `#coker g * ([B : I ⊔ N] / #(I ⊓ N)) / #ker f`, where
`I = f.range` and `N = g.ker`. (b) If one of the indices of `f` and `g` is nonzero, the index
of `g ∘ f` is their product. -/
lemma cokerKerIndex_comp :
    -- (a)
    cokerKerIndex (g ∘ₗ f) =
      g.range.cardQuot * ((f.range ⊔ g.ker).cardQuot / Nat.card (f.range ⊓ g.ker :)) /
        Nat.card f.ker ∧
    -- (b)
    (cokerKerIndex f ≠ 0 ∨ cokerKerIndex g ≠ 0 →
     cokerKerIndex (g ∘ₗ f) = cokerKerIndex f * cokerKerIndex g) := by
  -- Write `I = f.range`, `N = g.ker` and `t = [N : I ⊓ N] = [I ⊔ N : I]`. All four groups are
  -- counted by index towers; `t` occurs in `coker f` and in `ker g` and cancels if nonzero.
  set t : ℕ := f.range.toAddSubgroup.relIndex g.ker.toAddSubgroup with ht
  have ker_g : Nat.card g.ker = Nat.card (f.range ⊓ g.ker :) * t := by
    simpa [bot_inf_eq] using (relIndex_inf_mul_relIndex ⊥ f.range.toAddSubgroup
      g.ker.toAddSubgroup).symm
  have ker_comp : Nat.card (g ∘ₗ f).ker = Nat.card f.ker * Nat.card (f.range ⊓ g.ker :) := by
    simpa [relIndex_ker, AddSubgroup.map_comap_eq] using
      (relIndex_mul_relIndex ⊥ _ _ bot_le (f.toAddMonoidHom.ker_le_comap g.ker.toAddSubgroup)).symm
  have coker_f : f.range.cardQuot = t * (f.range ⊔ g.ker).cardQuot := by
    simp [ht, cardQuot, sup_toAddSubgroup,
      ← relIndex_mul_index (toAddSubgroup_mono (le_sup_left (b := g.ker)))]
  have coker_comp : (g ∘ₗ f).range.cardQuot = (f.range ⊔ g.ker).cardQuot * g.range.cardQuot := by
    simp [cardQuot, range_comp, sup_toAddSubgroup, index_map, map_toAddSubgroup]
    -- `↑g` and `g.toAddMonoidHom` are the same additive map only by unfolding the coercion.
    rfl
  simp only [cokerKerIndex, ← cardQuot_apply, ker_g, ker_comp, coker_f, coker_comp, Nat.cast_mul]
  constructor
  · ring
  · intro h_ne
    -- If `t = 0`, the formulas for `coker f` and `ker g` make both indices vanish.
    have t_ne : (t : ℚ) ≠ 0 := fun ht0 ↦ by simp [ht0] at h_ne
    field_simp

/-- For a short exact sequence `0 → A → B → C → 0` of abelian groups given by `f` and `g`, let
q_X = #(X/lX) / #X[l] be the rational cokernel-over-kernel index of multiplication by `l` on X,
taken to be 0 if either group is infinite. If q_A ≠ 0, meaning A/lA and A[l] are both finite, then
q_B = q_A · q_C. -/
lemma cokerKerIndex_mul_of_exact (hf : Function.Injective f) (h_exact : Exact f g)
    (hg : Surjective g) (hA : cokerKerIndex (l : End ℤ A) ≠ 0) :
    cokerKerIndex (l : End ℤ B) = cokerKerIndex (l : End ℤ A) * cokerKerIndex (l : End ℤ C) := by
  -- Multiplication by `l` on `B` factors through the range `X` of `ψ (b, a) = (l b - f a, g b)` as
  -- `B → X → B`. The first map has the index of `l` on `A`, the second that of `l` on `C`; both
  -- are read off from the exact sequence `A → B × A → B × C → C` by the first part of
  -- `cokerKerIndex_comp`.
  let ψ : B × A →ₗ[ℤ] B × C := (coprod (l : End ℤ B) (-f)).prod (g ∘ₗ fst ℤ B A)
  have exact_left : Exact (f.prod (l : End ℤ A)) ψ := by
    suffices h_iff : ∀ (b : B) (a : A),
        (l • b + -f a = 0 ∧ ∃ y : A, f y = b) ↔ ∃ y : A, f y = b ∧ l • f y = f a by
      simpa [Exact, ψ, h_exact _, ← hf.eq_iff] using h_iff
    grind
  have exact_right : Exact ψ (coprod (-g) (l : End ℤ C)) := by
    -- If `g b = l • g x`, then `l • x - b` lies in the range of `f`; take `b' = x`.
    have h_iff (b x : B) :
        -g b + l • g x = 0 ↔ ∃ b' : B, (∃ a : A, l • b' + -f a = b) ∧ g b' = g x := by
      grind [Exact, h_exact (l • x - b)]
    simpa [Exact, ψ, hg.forall] using h_iff
  let α : B →ₗ[ℤ] ψ.range := ψ.rangeRestrict ∘ₗ inl ℤ B A
  let β : ψ.range →ₗ[ℤ] B := fst ℤ B C ∘ₗ ψ.range.subtype
  have h_factor : (l : End ℤ B) = β ∘ₗ α := by aesop
  -- Write `l = snd ∘ (f, l)` on `A`: both indices compare `B × 0` with `ker ψ` inside `B × A`.
  have idx_α : cokerKerIndex (l : End ℤ A) = cokerKerIndex α := by
    rw [← snd_prod f (l : End ℤ A), (cokerKerIndex_comp (f.prod (l : End ℤ A)) (snd ℤ B A)).left,
      (cokerKerIndex_comp (inl ℤ B A) ψ.rangeRestrict).left]
    simp_all [exact_iff, range_inl, ← ker_eq_bot, sup_comm, inf_comm, bot_inf_eq]
  -- Write `l = coprod (-g) l ∘ inr` on `C`: both compare `0 × C` with `range ψ` in `B × C`.
  have idx_β : cokerKerIndex (l : End ℤ C) = cokerKerIndex β := by
    rw [← coprod_inr (-g) (l : End ℤ C),
      (cokerKerIndex_comp (inr ℤ B C) (coprod (-g) (l : End ℤ C))).left,
      (cokerKerIndex_comp ψ.range.subtype (fst ℤ B C)).left]
    simp_all [exact_iff, range_inr, ← range_eq_top, range_coprod, sup_comm, inf_comm]
  -- The index is multiplicative in `l = β ∘ α`, since `α` has nonzero index.
  rw [idx_α, idx_β, h_factor]
  exact (cokerKerIndex_comp α β).right (.inl (by rwa [← idx_α]))

/-- If `f : A → B` has finite kernel and cokernel, then `#(A/lA) / #A[l] = #(B/lB) / #B[l]`, each
side read as `0` when one of its groups is infinite. -/
lemma cokerKerIndex_natCast_eq_of_ne_zero (h : cokerKerIndex f ≠ 0) :
    cokerKerIndex (l : End ℤ A) = cokerKerIndex (l : End ℤ B) := by
  -- Take indices in `f ∘ l = l ∘ f` and cancel the nonzero index of `f`.
  have h_comm : f ∘ₗ (l : End ℤ A) = (l : End ℤ B) ∘ₗ f := by aesop
  apply mul_right_cancel₀ h
  calc cokerKerIndex (l : End ℤ A) * cokerKerIndex f
    _ = cokerKerIndex (f ∘ₗ (l : End ℤ A)) :=
      ((cokerKerIndex_comp (l : End ℤ A) f).right (.inr h)).symm
    _ = cokerKerIndex (l : End ℤ B) * cokerKerIndex f := by
      rw [h_comm, (cokerKerIndex_comp f (l : End ℤ B)).right (.inl h), mul_comm]

variable [NeZero l] [Module.Finite ℤ A]

/-- On a finitely generated abelian group `A`, multiplication by `l ≠ 0` has index
`#(A / l A) / #A[l] = l ^ rank A`. -/
lemma cokerKerIndex_natCast_eq_pow_finrank : cokerKerIndex (l : End ℤ A) = l ^ finrank ℤ A := by
  -- The torsion subgroup is finite, so we may pass to the free quotient `A ⧸ torsion ℤ A`, where
  -- multiplication by `l` is injective with image of index `l ^ rank`.
  have h_finite_torsion : Finite (torsion ℤ A) := finite_of_fg_torsion _ torsion_isTorsion
  have idx_ne : cokerKerIndex (torsion ℤ A).mkQ ≠ 0 := by
    simpa [cokerKerIndex] using (card_pos (α := torsion ℤ A)).ne'
  have ker_eq : ker (l : End ℤ (A ⧸ torsion ℤ A)) = ⊥ := by
    simp [ker_eq_bot', NeZero.ne, ← natCast_zsmul]
  have coker_card :
      Nat.card ((A ⧸ torsion ℤ A) ⧸ range (l : End ℤ (A ⧸ torsion ℤ A))) = l ^ finrank ℤ A :=
    (index_range_nsmul (M := A ⧸ torsion ℤ A) l).trans
      (by simp [finrank_quotient_eq_of_le_torsion])
  rw [cokerKerIndex_natCast_eq_of_ne_zero _ idx_ne, cokerKerIndex, ker_eq, coker_card]
  simp

/-- On a finitely generated abelian group `A`, multiplication by `l ≠ 0` has finite kernel and
cokernel: its index is nonzero. -/
lemma cokerKerIndex_natCast_ne_zero : cokerKerIndex (l : End ℤ A) ≠ 0 := by
  simp [cokerKerIndex_natCast_eq_pow_finrank, NeZero.ne]

/-- On a finitely generated abelian group `A`, multiplication by `l ≠ 0` has nonzero index
`#(A / l A) / #A[l] = l ^ rank A`: the two clauses are `New.cokerKerIndex_natCast_ne_zero` and
`New.cokerKerIndex_natCast_eq_pow_finrank`. -/
lemma cokerKerIndex_eq_pow_finrank :
    cokerKerIndex (l : End ℤ A) ≠ 0 ∧ cokerKerIndex (l : End ℤ A) = l ^ finrank ℤ A :=
  ⟨cokerKerIndex_natCast_ne_zero, cokerKerIndex_natCast_eq_pow_finrank⟩

variable (l)
  {Δ V Z : Type} [Group Δ] [Fintype Δ] [AddCommGroup V] [MulAction Δ Z] [Fact l.Prime]
  {σ : Representation ℤ Δ V} {τ : V →+ V}

omit [NeZero l] in
/-- Let `L` be a free `ℤ`-module of finite rank with basis `b` and `Δ`-action `ρ`, and `V` an
`𝔽_l`-space (`l` prime) with basis `c` and `Δ`-action `σ`. If `τ` satisfies
`∑ g, σ g ∘ τ ∘ σ g⁻¹ = id` (`hτ`), the averaging operator `π f = ∑ g, σ g ∘ τ ∘ f ∘ ρ g⁻¹` projects
`Hom(L, V)` onto the equivariant maps. So their number is `l ^ m`, with `m` the multiplicity of `1`
as a root modulo `l` of the characteristic polynomial of an integral lift of `π`, built from the
transposed matrices of `ρ g⁻¹` and integral lifts `T g` of the matrices of `σ g ∘ τ`. -/
lemma card_invariants_linHom (hτ : ∀ a : V, ∑ g : Δ, σ g (τ (σ g⁻¹ a)) = a) [Module (ZMod l) V]
    {ι κ L : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [AddCommGroup L]
    (c : Basis κ (ZMod l) V) {T : Δ → Matrix κ κ ℤ}
    (hT : ∀ (g : Δ) (i j : κ), T g i j = c.repr (σ g (τ (c j))) i) (b : Basis ι ℤ L)
    (ρ : Representation ℤ Δ L) :
    Nat.card (linHom ρ σ).invariants =
      Nat.card (ZMod l) ^
        ((∑ g : Δ, (toMatrix b b (ρ g⁻¹))ᵀ.kronecker (T g)).charpoly.map
            (algebraMap ℤ (ZMod l))).rootMultiplicity 1 := by
  -- The matrix of `π` in the basis `e` built from `b` and `c` is the integral lift modulo `l`.
  let π : (L →ₗ[ℤ] V) →ₗ[ZMod l] L →ₗ[ℤ] V :=
    ((∑ g, ρ.linHom σ g) ∘ₗ .compRight ℤ τ.toIntLinearMap).toAddMonoidHom.toZModLinearMap l
  let e : Basis (ι × κ) (ZMod l) (L →ₗ[ℤ] V) :=
    ((Pi.basis fun _ ↦ c).reindex (.sigmaEquivProd ι κ)).map (b.constr (ZMod l))
  have matrix_eq : (∑ g : Δ, (toMatrix b b (ρ g⁻¹))ᵀ.kronecker (T g)).map (algebraMap ℤ (ZMod l)) =
      toMatrix e e π := by
    aesop (add simp Pi.single_apply) (add simp [Matrix.sum_apply, toMatrix_apply])
  have h_finite_hom : Module.Finite (ZMod l) (L →ₗ[ℤ] V) := Module.Finite.of_basis e
  have h_π_fixed (x : L →ₗ[ℤ] V) (hx : x ∈ (linHom ρ σ).invariants) : π x = x := by
    ext y
    simp_all [π, isIntertwiningMap_iff]
  have π_mem (x : L →ₗ[ℤ] V) : π x ∈ (linHom ρ σ).invariants := fun g ↦ self_norm_apply _ g _
  -- If `(π - 1) ^ (k + 1)` kills `x`, then `π x - x` is invariant by induction, hence so is `x`.
  have mem_of_pow (k : ℕ) (x : L →ₗ[ℤ] V)
      (hx : ((π - (1 : ZMod l) • 1 : End (ZMod l) (L →ₗ[ℤ] V)) ^ k) x = 0) :
      x ∈ (linHom ρ σ).invariants := by
    induction k generalizing x with
    | zero => simp_all
    | succ k ih =>
      simpa using sub_mem (π_mem x) (ih (π x - x) (by simpa [pow_succ] using hx))
  -- So the invariants are the generalised eigenspace of `π` for the eigenvalue `1`.
  rw [← charpoly_map, matrix_eq, π.charpoly_toMatrix, ← finrank_maxGenEigenspace_eq,
    ← natCard_eq_pow_finrank]
  congr! 3 with x
  rw [End.mem_maxGenEigenspace]
  exact ⟨fun hx ↦ ⟨1, by simp [h_π_fixed x hx]⟩, fun ⟨k, hk⟩ ↦ mem_of_pow k x hk⟩

omit [AddCommGroup V] [Fact l.Prime] in
/-- Let `Δ` act on the lattice `L` by `ρ` and suppose that some real basis `γ` of `Hom(L, ℝ)` is
permuted as `Δ` permutes `Z`. For integral matrices `T g`, the sum of the Kronecker products of
the transposed matrices of `ρ g⁻¹` with `T g` then has the same characteristic polynomial as the
same sum for the permutation representation on `ℤ[Z]`. -/
private lemma charpoly_sum_kronecker_eq_of_perm {ι κ L : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype Z] [DecidableEq Z] [AddCommGroup L] (b : Basis ι ℤ L)
    (ρ : Representation ℤ Δ L) (γ : Basis Z ℝ (L →ₗ[ℤ] ℝ))
    (hγ : ∀ (g : Δ) (z : Z), (ρ g⁻¹).lcomp ℝ ℝ (γ z) = γ (g • z)) (T : Δ → Matrix κ κ ℤ) :
    (∑ g : Δ, (toMatrix b b (ρ g⁻¹))ᵀ.kronecker (T g)).charpoly =
      (∑ g : Δ, (toMatrix (MonoidAlgebra.basis Z ℤ) (MonoidAlgebra.basis Z ℤ)
        (ofMulAction ℤ Δ Z g⁻¹))ᵀ.kronecker (T g)).charpoly := by
  -- Both are matrices of one real operator `Φ`, taking on the first tensor factor the basis dual
  -- to `b` or the basis `γ`.
  let Φ : Module.End ℝ (TensorProduct ℝ (L →ₗ[ℤ] ℝ) (κ → ℝ)) :=
    ∑ g, TensorProduct.map (lcomp ℝ ℝ (ρ g⁻¹)) (toLin' ((T g).map (algebraMap ℤ ℝ)))
  simp_rw [← (Polynomial.map_injective _ (algebraMap ℤ ℝ).injective_int).eq_iff, ← charpoly_map]
  let e_b := ((Pi.basisFun ℝ ι).map (b.constr ℝ)).tensorProduct (Pi.basisFun ℝ κ)
  let e_γ := γ.tensorProduct (Pi.basisFun ℝ κ)
  have h_mat_b : (∑ g, (toMatrix b b (ρ g⁻¹))ᵀ.kronecker (T g)).map (algebraMap ℤ ℝ) =
      toMatrix e_b e_b Φ := by
    ext ⟨⟩ ⟨⟩
    simp [e_b, Φ, Pi.single_apply, mul_comm, Matrix.sum_apply, toMatrix_apply]
  have h_mat_γ : (∑ g, (toMatrix (MonoidAlgebra.basis Z ℤ) (MonoidAlgebra.basis Z ℤ)
      (ofMulAction ℤ Δ Z g⁻¹))ᵀ.kronecker (T g)).map (algebraMap ℤ ℝ) = toMatrix e_γ e_γ Φ := by
    ext ⟨⟩ ⟨⟩
    simp [e_γ, Φ, mul_comm, hγ, basis, Finsupp.single_apply, eq_inv_smul_iff, eq_comm,
      Matrix.sum_apply, toMatrix_apply]
  have : Module.Finite ℝ (L →ₗ[ℤ] ℝ) := Module.Finite.of_basis γ
  rw [h_mat_b, h_mat_γ, Φ.charpoly_toMatrix, Φ.charpoly_toMatrix]

/-- Let the finite `𝔽_l[Δ]`-module `V` be projective in Higman's sense: some additive `τ` has
`∑ g, g τ g⁻¹ = 1`. Let `A` be a finitely generated `ℤ[Δ]`-module of rank at most `#Z` with real
linear forms `Λ z` that are linearly independent over `ℝ` and permuted by `Δ` as `Z` is. Then there
are as many equivariant maps `A → V` that kill torsion as equivariant maps `Z → V`. The proof lifts
the averaging projector to an integral matrix and reads its characteristic polynomial over `ℝ`. -/
lemma card_hom_lattice_eq_card_equivariant [Finite V] (hτ : ∀ a : V, ∑ g : Δ, σ g (τ (σ g⁻¹ a)) = a)
    [Module (ZMod l) V] {ρ : Representation ℤ Δ A} {Λ : Z → A →ₗ[ℤ] ℝ}
    (hΛ : ∀ (g : Δ) (z : Z) (y : A), Λ z (ρ g⁻¹ y) = Λ (g • z) y) (h_indep : LinearIndependent ℝ Λ)
    (h_rank : finrank ℤ A ≤ Nat.card Z) :
    Nat.card {f : IntertwiningMap ρ σ // torsion ℤ A ≤ ker f.toLinearMap} =
      Nat.card {F : Z → V // ∀ (g : Δ) (z : Z), F (g • z) = σ g (F z)} := by
  classical
  -- Both sides count invariants of `Hom(L, V)`, for `L = A / torsion` and for `L = ℤ[Z]`. The two
  -- integral matrices of `card_invariants_linHom` become conjugate over `ℝ`.
  let c := finBasis (ZMod l) V
  let T (g : Δ) : Matrix (Fin (finrank (ZMod l) V)) (Fin (finrank (ZMod l) V)) ℤ :=
    of fun i j ↦ (c.repr (σ g (τ (c j))) i).val
  have hT (g : Δ) (i j : Fin (finrank (ZMod l) V)) : T g i j = c.repr (σ g (τ (c j))) i := by
    simp [T]
  -- `ρ` keeps torsion, and the forms `Λ z` kill it, as `ℝ` has no torsion.
  have h_smul_zero (g : Δ) (x : A) : ∀ a : nonZeroDivisors ℤ, a • x = 0 → a • ρ g x = 0 := by
    simp_all [← map_smul]
  have h_torsion_ker (z : Z) : torsion ℤ A ≤ (Λ z).ker := by
    rintro y ⟨a, h_smul⟩
    simpa [Submonoid.smul_def] using congrArg (Λ z) h_smul
  let ρ' : Representation ℤ Δ (A ⧸ torsion ℤ A) :=
    ρ.quotient (torsion ℤ A) fun g x ↦ Exists.imp (h_smul_zero g x)
  -- So the forms `Λ z` descend to independent forms on `A / torsion`.
  let Λ' (z : Z) : A ⧸ torsion ℤ A →ₗ[ℤ] ℝ := liftQ _ (Λ z) (h_torsion_ker z)
  have indep : LinearIndependent ℝ Λ' := h_indep.of_comp (lcomp ℝ ℝ (mkQ _))
  have h_finite_Z : Finite Z := indep.finite
  -- By `h_rank` they are a basis `γ` of `Hom(A / torsion, ℝ)`, and `Δ` permutes it as it does `Z`.
  let γ : Basis Z ℝ (A ⧸ torsion ℤ A →ₗ[ℤ] ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank' Λ' indep (indep.fintype_card_le_finrank.antisymm
      (by simp_all [finrank_linearMap, finrank_quotient_eq_of_le_torsion]))
  have γ_perm (g : Δ) (z : Z) : (ρ' g⁻¹).lcomp ℝ ℝ (γ z) = γ (g • z) := by
    -- On the class of `y : A` both sides are `Λ z (ρ g⁻¹ y) = Λ (g • z) y`.
    ext y
    have h_ρ'_mk : ρ' g⁻¹ (Submodule.Quotient.mk y) = Submodule.Quotient.mk (ρ g⁻¹ y) := rfl
    simpa [γ, Λ', h_ρ'_mk] using hΛ g z y
  let b := finBasis ℤ (A ⧸ torsion ℤ A)
  let b₀ := MonoidAlgebra.basis Z ℤ
  let ρ₀ : Representation ℤ Δ (MonoidAlgebra ℤ Z) := ofMulAction ℤ Δ Z
  -- An equivariant map on `A` that kills the torsion is an equivariant map on `A / torsion`.
  let descend :
      {f : IntertwiningMap ρ σ // torsion ℤ A ≤ ker f.toLinearMap} ≃ IntertwiningMap ρ' σ :=
    { toFun f := ⟨liftQ (torsion ℤ A) f.val.toLinearMap f.property,
        fun g ↦ linearMap_qext _ (f.val.isIntertwining' g)⟩
      invFun x := ⟨x.comp ⟨mkQ (torsion ℤ A), fun _ ↦ rfl⟩, le_comap_mkQ _ x.toLinearMap.ker⟩ }
  calc
    _ = Nat.card (linHom ρ' σ).invariants :=
      card_congr (descend.trans (invariantsEquivIntertwiningMap ρ' σ).symm.toEquiv)
    _ = Nat.card (linHom ρ₀ σ).invariants := by
      rw [card_invariants_linHom l hτ c hT b, card_invariants_linHom l hτ c hT b₀,
        charpoly_sum_kronecker_eq_of_perm b ρ' γ γ_perm T]
    -- An equivariant map on `ℤ[Z]` is given by its values on the basis `Z`.
    _ = Nat.card {F : Z → V // ∀ (g : Δ) (z : Z), F (g • z) = σ g (F z)} := by
      refine card_congr ((b₀.constr ℕ).symm.subtypeEquiv fun F ↦ ?_)
      -- Invariance under every `g⁻¹`, read on the basis, is equivariance of the values.
      refine inv_surjective.forall.trans ?_
      simp [b₀, ρ₀, MonoidAlgebra.lhom_ext'_iff, LinearMap.ext_ring_iff, inv_apply_eq_iff]

end New

/-! ## Tate's index formula for a cyclic action of prime order -/

section TateIndex

open LinearMap Module End Polynomial Function GeneralLinearGroup IsCyclotomicExtension

/-- Tate's index formula. Let `l` be prime, let `σ ^ l = 1` on `B`, let the sequence
`C → B → B → C` with maps `j`, `σ - 1`, `s` be exact with `j` injective, and let `s ∘ j = l`. So
`C` is the group of fixed points of `σ`, and `s` plays the role of the norm. With
`q_A = #(A/lA) / #A[l]` (`cokerKerIndex` of `l`) and `q_C ≠ 0`, one has
`[C : s B] ^ (l - 1) * q_B = q_C ^ l`. -/
lemma New.Tate.index_formula {B C : Type} [AddCommGroup B] [AddCommGroup C] (s : B →ₗ[ℤ] C)
    (j : C →ₗ[ℤ] B) {l : ℕ} [Fact l.Prime] (σ : End ℤ B) (hC : cokerKerIndex (l : End ℤ C) ≠ 0)
    (hσ : σ ^ l = 1) (hj : Function.Injective j) (exact_j : Exact j ⇑(σ - 1))
    (exact_s : Exact ⇑(σ - 1) s) (hsj : s ∘ₗ j = l) :
    s.range.cardQuot ^ (l - 1) * cokerKerIndex (l : End ℤ B) = cokerKerIndex (l : End ℤ C) ^ l := by
  -- Let `t` be `σ - 1` acting on `N = (σ - 1) B = ker s`. Then `q_C = [C : s B] * cokerKerIndex t`,
  -- and `q_N = cokerKerIndex t ^ (l - 1)` since `l` is `t ^ (l - 1)` times a unit on `N`; finally
  -- `q_B = q_C * q_N` along `0 → C → B → N → 0`.
  let N : Submodule ℤ B := (σ - 1).range
  let σN : End ℤ N := σ.restrict (show ∀ x ∈ N, σ x ∈ N by simp [N])
  let t : End ℤ N := (σ - 1).rangeRestrict ∘ₗ N.subtype
  obtain ⟨ζ, hζ⟩ : ∃ ζ : cycloField l, IsPrimitiveRoot ζ l := ⟨_, zeta_spec l ℚ _⟩
  -- `1 + σ + ⋯ + σ ^ (l - 1)` kills `N`, as its product with `σ - 1` is `σ ^ l - 1 = 0`. This is
  -- the minimal polynomial of `ζ`, so `N` is a `ℤ[ζ]`-module with `ζ` acting as `σ`.
  have minpoly_eq : cyclotomic l ℤ = minpoly ℤ hζ.toInteger := by
    rw [cyclotomic_eq_minpoly hζ Fin.pos', ← hζ.toInteger.minpoly_coe]
    exact congrArg (minpoly ℤ) hζ.coe_toInteger.symm
  have minpoly_kills : aeval σN (minpoly ℤ hζ.integralPowerBasis.gen) = 0 := by
    ext ⟨_, x, hx⟩
    simpa [σN, ← minpoly_eq, cyclotomic_prime, hσ, ← hx, pow_restrict _ _] using
      LinearMap.congr_fun (geom_sum_mul σ l) x
  -- In `ℤ[ζ]`, `l` is associated to `(ζ - 1) ^ (l - 1)`; transport this to `End ℤ N`.
  obtain ⟨u, hu⟩ : ∃ u : (End ℤ N)ˣ, t ^ (l - 1) * u = l := by
    rw [show t = σN - 1 by ext; simp [σN, t]]
    simpa [Associated, ← IsPrimitiveRoot.integralPowerBasis_gen] using
      (Rat.associated_zeta_sub_one_pow_prime _ hζ).map
        (hζ.integralPowerBasis.lift σN minpoly_kills)
  -- Both `cokerKerIndex (s ∘ₗ j)` and `cokerKerIndex t` unfold, by `cokerKerIndex_comp`, to the
  -- index of `ker (σ - 1) + N` in `B` over the order of `ker (σ - 1) ∩ N`; the first has the extra
  -- factor `[C : s B]`.
  have index_C : cokerKerIndex (l : End ℤ C) = s.range.cardQuot * cokerKerIndex t := by
    rw [← hsj, (cokerKerIndex_comp j s).left,
      (cokerKerIndex_comp N.subtype (σ - 1).rangeRestrict).left]
    simp [N, ker_eq_bot.mpr hj, exact_iff.mp exact_j, exact_iff.mp exact_s, sup_comm, inf_comm]
  have ht : cokerKerIndex t ≠ 0 := right_ne_zero_of_mul (by rwa [← index_C])
  -- The index is multiplicative once one factor is nonzero, and a unit has index `1`.
  have index_pow_mul (m : ℕ) : cokerKerIndex (t ^ m * (u : End ℤ N)) = cokerKerIndex t ^ m := by
    induction m with
    | zero =>
      have hu_eq : (u : End ℤ N) = (toLinearEquiv u).toLinearMap := rfl
      simp [cokerKerIndex, hu_eq]
    | succ m ih =>
      rw [pow_succ', mul_assoc, Module.End.mul_eq_comp,
        (cokerKerIndex_comp (t ^ m * (u : End ℤ N)) t).right (.inr ht), ih, pow_succ]
  have index_N : cokerKerIndex (l : End ℤ N) = cokerKerIndex t ^ (l - 1) := by
    rw [← hu, index_pow_mul]
  have index_B :
      cokerKerIndex (l : End ℤ B) = cokerKerIndex (l : End ℤ C) * cokerKerIndex (l : End ℤ N) :=
    cokerKerIndex_mul_of_exact j _ hj (by simpa [exact_iff] using exact_j)
      (σ - 1).surjective_rangeRestrict hC
  rw [index_B, index_N, mul_left_comm, ← mul_pow, ← index_C, mul_pow_sub_one NeZero.out]

end TateIndex

/-! ## Tate's index formula for the norm in an extension of prime degree -/

section TateNormIndex

open Module Algebra MonoidHom Units Set IsGalois groupCohomology

/-- Tate's index formula for the norm `N` of a Galois extension `L / K` of prime degree `l`.
Let `U ≤ Lˣ` be Galois-stable, `V = U ∩ Kˣ`, and suppose that every Galois-fixed class of
`Lˣ / U` comes from `Kˣ` (by Hilbert 90 this says `H¹(Gal(L/K), U) = 0`). With
`q_A = #(A / A ^ l) / #A[l]` and `q_V ≠ 0`, one has `[V : N U] ^ (l - 1) * q_U = q_V ^ l`. -/
lemma New.tate_index_formula_norm {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (l : ℕ) (hL : finrank K L = l) [Fact l.Prime]
    (U : Subgroup Lˣ) (V : Subgroup Kˣ) (hV : V = U.comap (Units.map (algebraMap K L)))
    (hU : ∀ g : Gal(L/K), ∀ y ∈ U, g • y ∈ U)
    (hH1 : ∀ z : Lˣ, (∀ g : Gal(L/K), g • z / z ∈ U) → ∃ x : Kˣ, x.map (algebraMap K L) / z ∈ U)
    (hqV : cokerKerIndex (l : End ℤ (Additive V)) ≠ 0) :
    (U.map (Units.map (Algebra.norm K))).relIndex V ^ (l - 1) *
        cokerKerIndex (l : End ℤ (Additive U)) =
      cokerKerIndex (l : End ℤ (Additive V)) ^ l := by
  -- Apply `Tate.index_formula` to `B = U`, `C = V` (written additively), a generator `g` of the
  -- Galois group, the inclusion `j : V → U` and the norm `N : U → V`.
  subst hL hV
  have cyc : IsCyclic Gal(L/K) := isCyclic_of_prime_card (card_aut_eq_finrank K L)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let σ : Gal(L/K) →* End ℤ (Additive U) :=
    unitsRep.subrepresentation U.toAddSubgroup.toIntSubmodule hU
  set V : Subgroup Kˣ := U.comap (map (algebraMap K L : K →* L))
  let val (v : Additive U) : L := (((Additive.toMul v : U) : Lˣ) : L)
  -- The norm of `y ∈ U` is the product of its conjugates, so it lies in `U ∩ Kˣ = V`.
  have norm_mem : ((Units.map (norm K : L →* K)).domRestrict U).range ≤ V := by
    rintro _ ⟨y, rfl⟩
    refine Subgroup.mem_comap.mpr <|
      mem_of_eq_of_mem ?_ (U.prod_mem (t := .univ) fun g _ ↦ hU g _ y.property)
    simp [Units.ext_iff, norm_eq_prod_automorphisms]
  -- The relative index is the index in `V` of the range of the norm `N : U → V`.
  rw [Subgroup.relIndex, ← domRestrict_range, subgroupOf_range_eq_of_le _ norm_mem]
  let N : U →* V := codRestrict _ V fun y ↦ norm_mem ⟨y, rfl⟩
  let j : V →* U := subgroupComap _ U
  have pow_eq_one : σ g ^ finrank K L = 1 := by simp [← card_aut_eq_finrank, ← map_pow]
  have j_inj : Function.Injective j.toAdditive.toIntLinearMap :=
    .restrictPreimage _ (map_injective (algebraMap K L).injective)
  -- An element of `U` is fixed by `g`, hence by the whole group, iff it comes from `K`.
  have exact_j : Function.Exact j.toAdditive.toIntLinearMap ⇑(σ g - 1) := by
    refine fun y ↦ sub_eq_zero.trans ⟨fun hy ↦ ?_, ?_⟩
    · -- `y` is fixed by `g`, hence by the whole group, so it comes from `Kˣ`.
      have h_fixed_g : g • val y = val y := congrArg val hy
      obtain ⟨x, hx⟩ := (DiscreteUnits.ofBase_bijective (Γ := Gal(L/K)) (K := K)).surjective
        ⟨((Additive.toMul y : U) : Lˣ),
          fun g' ↦ ext (smul_eq_self_of_mem_zpowers (hg g') h_fixed_g)⟩
      exact (range_restrictPreimage ..).ge ⟨x, Subtype.ext_iff.mp hx⟩
    · rintro ⟨x, rfl⟩
      exact Subtype.ext (ext (g.commutes _))
  -- The kernel of the norm on `U` consists of the `g • w / w` with `w ∈ U`.
  have exact_N : Function.Exact ⇑(σ g - 1) N.toAdditive.toIntLinearMap := by
    refine .of_comp_of_mem_range ?_ fun y hy ↦ ?_
    · -- `g • w` and `w` have the same norm
      ext x
      have h_σ_apply : val (σ g x) = g (val x) := rfl
      simp only [val] at h_σ_apply
      simp [N, field, h_σ_apply, norm_eq_of_algEquiv]
    · -- By Hilbert 90, `y = z / g z` with `z ∈ Lˣ`. So the class of `z` in `Lˣ / U` is fixed by
      -- `g`, hence by the whole group, and `hH1` gives `x ∈ Kˣ` with `w = x / z ∈ U`; then
      -- `g • w / w = z / g z = y`.
      have h_norm_one : Algebra.norm K (val y) = 1 :=
        congrArg (fun v : Additive V ↦ (((Additive.toMul v : V) : Kˣ) : K)) hy
      obtain ⟨z, hz⟩ : ∃ z : Lˣ, (z : L) / g z = val y :=
        exists_div_of_norm_eq_one hg (x := ((Additive.toMul y : U) : Lˣ)) h_norm_one
      let ρq : Representation ℤ Gal(L/K) (DiscreteUnits L ⧸ U.toAddSubgroup.toIntSubmodule) :=
        (unitsRep (Γ := Gal(L/K))).quotient U.toAddSubgroup.toIntSubmodule hU
      have fixed_g : ρq g ⟦.ofMul z⟧ = ⟦.ofMul z⟧ := by
        refine ((Submodule.Quotient.eq _).mpr (mem_of_eq_of_mem ?_ y.property)).symm
        ext
        simpa
      obtain ⟨x, hx⟩ : ∃ x : Kˣ, x.map (algebraMap K L) / z ∈ U :=
        hH1 z fun g' ↦ (Submodule.Quotient.eq _).mp
          ((ρq.mem_invariants_iff_of_forall_mem_zpowers g hg _).mpr fixed_g g')
      refine ⟨.ofMul ⟨_, hx⟩, Subtype.ext (Units.ext ?_)⟩
      -- With `a` the image of `x`, `(σ g - 1) w` is `g • w / w` in `Lˣ` for `w = a / z`.
      let w : Lˣ := x.map (algebraMap K L) / z
      change ((g • w / w : Lˣ) : L) = val y
      rw [← hz]
      simp [w, field]
  have norm_incl : N.toAdditive.toIntLinearMap ∘ₗ j.toAdditive.toIntLinearMap = finrank K L :=
    LinearMap.ext fun _ ↦ Subtype.ext (Units.ext (Algebra.norm_algebraMap _))
  exact Tate.index_formula N.toAdditive.toIntLinearMap j.toAdditive.toIntLinearMap (σ g) hqV
    pow_eq_one j_inj exact_j exact_N norm_incl

end TateNormIndex
end
end

section
section
/-!
# Index of l-th powers in a local field and finiteness of Kummer 1-cocycles

Let `L` be a local field with ring of integers `O`. `New.IsLocalGalois Γ L A` makes `Γ` the absolute
Galois group of `L`, acting on an algebraic closure `Ω` and stabilising its valuation ring `A`; then
`O = A ∩ L` is `New.valRingBelow L A`, a discrete valuation ring with finite residue field. Absolute
values `|x|` are the multiplicative valuation `A.valuation x`. This file counts the `l`-th power
classes in `Lˣ` and deduces the number of continuous 1-cocycles `Γ → Ωˣ` killed by `n`.

## Main definitions and results

* `New.cokerKerIndex_local_units`: `#(Lˣ / Lˣ ^ l) / #μ_l(L) = l · #(O / l)`.
* `New.IsLocalGalois.card_kummer_cocycles`: there are `n² · #(O / n)` continuous 1-cocycles
  `Γ → Ωˣ` killed by `n`; `New.IsLocalGalois.card_ker_natCast_Z1_unitsModule` and
  `New.IsLocalGalois.finite_ker_natCast_Z1_unitsModule` state the count and the finiteness apart.
* `New.IsLocalGalois.finite_Z1`: a finite discrete `Γ`-module has finitely many continuous
  1-cocycles.

Notions from other files:
* `New.cokerKerIndex`: `#coker / #ker` of a linear map, a rational number that is `0` if either
  group is infinite.
* `New.DiscreteModule`: a discrete `Γ`-module over `R`: an `R`-module with the discrete topology
  and a continuous `R`-linear action of the topological group `Γ`.
* `New.Z1 ρ`: the continuous 1-cocycles of the representation `ρ`; `New.unitsModule Γ` is `Ωˣ`,
  written additively, as a discrete `Γ`-module.

## Relation to the literature

Known; see `Lib.ClassField.LocalDuality.CrystallineDuality` for sources.
-/

@[expose] public section

/-!
## The index of l-th powers in the multiplicative group

It rests on a form of Hensel's lemma for l-th roots, proved first in the algebraic closure and then
descended by Galois invariance.
-/

section LocalPowerIndex

open Ideal Quotient Nat Polynomial Valuation IsLocalRing Function.Exact Module LinearMap

/-- Let `A` be a valuation subring of an algebraically closed field `Ω`, with absolute value
`|x| = A.valuation x`. If `r ≠ 0` and `|a - 1| ≤ |l| r`, then `a` has an `l`-th root `z` with
`|z - 1| ≤ r`. -/
lemma New.exists_root_near_one {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
    {l : ℕ} {a : Ω} {r : A.ValueGroup} (hr : r ≠ 0) (ha : A.valuation (a - 1) ≤ A.valuation l * r) :
    ∃ z : Ω, a = z ^ l ∧ A.valuation (z - 1) ≤ r := by
  by_contra! far
  have ha_ne : a ≠ 1 := by simpa using far 1
  -- The logarithmic derivative of `a - X ^ l` at `1` is `-l / (a - 1) = ∑ z, 1 / (1 - z)`, the sum
  -- over the roots. If all roots are far from `1`, every term has valuation `< r⁻¹`.
  let P : Polynomial Ω := C a - X ^ l
  have log_deriv : P.derivative.eval 1 / P.eval 1 = (P.roots.map fun z : Ω ↦ 1 / (1 - z)).sum :=
    (IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero (by simp [P, sub_eq_zero, ha_ne])
  have small : P.derivative.eval 1 / P.eval 1 ∈ A.valuation.ltAddSubgroup (Units.mk0 r hr)⁻¹ := by
    rw [log_deriv]
    -- Each root `z` of `P` is far from `1`, so `|1 / (1 - z)| < r⁻¹`.
    refine AddSubgroup.multiset_sum_mem _ _ fun t ht ↦ ?_
    obtain ⟨z, hz_root, rfl⟩ := Multiset.mem_map.mp ht
    have h_far : r < A.valuation (z - 1) :=
      far z (by simpa [P, sub_eq_zero] using (mem_roots'.mp hz_root).2)
    simp [inv_strictAnti₀, map_sub_swap, pos_iff_ne_zero, h_far, hr]
  -- As `P' 1 / P 1 = -l / (a - 1)`, this says `|l| r < |a - 1|`.
  have h_lt : A.valuation (l : Ω) * r < A.valuation (a - 1) := by
    simpa [P, derivative_pow, field, ha_ne, lt_div_iff₀ (pos_iff_ne_zero.mpr hr), pos_iff,
      sub_eq_zero] using small
  exact ha.not_gt h_lt

/-- Hensel's lemma for `l`-th roots in a local field `L` with absolute Galois group `Γ`
(`New.IsLocalGalois Γ L A`), where `|x| = A.valuation x`: if `0 < r < |l|` and `|a - 1| ≤ |l| r`,
then `a = x ^ l` for some `x` in `L` with `|x - 1| ≤ r`. -/
lemma New.exists_local_root_near_one (Γ : Type*) {L Ω : Type} [Group Γ] [TopologicalSpace Γ]
    [Field L] [Field Ω] [Algebra L Ω] [MulSemiringAction Γ Ω] (A : ValuationSubring Ω)
    [hLocal : IsLocalGalois Γ L A] {l : ℕ} {a : L} {r : A.ValueGroup} (hr : r ≠ 0)
    (hr_lt : r < A.valuation l) (ha : A.valuation (algebraMap L Ω a - 1) ≤ A.valuation l * r) :
    ∃ x : L, a = x ^ l ∧ A.valuation (algebraMap L Ω x - 1) ≤ r := by
  have h_alg_closed : IsAlgClosed Ω := hLocal.toIsAlgClosed
  obtain ⟨z, hz_pow, hz⟩ := exists_root_near_one A hr ha
  have val_z : A.valuation z = 1 := by
    simpa using map_eq_of_sub_lt _ ((hz.trans_lt hr_lt).trans_le (by simp))
  have hz_ne : z ≠ 0 := by simp [← A.valuation.zero_iff, val_z]
  -- `g • z / z` is an `l`-th root of unity closer to `1` than `|l|`, so it is `1`.
  have h_fixed : ∀ g : Γ, g • z = z := by
    intro g
    have h_smul : A.valuation (g • (z - 1)) ≤ r :=
      (decompGroup.val_smul (hLocal.mem_decompGroup g) _).trans_le hz
    have h_close : A.valuation (g • z / z - 1) < A.valuation l := by
      simpa [val_z, hz_ne, smul_sub, div_sub_one] using (map_sub_le _ h_smul hz).trans_lt hr_lt
    have h_ratio_pow : (g • z / z) ^ l = 1 := by
      rw [div_pow, ← smul_pow', show g • z ^ l = z ^ l by simp [← hz_pow],
        div_self (pow_ne_zero _ hz_ne)]
    exact eq_of_div_eq_one (eq_of_pow_eq_one_of_val_sub_lt h_ratio_pow (one_pow l) h_close)
  obtain ⟨x, rfl⟩ : ∃ a : L, algebraMap L Ω a = z := hLocal.isInvariant.isInvariant z h_fixed
  exact ⟨x, (algebraMap L Ω).injective (by simp [hz_pow]), hz⟩

/-- In a local field `L` with absolute Galois group `Γ` (`New.IsLocalGalois Γ L A`), the quotient of
the integers `O = New.valRingBelow L A` by a nonzero principal ideal is finite. -/
lemma New.IsLocalGalois.finite_quotient_span_singleton {Γ L Ω : Type} [Group Γ]
    [TopologicalSpace Γ] [Field L] [Field Ω] [Algebra L Ω] [MulSemiringAction Γ Ω]
    {A : ValuationSubring Ω} (hLocal : IsLocalGalois Γ L A) {x : valRingBelow L A} (hx : x ≠ 0) :
    Finite (valRingBelow L A ⧸ span {x}) := by
  have h_dvr : IsDiscreteValuationRing (valRingBelow L A) := hLocal.isDiscreteValuationRing
  have h_residue : Finite (ResidueField (valRingBelow L A)) := hLocal.finite_residue
  -- The ideal is a power of the maximal ideal, whose quotient is finite.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, span {x} = maximalIdeal (valRingBelow L A) ^ k :=
    exists_maximalIdeal_pow_eq_of_principal _ inferInstance (span {x})
      (span_singleton_eq_bot.ne.mpr hx)
  exact finite_quotient_iff.mpr ⟨k, hk.ge⟩

/-- Let `A` be a valuation subring of `Ω` and `L → Ω` a field embedding. An `l`-th root of unity
`u` in `L` with `|u - 1| < |l|` (for the valuation of `A`) is `1`. -/
lemma New.eq_one_of_pow_eq_one_of_valuation_sub_lt {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω]
    {A : ValuationSubring Ω} {l : ℕ} {u : L} (h_pow : u ^ l = 1)
    (h_close : A.valuation (algebraMap L Ω u - 1) < A.valuation l) : u = 1 := by
  simpa using eq_of_pow_eq_one_of_val_sub_lt (x := algebraMap L Ω u)
    (by rw [← map_pow, h_pow, map_one]) (one_pow l) h_close

/-- The order at the maximal ideal as an additive map. Let `L` be a local field
(`New.IsLocalGalois Γ L A`) with absolute value `|x| = A.valuation x`, `π` a uniformiser and `Y` an
additive group isomorphic to `Lˣ` (by `y`). Then some surjective `f : Y → ℤ` has
`|y a| = |π| ^ n` exactly when `f a = n`. -/
lemma New.IsLocalGalois.exists_surjective_ord {Γ L Ω : Type} [Group Γ] [TopologicalSpace Γ]
    [Field L] [Field Ω] [Algebra L Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω}
    (hLocal : IsLocalGalois Γ L A) {π : Lˣ} (hπ : IsUniformizer A π.val) {Y : Type} [AddCommGroup Y]
    (y : Y ≃+ Additive Lˣ) :
    ∃ f : Y →+ ℤ, Function.Surjective f ∧ ∀ (a : Y) (n : ℤ),
      A.valuation.comap (algebraMap L Ω) (y a).toMul = A.valuation.comap (algebraMap L Ω) π ^ n ↔
        f a = n := by
  set w : Valuation L A.ValueGroup := A.valuation.comap (algebraMap L Ω)
  have h_ord_exists : ∀ a : Y, ∃ n : ℤ, w (y a).toMul = w π ^ n :=
    fun a ↦ hπ.exists_valuationVia_eq_zpow hLocal _ (y a).toMul.ne_zero
  choose ord h_ord using h_ord_exists
  have hπ_pos : 0 < w π := by simp [w, pos_iff]
  have ord_eq {a : Y} {n : ℤ} (h_val : w (y a).toMul = w π ^ n) : ord a = n :=
    zpow_right_injective₀ hπ_pos hπ.valuationVia_lt_one.ne ((h_ord a).symm.trans h_val)
  have ord_add (a b : Y) : ord (a + b) = ord a + ord b :=
    ord_eq <| by
      rw [zpow_add₀ hπ_pos.ne', ← h_ord, ← h_ord]
      simp [w]
  refine ⟨AddMonoidHom.mk' ord ord_add, fun n ↦ ?_, fun a n ↦ ⟨ord_eq, ?_⟩⟩
  · -- `f` is onto: `n` is the order of `π ^ n`.
    exact ⟨y.symm (n • .ofMul π), ord_eq (by simp)⟩
  · rintro rfl
    exact h_ord a

/-- The index of `l`-th powers in a field `L`, where `Γ = Gal(Ω/L)` with `Ω` algebraically closed of
characteristic 0 and `O = New.valRingBelow L A` a discrete valuation ring with finite residue field
(`New.IsLocalGalois Γ L A`). Let `l ≠ 0` and let `Y` be an additive group isomorphic to `Lˣ` (by
`y`). For multiplication by `l` on `Y`, the index `#(Y / l Y) / #Y[l]` (a) is not `0`, that is, both
groups are finite; (b) equals `l · #(O / l O)`. -/
lemma New.cokerKerIndex_local_units {Γ L Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field L]
    [Field Ω] [Algebra L Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω}
    (hLocal : IsLocalGalois Γ L A) (l : ℕ) [NeZero l] {Y : Type} [AddCommGroup Y]
    (y : Y ≃+ Additive Lˣ) :
    -- (a) both groups are finite
    cokerKerIndex (l : End ℤ Y) ≠ 0 ∧
    -- (b) the value of the index
    cokerKerIndex (l : End ℤ Y) =
      l * Nat.card (valRingBelow L A ⧸ span {(l : valRingBelow L A)}) := by
  -- The index is multiplicative in `1 → Oˣ → Lˣ → ℤ → 0`, it is `l` on `ℤ`, and `Oˣ` may be
  -- replaced by the subgroup `V = 1 + l π O` of finite index. On `V` the `l`-th power map is
  -- injective, and `a ↦ (a - 1) / (l π)` identifies its cokernel with `O / l`.
  obtain ⟨π, hπ⟩ := hLocal.exists_isUniformizer
  -- The fields of `hLocal` (discrete valuation ring, finite residue field, …) as local instances.
  have h_fields := hLocal
  obtain ⟨⟩ := h_fields
  have h_char : CharZero L := (algebraMap L Ω).charZero
  -- `w` is the absolute value of `L`.
  set w : Valuation L A.ValueGroup := A.valuation.comap (algebraMap L Ω)
  have h_finite_l : Finite (valRingBelow L A ⧸ span {(l : valRingBelow L A)}) :=
    hLocal.finite_quotient_span_singleton (by simpa using NeZero.ne l)
  have lπ_lt : w (l * π) < A.valuation l := by simp [w, hπ.valuationVia_lt_one, pos_iff, NeZero.ne]
  have div_mem {x : L} : x / (l * π) ∈ valRingBelow L A ↔ w x ≤ w (l * π) := by
    simp [div_le_one₀, w, pos_iff, NeZero.ne]
  -- The order `f : Y → ℤ`, whose kernel is the unit group.
  obtain ⟨f₀, f_surj, h_ord⟩ := hLocal.exists_surjective_ord hπ y
  let f := f₀.toIntLinearMap
  have val_ker (a : f.ker) : w (y a).toMul = 1 := by
    simpa [w] using (h_ord a 0).mpr a.property
  -- `V` is the subgroup `1 + l π O` of the unit group.
  let V : Submodule ℤ f.ker :=
    (AddSubgroup.ofSub {a : f.ker | ((y a).toMul.val - 1) / (l * π) ∈ valRingBelow L A}
      ⟨0, by simp⟩ fun a ha b hb ↦ by
        -- As `|b| = 1`, `a / b - 1` has the absolute value of `(a - 1) - (b - 1)`.
        simpa [val_ker, div_mem, ← division_def, ← sub_div, div_sub_one] using
          sub_mem ha.out hb.out).toIntSubmodule
  -- The element `1 + x` of `V`, for `x ∈ l π O`.
  let oneAdd (x : L) (hx : w x ≤ w (l * π)) : V :=
    have h_val : w (1 + x) = 1 := w.map_one_add_of_lt ((hx.trans_lt lπ_lt).trans_le (by simp))
    have h_ne : 1 + x ≠ 0 := fun h_zero ↦ by simp [h_zero] at h_val
    have h_ker : f (y.symm (.ofMul (.mk0 (1 + x) h_ne))) = 0 :=
      (h_ord _ 0).mp (by simpa [w] using h_val)
    ⟨⟨y.symm (.ofMul (.mk0 (1 + x) h_ne)), h_ker⟩, div_mem.mpr (by simp_all)⟩
  -- Reduction modulo `l π` embeds `Oˣ / V` into the finite ring `O / l π`.
  have h_finite_index : Finite (f.ker ⧸ V) := by
    refine (hLocal.finite_quotient_span_singleton (x := l * ⟨π, hπ.valuationVia_lt_one.le⟩)
      (by simpa [Subtype.ext_iff] using NeZero.ne l)).of_injective
      (fun a ↦ mk _ ⟨(y a.out).toMul, (val_ker a.out).le⟩) fun a b hab ↦ ?_
    -- Equal residues mod `l π` of representatives put their quotient in `V`.
    have h_quot : w (((y (a.out - b.out : f.ker)).toMul : L) - 1) ≤ w (l * π) := by
      simpa [mk_span_eq_iff_dvd_sub, dvd_iff_valuationVia_le, val_ker, w, div_sub_one,
        valuationVia] using hab
    exact out_equiv_out.mp (V.quotientRel_def.mpr (div_mem.mpr h_quot))
  -- An `l`-th root of unity closer to `1` than `|l|` is `1`.
  have ker_pow : LinearMap.ker (l : End ℤ V) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun a ha ↦ ?_
    have h_pow : (y a).toMul.val ^ l = 1 := by
      simpa using congrArg (fun v : V ↦ ((y v).toMul : L)) ha
    have h_close : A.valuation (algebraMap L Ω (y a).toMul - 1) < A.valuation l := by
      simpa [w] using (div_mem.mp a.property).trans_lt lπ_lt
    simpa using eq_one_of_pow_eq_one_of_valuation_sub_lt h_pow h_close
  -- `red a` is the class of `(a - 1) / (l π)` in `O / l`; it is additive by `h_defect`.
  have h_defect (s t : L) : (s * t - 1) / (l * π) - ((s - 1) / (l * π) + (t - 1) / (l * π)) =
      l * ((s - 1) / (l * π) * ((t - 1) / (l * π)) * π) := by field
  let red : V →ₗ[ℤ] valRingBelow L A ⧸ span {(l : valRingBelow L A)} :=
    (AddMonoidHom.mk' (fun a : V ↦ mk (span {(l : valRingBelow L A)}) ⟨_, a.property⟩) fun a b ↦ by
      refine mk_span_eq_iff_dvd_sub.mpr
        ⟨⟨_, a.property⟩ * ⟨_, b.property⟩ * ⟨π, hπ.valuationVia_lt_one.le⟩, Subtype.ext ?_⟩
      simpa using h_defect _ _).toIntLinearMap
  have red_surj : Function.Surjective red := by
    refine Quot.ind fun x ↦ ?_
    -- `x` is the image of `1 + x l π`.
    have h_le : w ((x : L) * (l * π)) ≤ w (l * π) := div_mem.mp (by simp [NeZero.ne])
    refine ⟨oneAdd ((x : L) * (l * π)) h_le, congrArg (Ideal.Quotient.mk _) (Subtype.ext ?_)⟩
    simp [oneAdd, NeZero.ne]
  have red_exact : Function.Exact (l : End ℤ V) red := by
    refine .of_comp_of_mem_range ?_ fun a ha ↦ ?_
    · ext
      simpa using mul_eq_zero_of_left (mk_singleton_self _) _
    · -- If `l ∣ (a - 1) / (l π)`, Hensel's lemma gives an `l`-th root of `a` in `V`.
      -- `ha`: `l` divides `(a - 1) / (l π)` in `O`, that is, `|(a - 1) / (l π)| ≤ |l|`.
      have h_near :
          A.valuation (algebraMap L Ω (y a).toMul.val - 1) ≤ A.valuation l * w (l * π) := by
        simpa [w, div_le_iff₀, NeZero.ne, valuationVia, pos_iff] using
          dvd_iff_valuationVia_le.mp ((eq_zero_iff_dvd (l : valRingBelow L A) _).mp ha)
      obtain ⟨x, hx_pow, hx⟩ :=
        exists_local_root_near_one Γ A (by simp [NeZero.ne]) lπ_lt h_near
      refine ⟨oneAdd (x - 1) (by simpa [w] using hx), Subtype.ext (Subtype.ext (y.injective ?_))⟩
      ext
      simp [oneAdd, hx_pow]
  -- Pass from `f.ker` to `V` (the inclusion has finite kernel and cokernel), and read off the
  -- kernel and the cokernel on `V`.
  have idx_units :
      cokerKerIndex (l : End ℤ f.ker) =
        Nat.card (valRingBelow L A ⧸ span {(l : valRingBelow L A)}) := by
    rw [← cokerKerIndex_natCast_eq_of_ne_zero V.subtype (by simp [ne_of_gt, cokerKerIndex]),
      cokerKerIndex, ker_pow, card_congr (red_exact.linearEquivOfSurjective red_surj).toEquiv]
    simp
  -- Split off `ℤ`, where the index is `l`.
  rw [cokerKerIndex_mul_of_exact _ f (by simp) f.exact_subtype_ker_map f_surj
      (by simp [idx_units, ne_of_gt]),
    idx_units, cokerKerIndex_eq_pow_finrank.right]
  simp [mul_comm, NeZero.ne]

end LocalPowerIndex

/-!
## Kummer count and finiteness of continuous 1-cocycles

`New.DiscreteUnits` is Ωˣ written additively, `New.unitsModule` the same as a discrete Γ-module, and
`New.Z1` the module of continuous 1-cocycles.
-/

section LocalFiniteness

open Nat Function HasEnoughRootsOfUnity NeZero LinearMap CommGroup Ideal

namespace New.IsLocalGalois

variable {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] {A : ValuationSubring Ω}

/-- Kummer theory. Assume `New.IsLocalGalois Γ k A`: `Ω` is algebraically closed of characteristic
0, `Γ` is the Galois group of `Ω` over `k` and stabilises the valuation subring `A`, and
`O = New.valRingBelow k A = A ∩ k` is a discrete valuation ring with finite residue field (`k` need
not be complete). For `n ≠ 0`, let `c` be the number of continuous 1-cocycles `Γ → Ωˣ` killed by `n`
(those with values in the `n`-th roots of unity). Then (a) `c > 0`, which says that the group is
finite, since `Nat.card` of an infinite type is `0`; (b) `c = n² · #(O / n O)`.

It is proved from Hilbert 90, the multiplicativity of `New.cokerKerIndex` along
`1 → kˣ → Ωˣ → Z¹ → 1`, and `New.cokerKerIndex_local_units` on `kˣ`, not from Tate's local Euler
characteristic formula; it is a variant of Kummer theory; it counts 1-cocycles rather than
cohomology classes with values in the n-th roots of unity. -/
lemma card_kummer_cocycles [hLocal : IsLocalGalois Γ k A] (n : ℕ) [NeZero n] :
    let c := Nat.card (n : Module.End ℤ (Z1 (unitsModule Γ).ρ)).ker
    -- (a)
    0 < c ∧
    -- (b)
    c = n ^ 2 * Nat.card (valRingBelow k A ⧸ span {(n : valRingBelow k A)}) := by
  -- By Hilbert 90 the sequence `1 → kˣ → Ωˣ → Z¹ → 1` is exact, and the index `#coker / #ker` of
  -- multiplication by `n` is multiplicative in it. On `kˣ`, the group `K` of invariants of `Ωˣ`,
  -- it is `n · #(O / n)`.
  have h_surj : Surjective (unitsModule Γ).coboundary :=
    fun f ↦ (hilbert90_unitsRep f).imp (by aesop)
  let K : Submodule ℤ (DiscreteUnits Ω) := (unitsRep (Γ := Γ) (Ω := Ω)).invariants
  obtain ⟨h_ne, h_units⟩ : cokerKerIndex (n : Module.End ℤ K) ≠ 0 ∧
      cokerKerIndex (n : Module.End ℤ K) =
        n * Nat.card (valRingBelow k A ⧸ span {(n : valRingBelow k A)}) :=
    cokerKerIndex_local_units hLocal n
      (AddEquiv.ofBijective _ (DiscreteUnits.ofBase_bijective Γ)).symm
  -- The invariants are the kernel of the coboundary map `x ↦ (g ↦ g • x - x)`.
  have h_exact : Exact K.subtype (unitsModule Γ).coboundary := by
    simp [K, Exact, funext_iff, Subtype.ext_iff, sub_eq_zero]
  have h_mul :
      cokerKerIndex (n : Module.End ℤ (DiscreteUnits Ω)) =
        cokerKerIndex (n : Module.End ℤ K) *
          cokerKerIndex (n : Module.End ℤ (Z1 (unitsModule Γ).ρ)) :=
    cokerKerIndex_mul_of_exact K.subtype _ K.subtype_injective h_exact h_surj h_ne
  -- `Ωˣ` is divisible, hence so is its quotient `Z¹`; and `Ωˣ` has `n` elements killed by `n`.
  have h_div : Surjective fun x : DiscreteUnits Ω ↦ n • x := fun x ↦ x.exists_nsmul out
  have h_div' : Surjective fun f : Z1 (unitsModule Γ).ρ ↦ n • f :=
    .of_comp (by simpa [comp_def] using h_surj.comp h_div)
  -- The `n`-torsion of `DiscreteUnits Ω` is `rootsOfUnity n Ω` after unfolding.
  rw [h_units, cokerKerIndex, cokerKerIndex, range_eq_top.mpr h_div, range_eq_top.mpr h_div',
    show Nat.card (LinearMap.ker (n : Module.End ℤ (DiscreteUnits Ω))) = n from
      natCard_rootsOfUnity Ω n] at h_mul
  -- What is left is an equation in `ℚ` for `c`, the number of cocycles killed by `n`.
  replace h_mul : (1 : ℚ) / n = n * Nat.card (valRingBelow k A ⧸ span {(n : valRingBelow k A)}) *
      (1 / Nat.card (n : Module.End ℤ (Z1 (unitsModule Γ).ρ)).ker) := by
    simpa [Nat.card_unique] using h_mul
  qify
  grind

/-- Let `k` be a local field with absolute Galois group `Γ` (`New.IsLocalGalois Γ k A`) and let
`n ≠ 0`. The continuous 1-cocycles `Γ → Ωˣ` killed by `n` form a finite group. -/
lemma finite_ker_natCast_Z1_unitsModule [IsLocalGalois Γ k A] (n : ℕ) [NeZero n] :
    Finite (n : Module.End ℤ (Z1 (unitsModule Γ).ρ)).ker :=
  Nat.finite_of_card_ne_zero (card_kummer_cocycles n).left.ne'

/-- Assume `New.IsLocalGalois Γ k A`: `Ω` is algebraically closed of characteristic 0, `Γ` is the
Galois group of `Ω` over `k` and stabilises the valuation subring `A`, and
`O = New.valRingBelow k A = A ∩ k` is a discrete valuation ring with finite residue field (`k` need
not be complete). Then for `n ≠ 0`, the number of continuous 1-cocycles `Γ → Ωˣ` killed by `n` is
`n² · #(O / n O)`. -/
lemma card_ker_natCast_Z1_unitsModule [IsLocalGalois Γ k A] (n : ℕ) [NeZero n] :
    Nat.card (n : Module.End ℤ (Z1 (unitsModule Γ).ρ)).ker =
      n ^ 2 * Nat.card (valRingBelow k A ⧸ span {(n : valRingBelow k A)}) :=
  (card_kummer_cocycles n).right

/-- If `k` is a local field with absolute Galois group `Γ` (`New.IsLocalGalois Γ k A`), then for
every finite discrete `Γ`-module `M` over a commutative ring `R`, the module `Z¹(Γ, M)` of
continuous 1-cocycles is finite.

A case of the finiteness of Galois cohomology of a local field: degree one, in characteristic 0,
stated for continuous 1-cocycles of a finite module rather than for H¹. -/
lemma finite_Z1 [IsLocalGalois Γ k A] ⦃R : Type⦄ [CommRing R] (M : DiscreteModule R Γ)
    [Finite M] : Finite (Z1 M.ρ) := by
  -- Let `U` be an open subgroup acting trivially on `Hom(M, Ωˣ)`. A cocycle `z` is determined by
  -- its values on representatives of `Γ / U` and by the cocycles `f ∘ z` of `U` in `Ωˣ`, for `f`
  -- in `Hom(M, Ωˣ)`. These are killed by `#M`, so Kummer theory over the fixed field of `U`
  -- leaves finitely many of them.
  obtain ⟨⟨U, hU_normal⟩, hU⟩ := exists_openNormalSubgroup_apply_eq M.cartierDual.continuous
  -- On `U` every `f : M →+ DiscreteUnits Ω` is equivariant (`using!`: the action on
  -- `M.cartierDual` in `hU` gives this equation only after unfolding).
  have h_equiv (f : M →+ DiscreteUnits Ω) (u : U.toSubgroup) (x : M) :
      f (M.ρ u x) = unitsRep u.val (f x) := by
    simpa using! congr($(hU _ u.property f) (M.ρ u x)).symm
  -- Over the fixed field of `U` the cocycles killed by `#M` form a finite group.
  let := (of_finite U).isLocalGalois.finite_ker_natCast_Z1_unitsModule (Nat.card M)
  have hz_mul (z : Z1 M.ρ) (g h : Γ) : z.val (g * h) = z.val g + M.ρ g (z.val h) :=
    z.property.right g h
  -- Restrict to `U` and compose with each character of `M`. The resulting cocycles lie in
  -- the finite Kummer kernel, so there is no need to enumerate that kernel.
  let res (z : Z1 M.ρ) (f : M →+ DiscreteUnits Ω) :
      (Nat.card M : Module.End ℤ (Z1 (unitsModule U.toSubgroup).ρ)).ker :=
    ⟨⟨fun u ↦ f (z.val u),
      continuous_of_discreteTopology.comp (z.property.left.comp continuous_subtypeVal),
      fun g g' ↦ by simpa [hz_mul z] using! h_equiv f g _⟩,
      by simp [Subtype.ext_iff, funext_iff, ← map_nsmul]⟩
  refine .of_injective (fun z ↦ (fun q : Γ ⧸ U.toSubgroup ↦ z.val q.out, res z)) fun y z hyz ↦ ?_
  have h_out_eq : (fun q : Γ ⧸ U.1 ↦ y.val q.out) = fun q ↦ z.val q.out := congrArg Prod.fst hyz
  have h_res_eq : res y = res z := congrArg Prod.snd hyz
  ext g
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  -- Characters with values in `Ωˣ` separate the points of `M`, so `y` and `z` agree on `U`.
  have h_res : y.val u = z.val u := by
    refine (CommGroup.forall_apply_eq_apply_iff (Multiplicative M) (M := Ω)).mp fun f ↦ ?_
    exact congrArg (fun c ↦ c.val.val u) (congrFun h_res_eq f.toAdditiveRight)
  -- On the representative `g * u` of the class of `g`, the two cocycles agree.
  have h_rep : y.val (g : Γ ⧸ U.1).out = z.val (g : Γ ⧸ U.1).out := congrFun h_out_eq g
  simpa [hz_mul y, hz_mul z, hu, h_res] using h_rep

end New.IsLocalGalois

end LocalFiniteness
end
end

/-!
# The local invariant Br(k) ≅ Q/Z and its behaviour under restriction and maps of local fields

The invariant map of local class field theory, for a henselian local field `k` of characteristic `0`
with absolute Galois group `Γ` acting on `Ω` (`New.IsLocalGalois`).

* `New.IsLocalGalois.isClassOfInvariant_classOfInvariant`: the chosen map
  `New.Cohomology.classOfInvariant` from ℚ/ℤ to H²(Γ, Ωˣ) is injective and computes the cyclic
  classes of unramified characters.
* `New.IsLocalGalois.classOfInvariant_bijective`: `New.Cohomology.classOfInvariant` is bijective, so
  it identifies ℚ/ℤ with H²(Γ, Ωˣ).
* `New.Cohomology.resH2_classOfInvariant`, `New.IsLocalGalois.exists_resH2_classOfInvariant_eq`:
  restriction to an open subgroup multiplies the invariant by the index and is onto.
* `New.IsLocalGalois.pairMapH2_classOfInvariant_of_ordRat_eq`,
  `New.IsLocalGalois.pairMapH2_classOfInvariant`: a map of local fields with ramification index `e`
  and residue degree `f` multiplies the invariant by `e * f`.

Notions from other files:
* `New.unitsModule`, `New.unitsRep`: `Ωˣ` written additively (`New.DiscreteUnits`) with the action
  of `Γ`, as a discrete module and as a representation; `H0` are its `Γ`-invariants, the units
  of `k`.
* `New.DiscreteModule.resH2`: restriction of a class in `H²(Γ, M)` to a subgroup of `Γ`; a class is
  split by `V` when its restriction to `V` is zero.
* `New.cyclicClass`: the cyclic class (symbol) `(χ, w) = δχ ∪ w` of a character `χ : Γ → ℚ/ℤ` and
  an invariant `w`.

## Relation to the literature

Known; see `Lib.ClassField.Local.ArtinMap` for sources.
-/

@[expose] public section

/-- If `R ^ (l - 1) * (l * c ^ l) = (l * c) ^ l` in `ℚ`, with `l` prime and `l * c ≠ 0`, then
`R = l`. -/
private lemma Nat.eq_of_pow_sub_one_mul_eq_mul_pow {R l c : ℕ} (hl : l.Prime)
    (hlc : (l : ℚ) * c ≠ 0) (h : (R : ℚ) ^ (l - 1) * (l * c ^ l) = ((l : ℚ) * c) ^ l) : R = l := by
  -- Cancel `l * c ^ l`, then take `(l - 1)`-th roots, where `l - 1 ≠ 0`.
  have h_pow : (R : ℚ) ^ (l - 1) = (l : ℚ) ^ (l - 1) := by
    refine mul_right_cancel₀ (b := (l * c ^ l : ℚ))
      (mul_ne_zero (left_ne_zero_of_mul hlc) (pow_ne_zero l (right_ne_zero_of_mul hlc))) ?_
    rw [h, mul_pow, ← mul_assoc, pow_sub_one_mul hl.ne_zero]
  exact Nat.pow_left_injective (Nat.sub_ne_zero_of_lt hl.one_lt) (by exact_mod_cast h_pow)

namespace New.IsLocalGalois

open Cohomology Function DiscreteModule Subgroup QZChar QuotientGroup QZ DiscreteUnits AddMonoidHom

variable {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] (V : OpenSubgroup Γ) {A : ValuationSubring Ω} [L : IsLocalGalois Γ k A]

/-- Let `V` be an open normal subgroup of prime index in `Γ`. If `β ≠ 0` in `H²(Γ, Ωˣ)` is split
by `V` (its restriction to `V` is zero), then every class `x` split by `V` is an integer multiple
of `β`.

This is the case of prime index of `mem_zmultiples_of_resH2_eq_zero`: the classes split by `V` are
the symbols `(ψ, y)` with `ker ψ = V` and `y ∈ kˣ`, and they form a quotient of `kˣ` modulo
norms, a group of prime order `[Γ : V]`. -/
lemma mem_zmultiples_of_index_prime [V.Normal] {β x : (unitsModule Γ).H2} (h_prime : V.index.Prime)
    (hβ : (unitsModule Γ).resH2 V β = 0) (hβ_ne : β ≠ 0) (hx : (unitsModule Γ).resH2 V x = 0) :
    x ∈ AddSubgroup.zmultiples β := by
  -- Write `V = ker ψ`. The symbol map `y ↦ (ψ, y)` sends `kˣ` onto the classes split by `V` and
  -- kills the norms `N`; by Tate's formula `kˣ ⧸ N` has prime order `[Γ : V]`, so the image of
  -- `β ≠ 0` generates.
  have : Fact V.index.Prime := ⟨h_prime⟩
  have h_ext : IsLocalExtension k A (V : Subgroup Γ) (fixedFieldOf (V : Subgroup Γ)) := of_finite V
  obtain ⟨ψ, hψ⟩ := exists_ker_eq_of_isCyclic V (isCyclic_of_prime_card (p := V.index) rfl)
  obtain ⟨V, _⟩ := V
  obtain rfl : QZChar.ker ψ = V := hψ
  -- The split classes are the symbols `(ψ, y)` with `y ∈ kˣ`.
  obtain ⟨y, rfl⟩ := ((cyclicClass_spec ψ).1 β).mp hβ
  obtain ⟨z, rfl⟩ := ((cyclicClass_spec ψ).1 x).mp hx
  -- The symbol map kills the group `N` of norms.
  let N : Subgroup kˣ := map (Units.map (Algebra.norm k : fixedFieldOf (ker ψ) →* k)) ⊤
  let f : kˣ ⧸ N →* Multiplicative (unitsModule Γ).H2 :=
    lift N ((cyclicClass unitsRep ψ).comp (ofBase Γ Ω)).toMultiplicativeRight fun _ ⟨b, _, hb⟩ ↦
      (cyclicClass_eq_zero_iff_norm _).mpr ⟨b, hb⟩
  -- Tate's formula for the norm from `K = fixedFieldOf (ker ψ)` gives `#(kˣ ⧸ N) = [Γ : ker ψ]`.
  have card_eq : Nat.card (kˣ ⧸ N) = (QZChar.ker ψ).index := by
    set l : ℕ := (QZChar.ker ψ).index
    have : NeZero l := ⟨h_prime.ne_zero⟩
    obtain ⟨qk_ne, qk_eq⟩ := cokerKerIndex_local_units L l (topEquiv (G := kˣ)).toAdditive
    have qK_eq := (cokerKerIndex_local_units h_ext.isLocalGalois l
      (topEquiv (G := (fixedFieldOf (ker ψ))ˣ)).toAdditive).2
    rw [h_ext.card_quotient, Nat.cast_pow] at qK_eq
    have tate := tate_index_formula_norm l (finrank_fixedFieldOf (QZChar.ker ψ)) ⊤ ⊤
      (comap_top _).symm (fun _ _ _ ↦ mem_top _) (fun _ _ ↦ ⟨1, mem_top _⟩) qk_ne
    rw [qK_eq, qk_eq, relIndex_top_right] at tate
    exact Nat.eq_of_pow_sub_one_mul_eq_mul_pow h_prime (by rwa [← qk_eq]) tate
  -- So `z` is a power `y ^ m` modulo `N`, and applying `f` gives `(ψ, z) = m • (ψ, y)`.
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (y : kˣ ⧸ N) ^ m = z := mem_zpowers_of_prime_card card_eq
    fun hy ↦ hβ_ne <| ofAdd_eq_one.mp ((congrArg f hy).trans f.map_one)
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨m, Multiplicative.ofAdd.injective <|
    (ofAdd_zsmul _ _).trans <| (f.map_zpow (y : kˣ ⧸ N) m).symm.trans (congrArg f hm)⟩

/-- If the class `β` in `H²(Γ, Ωˣ)` is split by the open normal subgroup `V` (its restriction to
`V` is zero) and is killed only by multiples of `[Γ : V]`, then every class `x` split by `V` is an
integer multiple of `β`. -/
lemma mem_zmultiples_of_resH2_eq_zero [V.Normal] {β x : (unitsModule Γ).H2}
    (hβ : (unitsModule Γ).resH2 V β = 0) (hβ_order : ∀ n : ℕ, n • β = 0 → V.index ∣ n)
    (hx : (unitsModule Γ).resH2 V x = 0) : x ∈ AddSubgroup.zmultiples β := by
  -- Reduce via `mem_of_prime_step` to a single step `V ≤ W ≤ U` with `W` of prime index in `U`,
  -- done over the fixed field of `U`: given a multiple `s` of `β` with `x - s` split by `W`, find
  -- one with `x - s` split by `U`.
  refine mem_of_prime_step _ hx fun U W hW_normal hVU hVW hW_prime s hs hxs ↦ ?_
  -- `V_U` and `V'` are `V` seen inside `U` and `W`. The class `β'` on `U` dies on `W`, because a
  -- class split by an open subgroup is killed by its index (`index_smul_eq_zero_of_resH2`).
  let V_U : OpenSubgroup (U : Subgroup Γ) := V.comap (Subgroup.subtype _) continuous_subtypeVal
  let V' : OpenSubgroup (W : Subgroup U) := V_U.comap (Subgroup.subtype _) continuous_subtypeVal
  let β' : ((unitsModule Γ).restrictTo U).H2 := V'.index • (unitsModule Γ).resH2 U β
  -- `β` restricted to `U` is split by `V_U`, and then by `V'` inside `W`.
  have hβ_U : ((unitsModule Γ).restrictTo U).resH2 V_U ((unitsModule Γ).resH2 U β) = 0 :=
    resH2_subgroupOf_eq_zero_symm (by rw [hβ, map_zero])
  have dies : ((unitsModule Γ).restrictTo U).resH2 W β' = 0 := by
    dsimp only [β']
    rw [map_nsmul]
    exact index_smul_eq_zero_of_resH2 V' (resH2_subgroupOf_eq_zero_symm (by rw [hβ_U, map_zero]))
  have index_eq : V.index = V'.index * U.index * W.index := by
    -- `V'.index` is by definition the relative index of `V` (inside `U`) in `W`.
    change V.index = ((V : Subgroup Γ).subgroupOf U).relIndex W * U.index * W.index
    rw [mul_right_comm, relIndex_mul_index hVW, ← relIndex_mul_index hVU, relIndex]
  -- If `β' = 0`, the proper divisor `V'.index * U.index` of `V.index` kills `β`, against
  -- `hβ_order`.
  have β'_ne : β' ≠ 0 := by
    intro hβ'_zero
    have h_kill : (V'.index * U.index) • β = 0 := by
      rw [mul_nsmul]
      exact index_smul_eq_zero_of_resH2 U (by rwa [map_nsmul])
    have h_pos : 0 < V'.index * U.index :=
      Nat.pos_of_ne_zero (mul_ne_zero index_ne_zero_of_finite index_ne_zero_of_finite)
    refine Nat.not_dvd_of_pos_of_lt h_pos ?_ (hβ_order _ h_kill)
    exact (lt_mul_of_one_lt_right h_pos hW_prime.one_lt).trans_eq index_eq.symm
  -- So on `U` the class `x - s`, which dies on `W`, is a multiple `j • β'`, and
  -- `s + j • V'.index • β` is the multiple of `β` sought.
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j • β' = (unitsModule Γ).resH2 U (x - s) :=
    mem_zmultiples_of_index_prime W (L := (of_finite U).isLocalGalois) hW_prime dies β'_ne hxs
  refine ⟨s + j • V'.index • β,
    add_mem hs (zsmul_mem (nsmul_mem (AddSubgroup.mem_zmultiples β) _) _), ?_⟩
  rw [← sub_sub, map_sub, ← hj, map_zsmul, map_nsmul, sub_self]

/-! ### The class attached to an element of `ℚ/ℤ` -/

/-- Let `Γ = Gal(Ω/k)` with `Ω` algebraically closed of characteristic 0, and let `A` be stable
under `Γ` with `A ∩ k` a discrete valuation ring with finite residue field (`IsLocalGalois Γ k A`).
Then there is an additive map `b : ℚ/ℤ → H²(Γ, Ωˣ)` satisfying `IsClassOfInvariant`. That is, `b` is
injective, and `b` sends `n • χ(φ)` to the cyclic class of `χ` and `w`, whenever `χ` is a continuous
unramified character `Γ → ℚ/ℤ`, `φ` is a Frobenius element, and `w ∈ Ωˣ` is invariant of normalised
order `n`. -/
lemma exists_isClassOfInvariant :
    ∃ b : QZ →+ H2 (unitsRep (Γ := Γ) (Ω := Ω)), IsClassOfInvariant Γ k A b := by
  -- The class of `r` is the cyclic class `(c r, π)`, where `π` is a uniformiser and `c r` is the
  -- unramified character with value `r` at the Frobenius element.
  obtain ⟨π, hπ⟩ : ∃ π : (unitsModule Γ).H0, ordRat k A π.val = 1 :=
    ⟨_, L.exists_isUniformizer.choose_spec.ordRat_eq_one L⟩
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ : Γ, IsFrob A (residueCard k A) φ := L.frobenius_spec.left
  choose c hc c_unique using existsUnique_unramified_char hφ₀
  -- If `(χ, w) = 0` then `w` is a norm from the fixed field of `χ`. For unramified `χ`, the order
  -- of a norm is a sum of `[Γ : ker χ]` equal integers.
  have index_dvd {χ : QZChar Γ} (hχ : inertiaGroup Γ A ≤ QZChar.ker χ) (w : (unitsModule Γ).H0)
      (n : ℤ) (hn : ordRat k A w.val = n) (h : cyclicClass _ χ w = 0) : ↑(ker χ).index ∣ n := by
    obtain ⟨y, hy⟩ := ((cyclicClass_spec χ).right w).mp h
    -- `y` is fixed by inertia, so its order is an integer.
    obtain ⟨j, hj⟩ : ∃ j : ℤ, ordRat k A y.val = j :=
      exists_ordRat_eq_intCast fun g hg ↦ y.property ⟨g, hχ hg⟩
    refine ⟨j, ?_⟩
    qify
    rw [← hn, ← hy]
    dsimp only [corestrictH0, DiscreteModule.sum]
    rw [Representation.IntertwiningMap.coe_mk, LinearMap.sum_apply, map_sum,
      Finset.sum_eq_card_nsmul (b := (j : ℚ))]
    · simp only [Finset.card_univ, Fintype.card_eq_nat_card, nsmul_eq_mul, index]
    · intro x _
      dsimp only [LinearMap.proj_apply]
      simp [← hj, eq_iff, ↓L.ordRat_eq_zero, decompGroup.val_smul, L.mem_decompGroup]
  -- `c` is additive by the uniqueness in `c_unique`.
  have c_add (r s : QZ) : c (r + s) = c r + c s :=
    (c_unique _ _ ⟨fun g hg ↦ by
        change (c r).val g + (c s).val g = 0
        rw [(hc r).1 g hg, (hc s).1 g hg, add_zero],
      by
        change (c r).val φ₀ + (c s).val φ₀ = r + s
        rw [(hc r).2, (hc s).2]⟩).symm
  refine ⟨((cyclicClass _).flip π).comp (.mk' c c_add),
    (injective_iff_map_eq_zero _).mpr fun r h ↦ ?_, fun χ hχ φ hφ w n hn ↦ ?_⟩
  · -- If `(c r, π) = 0`, the kernel of `c r` has index one, so `r = c r φ₀ = 0`.
    have h_index : (ker (c r)).index ∣ 1 := Int.ofNat_dvd.mp (index_dvd (hc r).left π 1 hπ h)
    have h_frob : φ₀ ∈ ker (c r) := (index_eq_one.mp (Nat.dvd_one.mp h_index)).ge (mem_top φ₀)
    exact (hc r).right.symm.trans h_frob
  -- All classes `(χ, w)` are split by `ker χ`, and `(χ, π)` generates the split classes.
  have h_split (w : (unitsModule Γ).H0) :
      (unitsModule Γ).resH2 (ker χ) (cyclicClass _ χ w) = 0 := by
    obtain ⟨y, rfl⟩ := (ofBase_bijective Γ).surjective w
    exact ((cyclicClass_spec χ).left _).mpr ⟨y.toMul, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j • cyclicClass _ χ π = cyclicClass _ χ w :=
    mem_zmultiples_of_resH2_eq_zero ⟨_, isOpen_ker χ⟩ (h_split π)
      (fun n hn ↦ Int.ofNat_dvd.mp (index_dvd hχ (n • π) n
        (by rw [AddSubmonoidClass.coe_nsmul, map_nsmul, hπ, nsmul_eq_mul, mul_one,
          Int.cast_natCast])
        (by rw [map_nsmul]; exact hn)))
      (h_split w)
  -- `j ≡ n` modulo the index, which kills `(χ, π)`.
  have h_ord_diff : ordRat k A (j • π - w).val = (j - n : ℤ) := by
    rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_zsmul, map_sub, map_zsmul, hπ, hn,
      zsmul_eq_mul, mul_one, Int.cast_sub]
  have h_class_diff : cyclicClass _ χ (j • π - w) = 0 := by
    rw [map_sub, map_zsmul, hj, sub_self]
  obtain ⟨i, hi⟩ : ↑(ker χ).index ∣ j - n := index_dvd hχ (j • π - w) _ h_ord_diff h_class_diff
  have χ_eq : χ = c (χ.val φ) := c_unique _ χ
    ⟨hχ, (toHom χ).eq_iff.mpr (hχ _ (hφ.inv_mul_mem_inertiaGroup hφ₀))⟩
  rw [← hj]
  change (j • cyclicClass _ χ π) = n • cyclicClass _ (c (χ.val φ)) π
  rw [← χ_eq, eq_add_of_sub_eq hi, add_zsmul, mul_zsmul', natCast_zsmul,
    index_smul_eq_zero_of_resH2 ⟨_, isOpen_ker χ⟩ (h_split π), zsmul_zero, zero_add]

/-- The chosen map `classOfInvariant` from `ℚ/ℤ` to `H²(Γ, Ωˣ)` is injective, and the cyclic class
of an unramified character `χ` and an invariant `w` of order `n` is
`n • classOfInvariant Γ k A (χ φ)` for a Frobenius `φ`.

This is the normalisation of the invariant map on the Brauer group of a local field in
characteristic 0, expressed through the inverse map and an arithmetic Frobenius. -/
lemma isClassOfInvariant_classOfInvariant : IsClassOfInvariant Γ k A (classOfInvariant Γ k A) :=
  Cohomology.isClassOfInvariant_classOfInvariant_of_exists Γ k A exists_isClassOfInvariant

variable {Γ' k' Ω' : Type} [Group Γ'] [TopologicalSpace Γ'] [Field k'] [Field Ω'] [Algebra k' Ω']
  [MulSemiringAction Γ' Ω'] {A' : ValuationSubring Ω'} [L' : IsLocalGalois Γ' k' A']

/-- Let `k'` be a second local field, with Galois group `Γ'` acting on `Ω'` and valuation ring `A'`,
and let `j : Ω → Ω'` be a field map compatible with `φ : Γ' → Γ` (`hj`) with `A'` pulling back to
`A` (`hA`). Suppose the `Γ`-fixed unit `w` of `Ωˣ` has normalised order `1` over `k` (`hw_ord`),
`j w` has order `e` over `k'` (`he`, so `e` is the ramification index), and the residue field of
`k'` has `q ^ f` elements, where `q` is that of `k` (`hf`). Then the map `H²(Γ, Ωˣ) → H²(Γ', Ω'ˣ)`
induced by `φ` and `j` sends `classOfInvariant Γ k A r`, the class with invariant `r ∈ ℚ/ℤ`, to the
class with invariant `(e * f) • r`. -/
lemma pairMapH2_classOfInvariant_of_ordRat_eq (φ : Γ' →ₜ* Γ) (j : Ω →+* Ω') (hA : A'.comap j = A)
    (hj : ∀ (g : Γ') (x : Ω), j (φ g • x) = g • j x) {e f : ℕ} {w : (unitsModule Γ).H0}
    (hw_ord : ordRat k A w = 1) (he : ordRat k' A' ((Units.map j).toAdditive w.val) = e)
    (hf : residueCard k' A' = residueCard k A ^ f) (r : QZ) :
    (pairMapH2 φ (Units.map j).toAdditive.toIntLinearMap) (classOfInvariant Γ k A r) =
      classOfInvariant Γ' k' A' ((e * f) • r) := by
  -- Write `r = χ σ` with `χ` unramified and `σ` a Frobenius, so the class is the cyclic class
  -- `(χ, w)`. Its image is the cyclic class of `χ ∘ φ` and `j w`; here `j w` has order `e`, and
  -- `χ ∘ φ` takes the value `f • r` on a Frobenius `τ` of `k'`.
  obtain ⟨σ, hσ⟩ : ∃ σ : Γ, IsFrob A (residueCard k A) σ := L.frobenius_spec.left
  obtain ⟨τ, hτ⟩ : ∃ τ : Γ', IsFrob A' (residueCard k' A') τ := L'.frobenius_spec.left
  obtain ⟨χ, χ_unr, rfl⟩ : ∃ χ : QZChar Γ, (∀ g ∈ inertiaGroup Γ A, χ.val g = 0) ∧ χ.val σ = r :=
    (existsUnique_unramified_char hσ r).exists
  subst hA
  let χ' : QZChar Γ' := comap φ χ
  -- The image of `w` in `Ω'ˣ` is fixed by `Γ'`, as `w` is fixed by `Γ` and `j` is compatible.
  let w' : (unitsModule Γ').H0 := ⟨(Units.map (j : Ω →* Ω')).toAdditive w.val, fun g ↦
    Additive.toMul.injective (Units.ext ((hj g w.val.toMul.val).symm.trans
      (congrArg (fun u : DiscreteUnits Ω ↦ j u.toMul.val) (w.property (φ g)))))⟩
  have χ'_unr : ∀ g ∈ inertiaGroup Γ' A', χ'.val g = 0 := fun g hg ↦ χ_unr _ (hg.map hj)
  -- `φ τ` and `σ ^ f` are both Frobenius elements for `residueCard k A ^ f`, so they differ by
  -- inertia.
  have inertia : (σ ^ f)⁻¹ * φ τ ∈ inertiaGroup Γ (A'.comap j) :=
    (hσ.pow f).inv_mul_mem_inertiaGroup (by simpa only [hf] using hτ.map hj)
  have χ'_frob : χ'.val τ = f • χ.val σ :=
    ((toHom χ).eq_iff.mpr (χ_unr _ inertia)).trans (map_pow (toHom χ) σ f)
  have h_cyc : cyclicClass unitsRep χ w = (1 : ℤ) • classOfInvariant Γ k (A'.comap j) (χ.val σ) :=
    isClassOfInvariant_classOfInvariant.right χ χ_unr σ hσ w 1 hw_ord
  have h_cyc' : cyclicClass unitsRep χ' w' = (e : ℤ) • classOfInvariant Γ' k' A' (χ'.val τ) :=
    isClassOfInvariant_classOfInvariant.right χ' χ'_unr τ hτ w' e he
  have h_eq : ∀ (g : Γ') (m : DiscreteUnits Ω),
      (Units.map (j : Ω →* Ω')).toAdditive.toIntLinearMap (unitsRep (φ g) m) =
        unitsRep g ((Units.map (j : Ω →* Ω')).toAdditive.toIntLinearMap m) :=
    fun g m ↦ Additive.toMul.injective (Units.ext (hj g m.toMul.val))
  -- The cocycles of both classes take the values `n • w` and `n • j w` with the same integers.
  have h_map : (pairMapH2 φ (Units.map (j : Ω →* Ω')).toAdditive.toIntLinearMap h_eq)
      (cyclicClass unitsRep χ w) = cyclicClass unitsRep χ' w' :=
    congrArg (Quotient.mk _) (Subtype.ext (funext fun _ ↦ map_zsmul _ _ _))
  rwa [h_cyc, h_cyc', one_zsmul, χ'_frob, natCast_zsmul, ← map_nsmul, ← mul_smul] at h_map

/-- For two local Galois data `Γ, k, A` and `Γ', k', A'`, let `φ : Γ' →ₜ* Γ` be continuous and
`j : Ω →+* Ω'` a ring map with `A'.comap j = A` and `j (φ g • x) = g • j x`. Suppose a `Γ`-invariant
unit `w` of `Ω` has normalised order `1` on `k`, its image under `j` has normalised order `e` on
`k'`, and `residueCard k' A' = residueCard k A ^ f`; then the map `H²(Γ, Ωˣ) → H²(Γ', Ω'ˣ)` induced
by `φ` and `j` sends the class of invariant `r` to the class of invariant `(e * f) • r`. This is the
form of `pairMapH2_classOfInvariant_of_ordRat_eq` with the two conditions on the orders of `w` in
one hypothesis `he`. -/
lemma pairMapH2_classOfInvariant {Γ' k' Ω' : Type} [Group Γ'] [TopologicalSpace Γ'] [Field k']
    [Field Ω'] [Algebra k' Ω'] [MulSemiringAction Γ' Ω'] {A' : ValuationSubring Ω'}
    [L' : IsLocalGalois Γ' k' A'] (φ : Γ' →ₜ* Γ) (j : Ω →+* Ω') (hA : A'.comap j = A)
    (hj : ∀ (g : Γ') (x : Ω), j (φ g • x) = g • j x) {e f : ℕ} {w : (unitsModule Γ).H0}
    (he : ordRat k A w = 1 ∧ ordRat k' A' ((Units.map j).toAdditive w.val) = e)
    (hf : residueCard k' A' = residueCard k A ^ f) (r : QZ) :
    (pairMapH2 φ (Units.map j).toAdditive.toIntLinearMap) (classOfInvariant Γ k A r) =
      classOfInvariant Γ' k' A' ((e * f) • r) :=
  pairMapH2_classOfInvariant_of_ordRat_eq φ j hA hj he.left he.right hf r

/-- Restriction to an open subgroup `V`, the Galois group of `Ω` over the fixed field
`fixedFieldOf V`, sends the class of `r` to the class of `[Γ : V] • r`.

Part of the functoriality of the local invariant: in characteristic 0, restriction to an open
subgroup multiplies the invariant by the degree, expressed through the inverse map ℚ/ℤ → H². -/
lemma _root_.New.Cohomology.resH2_classOfInvariant {r : QZ} :
    (unitsModule Γ).resH2 V (classOfInvariant Γ k A r) =
      classOfInvariant V.toSubgroup (fixedFieldOf V.toSubgroup) A (V.index • r) := by
  -- The degree `[Γ : V]` is `e * f`, so this is `pairMapH2_classOfInvariant_of_ordRat_eq` for the
  -- inclusion of `V`, with a uniformiser `π` of `k` as the invariant of order `1`.
  obtain ⟨e, f, h_ram, -⟩ := (of_finite V).exists_isRamificationData
  obtain ⟨π, hπ_unif⟩ : ∃ π : kˣ, IsUniformizer A π.val := L.exists_isUniformizer
  have hπ : ordRat k A (ofBase Γ Ω (Additive.ofMul π)) = 1 := hπ_unif.ordRat_eq_one L
  have hπ_V : ordRat (fixedFieldOf (V : Subgroup Γ)) A
      ((Units.map (RingHom.id Ω)).toAdditive (ofBase Γ Ω (Additive.ofMul π)).val) = e := by
    have hmap : (Units.map (RingHom.id Ω)).toAdditive (ofBase Γ Ω (Additive.ofMul π)).val =
        (ofBase Γ Ω (Additive.ofMul π)).val :=
      Additive.toMul.injective (Units.ext rfl)
    rw [hmap, h_ram.ordRat_eq, AddMonoidHom.smul_apply, hπ, nsmul_eq_mul, mul_one]
  rw [← h_ram.mul_eq]
  exact pairMapH2_classOfInvariant_of_ordRat_eq (L' := (of_finite V).isLocalGalois) _ (.id Ω) rfl
    (fun _ _ ↦ rfl) hπ hπ_V h_ram.residueCard_eq r

lemma resH2_classOfInvariant_eq_zero {r : QZ} (h_kill : V.index • r = 0) :
    (unitsModule Γ).resH2 V (classOfInvariant Γ k A r) = 0 := by
  rw [resH2_classOfInvariant V, h_kill]
  exact map_zero _

/-! ### The invariant -/

/-- For a henselian local field `k` of characteristic `0` with absolute Galois group `Γ`, the map
`New.Cohomology.classOfInvariant` from `ℚ/ℤ` to `H²(Γ, Ωˣ)` is bijective. So the Brauer group of `k`
is `ℚ/ℤ`.

This is the invariant isomorphism, stated for the inverse map ℚ/ℤ → H²(Γ, Ωˣ) and for `k` henselian
and discretely valued with finite residue field, complete or not. -/
lemma classOfInvariant_bijective : Bijective (classOfInvariant Γ k A) := by
  -- Injectivity is part of `isClassOfInvariant_classOfInvariant`. For surjectivity, a cocycle `x`
  -- is split by an open normal subgroup `W`, and the class of `1 / [Γ : W]` generates the classes
  -- split by `W`.
  refine ⟨isClassOfInvariant_classOfInvariant.left, Quot.ind fun ⟨x, x_cont, x_cocycle⟩ ↦ ?_⟩
  obtain ⟨W, hW⟩ : ∃ W : OpenNormalSubgroup Γ, ∀ h ∈ W, ∀ g : Γ, x (g, h) = x (g, 1) :=
    exists_openNormalSubgroup_apply_eq (x_cont.comp continuous_swap)
  have hW_index : NeZero W.index := ⟨index_ne_zero_of_finite⟩
  let r : QZ := ofZMod W.index 1
  have r_split : (unitsModule Γ).resH2 W.toOpenSubgroup (classOfInvariant Γ k A r) = 0 :=
    resH2_classOfInvariant_eq_zero _
      (by rw [← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero])
  -- `classOfInvariant` is injective, and `n • r` is the image of `n` in `ZMod W.index`.
  have r_order (n : ℕ) (h : n • classOfInvariant Γ k A r = 0) : W.index ∣ n := by
    rw [← map_nsmul, map_eq_zero_iff _ isClassOfInvariant_classOfInvariant.left, ← map_nsmul,
      nsmul_eq_mul, mul_one, map_eq_zero_iff _ QZ.ofZMod_injective,
      ZMod.natCast_eq_zero_iff] at h
    exact h
  -- On `W`, `x (g, h) = x (g, 1) = g • x (1, 1)` is the coboundary of the constant `x (1, 1)`.
  have x_g_one (g : Γ) : x (g, 1) = unitsRep g (x (1, 1)) - x (1, 1) + x (1, 1) := by
    simpa using x_cocycle g 1 1
  have x_split : (unitsModule Γ).resH2 W.toOpenSubgroup ⟦⟨x, x_cont, x_cocycle⟩⟧ = 0 :=
    (Submodule.ker_mkQ _).ge ⟨fun _ ↦ x (1, 1), continuous_const, fun g h ↦
      (hW h h.property g).trans (x_g_one g)⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n • classOfInvariant Γ k A r = ⟦⟨x, x_cont, x_cocycle⟩⟧ :=
    mem_zmultiples_of_resH2_eq_zero W.toOpenSubgroup r_split r_order x_split
  exact ⟨n • r, (map_zsmul _ n r).trans hn⟩

/-- Restriction to the open subgroup `V` (a finite extension of `k`) is onto on the classes of
`ℚ/ℤ`: every class `y` in `H²(V, Ωˣ)` is the restriction of the class of some `r`. -/
lemma exists_resH2_classOfInvariant_eq (y : ((unitsModule Γ).restrictTo V).H2) :
    ∃ r : QZ, (unitsModule Γ).resH2 V (classOfInvariant Γ k A r) = y := by
  -- `y` has an invariant `s` over the fixed field of `V`; divide `s` by the index in `ℚ/ℤ`.
  obtain ⟨s, rfl⟩ : ∃ s : QZ, classOfInvariant V.toSubgroup (fixedFieldOf V.toSubgroup) A s = y :=
    (of_finite V).isLocalGalois.classOfInvariant_bijective.surjective y
  obtain ⟨r, rfl⟩ : ∃ r : QZ, V.index • r = s :=
    DivisibleBy.surjective_smul _ ℤ (Int.natCast_ne_zero.mpr index_ne_zero_of_finite) s
  exact ⟨r, resH2_classOfInvariant V⟩

end New.IsLocalGalois
end
end

/-!
# The inequality of local Tate duality for orthogonal groups of cocycles

Throughout, `k` is a local field with absolute Galois group `Γ` (`New.IsLocalGalois`) and `l` is a
prime. The inequality of local duality is proved as a count of cocycles, for a finite discrete
module `M` and its dual `Hom(M, Ωˣ)`.

* `New.card_mul_card_le_of_le_pairingAnnihilator`: for `M` killed by a power of `l`, orthogonal
  groups of cocycles in `Hom(M, Ωˣ)` and `M` have `#X · #W ≤ #M ^ (2 + d)`, where `O` is the
  valuation ring of `k` and `#(O / l) = l ^ d`, if `Γ` acts by elements of `l`-power order.
* `New.DiscreteModule.HoldsCorestrictions.pairingAnnihilator_le`: annihilators descend from an open
  subgroup whose index is invertible on the module.
* `New.DiscreteModule.local_duality_card_dvd`: for an open subgroup `U` of index prime to `#M`, a
  largest orthogonal pair of cocycle groups over `U` bounds `#L^⊥ · #L` for cocycle groups `L` over
  `Γ`.

`New.Z1` is the group of continuous cocycles (not classes), `New.unitsModule` is `Ωˣ` written
additively, `unitsRep` is the action of `Γ` on this `Ωˣ` (so `H2 unitsRep` is `H²(Γ, Ωˣ)`),
`New.DiscreteModule.evalCup` is the cup product `Z¹(Hom(M, Ωˣ)) × Z¹(M) → H²(Ωˣ)`, and
`New.pairingAnnihilator b L` is the annihilator of `L` in the right-hand group of the pairing `b`.

Notions from other files:
* `New.DiscreteModule`: A discrete Γ-module over R: an R-module with the discrete topology and a
  continuous R-linear action of the topological group Γ.
* `New.DiscreteModule.cartierDual`: For finite M, the discrete Γ-module Hom(M, Ω^×) of additive maps
  to `New.unitsModule`, with (gf)(m) = g f(g⁻¹m).

## Relation to the literature

Known; see `Lib.ClassField.LocalDuality.CrystallineDuality` for sources.
-/

@[expose] public section

namespace New

open DiscreteUnits Cohomology DFunLike DiscreteModule QZChar NeZero QZ Ideal AddSubgroup
  IsLocalGalois Nat Function

variable {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} [J : IsLocalGalois Γ k A]
  {l r : ℕ} [Fact l.Prime] {R S : Type} [CommRing R] [CommRing S]
  {M : DiscreteModule R Γ} {N : DiscreteModule S Γ}

/-- Over a local field `k`, a continuous character `χ : Γ → ℚ/ℤ` whose cyclic class `δχ ∪ w` in
`H²(Γ, Ωˣ)` vanishes for every `w` in `kˣ` is zero. -/
lemma Cohomology.char_eq_zero_of_cyclicClass_eq_zero {χ : QZChar Γ}
    (h : ∀ w : Additive kˣ, cyclicClass unitsRep χ (DiscreteUnits.ofBase Γ Ω w) = 0) (g : Γ) :
    χ.val g = 0 := by
  -- The class with invariant `χ g` dies over the fixed field of `ker χ`, since restriction
  -- multiplies the invariant by the index. So it is a symbol `(χ, w)`, hence zero.
  have h_index : (ker χ).index • χ.val g = 0 :=
    congrArg Multiplicative.toAdd
      (by simpa using (ker χ).pow_index_mem g : toHom χ g ^ (ker χ).index = 1)
  obtain ⟨w, hw⟩ : ∃ w : kˣ, classOfInvariant Γ k A (χ.val g) = cyclicClass _ χ
    (ofBase Γ Ω (.ofMul w)) :=
    ((cyclicClass_spec χ).1 _).mp (resH2_classOfInvariant_eq_zero _ h_index)
  -- `classOfInvariant` is injective
  exact (map_eq_zero_iff _ isClassOfInvariant_classOfInvariant.left).mp (hw.trans (h _))

/-- Let `k` be local, `i · [Γ : U]` act as the identity on `M`, `b : M × N → Ωˣ` an equivariant
pairing, and let `X`, `Y` contain the coboundaries and corestrictions of `X'`, `Y'`. If `X'`
contains the cup product annihilator of `Y'` over `U`, then `X` contains that of `Y`. -/
lemma DiscreteModule.HoldsCorestrictions.pairingAnnihilator_le {U : OpenSubgroup Γ}
    {X : AddSubgroup ↥(Z1 M.ρ)} {X' : AddSubgroup ↥(Z1 (M.restrictTo U).ρ)}
    {Y : AddSubgroup ↥(Z1 N.ρ)} {Y' : AddSubgroup ↥(Z1 (N.restrictTo U).ρ)} {i : ℤ}
    (hX : M.HoldsCorestrictions U X' X) (hY : N.HoldsCorestrictions U Y' Y)
    (h_inv : ∀ m : M, i • U.index • m = m)
    {b : (M.restrictTo (U : Subgroup Γ)).V →+ (N.restrictTo (U : Subgroup Γ)).V →+
      (unitsModule (U : Subgroup Γ)).V}
    (h_equivariant : ∀ (g : Γ) (x : M.V) (y : N.V),
      (b ((M.ρ g) x)) ((N.ρ g) y) = ((unitsModule Γ).ρ g) ((b x) y))
    (h_ann :
      pairingAnnihilator
        (cupProduct (unitsModule U.toSubgroup) (M.restrictTo U.toSubgroup)
          (N.restrictTo U.toSubgroup) b fun g : (U : Subgroup Γ) ↦ h_equivariant g).flip
        Y' ≤ X') :
    pairingAnnihilator (cupProduct (unitsModule Γ) M N b h_equivariant).flip Y ≤ X := by
  intro z hz
  -- The restriction of `z` to `U` is orthogonal to `Y'`, hence lies in `X'`.
  let z' : Z1 (M.restrictTo (U : Subgroup Γ)).ρ :=
    pairMapZ1 (subgroupIncl (U : Subgroup Γ)) .id (fun _ _ ↦ rfl) z
  have h_res_mem : z' ∈ X' := by
    refine h_ann fun y hy ↦ ?_
    -- `y` is the Shapiro image of a cocycle `F` in functions on `Γ ⧸ U` with sum in `Y`.
    obtain ⟨F, rfl, hF : (N.sum U).mapZ1 F ∈ Y⟩ := hY.exists_corestriction y hy
    -- Pair `z` with the Shapiro lift `F` of `y`, in functions on `Γ ⧸ U`.
    let β : ((unitsModule Γ).funModule (U : Subgroup Γ)).H2 :=
      cupProduct ((unitsModule Γ).funModule (U : Subgroup Γ)) M (N.funModule _)
        (.mk' (fun m ↦ (b m).compLeft _) (by bound)) (by simp [funext_iff, h_equivariant]) z F
    -- Its Shapiro image is the class to be killed; its sum over `Γ ⧸ U` vanishes by `hz`.
    have h_shapiro_β :
        shapiroH2 U β =
          cupProduct (unitsModule (U : Subgroup Γ)) _ _ b (fun g ↦ h_equivariant g) z'
            (N.shapiroZ1 U F) :=
      -- Both are classes of cocycles that agree pointwise, by evaluating `F` at the trivial coset.
      congrArg (Quotient.mk _)
        (Subtype.ext (funext fun _ ↦ congrArg (b _) (N.funModule_apply_one U ..)))
    have h_sum_β :
        ((unitsModule Γ).sum _).mapH2 β =
          cupProduct (unitsModule Γ) M N b h_equivariant z ((N.sum _).mapZ1 F) :=
      -- The cocycles agree pointwise: the sum over the cosets commutes with the action.
      congrArg (Quotient.mk _) (by
        simp [← (sum ..).isIntertwining]
        simp [sum])
    -- The Shapiro image is the restriction of a class of invariant `s`, and the sum has
    -- invariant `U.index • s`; so `U.index • s = 0` and the restriction vanishes.
    obtain ⟨s, hs⟩ : ∃ s : QZ, (unitsModule Γ).resH2 U (classOfInvariant Γ k A s) = shapiroH2 U β :=
      exists_resH2_classOfInvariant_eq U _
    have h_index : classOfInvariant Γ k A (U.index • s) = 0 := by
      rw [map_nsmul, ← mapH2_sum_eq_index_smul U _ _ hs, h_sum_β]
      exact hz _ hF
    have h_res : (unitsModule Γ).resH2 U (classOfInvariant Γ k A s) = 0 :=
      resH2_classOfInvariant_eq_zero U ((map_eq_zero_iff _
        isClassOfInvariant_classOfInvariant.left).mp h_index)
    exact (hs.trans h_shapiro_β).symm.trans h_res
  -- A corestriction of it lies in `X`, and differs from `U.index • z` by a coboundary.
  obtain ⟨F, sh_F, hF : (M.sum U).mapZ1 F ∈ X⟩ := hX.exists_corestriction z' h_res_mem
  -- On `U`, at the trivial coset, `F` agrees with `z`; so `F` minus the constant lift of `z` is a
  -- coboundary, by Shapiro's lemma.
  have h_sh (u : (U : Subgroup Γ)) : F.val u ⟦1⟧ = z.val u :=
    congrFun (congrArg Subtype.val sh_F) u
  have h_diff (u : (U : Subgroup Γ)) : (F - (M.const _).mapZ1 z).val u ⟦1⟧ = M.ρ u 0 - 0 := by
    simpa [sub_eq_zero, DiscreteModule.const] using h_sh u
  obtain ⟨n, hn⟩ : ∃ n : (M.funModule U).V, ∀ g : Γ,
      (F - (M.const _).mapZ1 z).val g = (M.funModule (U : Subgroup Γ)).ρ g n - n :=
    shapiro_H1 U _ 0 h_diff
  have h_index : U.index • z = (M.sum _).mapZ1 F - M.coboundary (M.sum _ n) := by
    ext g
    -- Sum the equation `hn g` over the cosets.
    have h_const : M.sum (U : Subgroup Γ) (M.const (U : Subgroup Γ) (z.val g)) =
        M.sum (U : Subgroup Γ) fun _ ↦ z.val g := rfl
    simpa [index_smul_eq_sum_const, ← (sum ..).isIntertwining, h_const] using
      congrArg (fun f ↦ M.sum _ (F.val g - f)) (hn g)
  -- Multiplication by `i` inverts multiplication by `U.index`.
  have h_inv' : z = i • U.index • z := Subtype.ext (funext fun g ↦ (h_inv _).symm)
  rw [h_inv', h_index]
  exact zsmul_mem (sub_mem hF (hX.coboundary_mem _)) i

/-- Kummer theory in each coordinate: for a finite trivial module `M` killed by `l`, there are at
most `#M ^ (2 + d)` cocycles in `Hom(M, Ωˣ)`, where `O` is the valuation ring of `k` and
`#(O / l) = l ^ d`. -/
lemma card_dual_cocycles_le_of_trivial [Finite M] {d : ℕ}
    (hd : Nat.card (valRingBelow k A ⧸ span {(l : valRingBelow k A)}) = l ^ d)
    (h_kill : ∀ m : M, l • m = 0) (h_triv : M.TrivialOn ⊤) :
    Nat.card (Z1 M.cartierDual.ρ) ≤ Nat.card M ^ (2 + d) := by
  -- Being killed by `l`, `M` is a vector space over `ZMod l`; take a basis `e`.
  have h_module : Module (ZMod l) M.V := AddCommGroup.zmodModule h_kill
  let e := Module.finBasis (ZMod l) M
  -- `K`: the cocycles in `Ωˣ` killed by `l`; Kummer theory counts them.
  let K : Submodule ℤ ↥(Z1 (unitsModule Γ).ρ) :=
    (l : Module.End ℤ (Z1 (unitsModule Γ).ρ)).ker
  have K_card :
      Nat.card K = l ^ 2 * Nat.card (valRingBelow k A ⧸ span {(l : valRingBelow k A)}) :=
    IsLocalGalois.card_ker_natCast_Z1_unitsModule l
  have : Finite K := IsLocalGalois.finite_ker_natCast_Z1_unitsModule (k := k) (A := A) l
  -- The values of a cocycle at the basis vectors are cocycles in `Ωˣ` killed by `l`.
  let coord (z : Z1 M.cartierDual.ρ) (j : Fin (Module.finrank (ZMod l) M)) : K :=
    ⟨pairMapZ1 (.id _) ⟨⟨fun f ↦ f (e j), by simp⟩, by simp⟩ (by simp [h_triv]) z, by
      ext
      simp [← map_nsmul, h_kill]⟩
  -- They determine the cocycle, as additive maps that agree on a basis over `ZMod l` are equal.
  have h_coord_inj : Function.Injective coord := fun x y h ↦ by
    ext g : 3
    -- The coordinates of `x` and `y` at `g` agree on every basis vector.
    have h_coord (j : Fin (Module.finrank (ZMod l) M)) : (x.val g) (e j) = (y.val g) (e j) :=
      congrArg (fun c : K ↦ (c : Z1 (unitsModule Γ).ρ).val g) (congrFun h j)
    have h_top : ((x.val g).eqLocus (y.val g)).toZModSubmodule l = ⊤ :=
      (Submodule.eq_top_iff_forall_basis_mem e).mpr h_coord
    exact h_top.ge Submodule.mem_top
  calc
    _ ≤ Nat.card (Fin _ → K) := Nat.card_le_card_of_injective _ h_coord_inj
    _ = (l ^ (2 + d)) ^ Module.finrank (ZMod l) M := by simp [Nat.card_fun, K_card, hd, pow_add]
    _ = _ := by simp [Nat.card_congr e.equivFun.toEquiv, pow_right_comm]

/-- One side of the nondegeneracy of the Hilbert symbol, extended to a trivial module. Let `Γ` act
as `Gal(Ω/k)` on an algebraically closed field `Ω` of characteristic 0, with `A ∩ k` a discrete
valuation ring with finite residue field (`IsLocalGalois Γ k A`), and let `M` be a finite discrete
`Γ`-module killed by the prime `l` on which all of `Γ` acts trivially. A continuous 1-cocycle `y`
of `M` is zero if its cup product `M.evalCup x y` vanishes for every continuous 1-cocycle `x` of
`Hom(M, Ωˣ)`. -/
lemma eq_zero_of_evalCup_eq_zero_of_trivialOn [Finite M] (h_kill : ∀ m : M, l • m = 0)
    (h_triv : M.TrivialOn ⊤) {y : Z1 M.ρ} (hy : ∀ x : Z1 M.cartierDual.ρ, M.evalCup x y = 0) :
    y = 0 := by
  have h_units_cont :
      Continuous (uncurry fun (g : Γ) (u : (unitsModule Γ).V) ↦ (unitsModule Γ).ρ g u) :=
    (unitsModule Γ).continuous
  -- It is enough that each coordinate `ξ = j ∘ y` in `ZMod l` vanishes, and for this
  -- (`char_eq_zero_of_cyclicClass_eq_zero`) that its symbol with each `x` in `kˣ` vanishes.
  ext g
  refine eq_zero_of_forall_hom_eq_zero
    ((bijective_ofZMod_comp h_kill).surjective.forall.mpr fun j ↦ ?_)
  let ξ : Z1 (Representation.trivial ℤ Γ (ZMod l)) :=
    ⟨j ∘ y.val, y.prop.imp (by fun_prop) (by simp_all)⟩
  refine char_eq_zero_of_cyclicClass_eq_zero (χ := ofZModCocycle l ξ) (fun x ↦ ?_) g
  -- The Kummer cocycle of an `l`-th root `a` of `x`, twisted by `j`, takes values in `Hom(M, Ωˣ)`.
  obtain ⟨a, ha⟩ : ∃ a : DiscreteUnits Ω, l • a = DiscreteUnits.ofBase Γ Ω x :=
    exists_nsmul (DiscreteUnits.ofBase Γ Ω x).val (out : l ≠ 0)
  let z : Z1 M.cartierDual.ρ :=
    ⟨fun g ↦ .mk' (fun m ↦ (j m).val • (unitsRep g a - a)) (by
        simp [ZMod.val_add, add_smul, ← nsmul_eq_mod_nsmul, smul_sub l, ← map_nsmul, ha,
          DiscreteUnits.ext_iff]),
      .congr (by
        simp only [AddMonoidHom.mk'_apply]
        fun_prop) (leftInverse_invFun coe_injective ∘' _),
      by simp [ext_iff, h_triv, smul_sub]⟩
  -- Its cup product with `y` is minus the symbol (`mk_eq_neg_cyclicClass_ofZModCocycle`).
  exact neg_eq_zero.mp
    ((mk_eq_neg_cyclicClass_ofZModCocycle ha ξ _ (by simp [z, ξ, h_triv])).symm.trans (hy z))

/-- Let `k` be local with valuation ring `O` and `#(O / l) = l ^ d`. Let `M` be a finite module
killed by `l ^ r` and fixed by `Q`, where every `g : Γ` has a power `g ^ l ^ i` in `Q`. This is
`hM : FiniteKilledFixedInj (l ^ r) Q 1 0 M`, the predicate for which dévissage is stated; its last
two arguments `1` and `0` ask that `ρ 1 - 0 = id` be injective, so they impose nothing. If groups
`X` of cocycles in `Hom(M, Ωˣ)` and `W` of cocycles in `M` are orthogonal under the cup product
(`h_orth`), then `#X · #W ≤ #M ^ (2 + d)`: the form of Tate's local duality and Euler
characteristic formula used. -/
lemma card_mul_card_le_of_le_pairingAnnihilator [Finite M] {d : ℕ} (Q : Subgroup Γ)
    (hd : Nat.card (valRingBelow k A ⧸ span {(l : valRingBelow k A)}) = l ^ d)
    (hM : FiniteKilledFixedInj (l ^ r) Q 1 0 M) (h_pow : ∀ g : Γ, ∃ i : ℕ, g ^ l ^ i ∈ Q)
    (X : AddSubgroup ↥(Z1 M.cartierDual.ρ)) (W : AddSubgroup ↥(Z1 M.ρ))
    (h_orth : X ≤ pairingAnnihilator M.evalCup.flip W) :
    Nat.card X * Nat.card W ≤ Nat.card M ^ (2 + d) := by
  -- The dévissage runs over all modules with the same conditions, so prove the bound for each.
  suffices h_all : ∀ (M : DiscreteModule R Γ) (hM : FiniteKilledFixedInj (l ^ r) Q 1 0 M),
      have : Finite M := hM.finite
      ∀ (X : AddSubgroup ↥(Z1 M.cartierDual.ρ)) (W : AddSubgroup ↥(Z1 M.ρ)),
        X ≤ pairingAnnihilator M.evalCup.flip W →
          Nat.card X * Nat.card W ≤ Nat.card M ^ (2 + d) from h_all M hM X W h_orth
  intro M hM
  -- Dévissage: reduce to trivial modules killed by `l` and to extensions.
  have := J.finite_Z1
  refine M.devissage_induction rfl ⊤ Q (by simpa)
    (fun M _ ⟨h_finite, h_kill, h_triv, h_inj⟩ X W h ↦ ?_)
    (fun {M' M M'' ι π} s hM ih' ih'' X W h ↦ ?_) hM
  · -- Trivial modules killed by `l`: the pairing has no kernel in `Z1 M.ρ`.
    have h_ker_bot : M.evalCup.flip.ker ⊓ W = ⊥ := bot_unique fun y hy ↦
      eq_zero_of_evalCup_eq_zero_of_trivialOn h_kill h_triv (ext_iff.mp hy.1)
    calc
      Nat.card X * Nat.card W ≤ Nat.card (pairingAnnihilator M.evalCup.flip W) * Nat.card W := by
        grw [card_le_of_le h]
      _ = Nat.card (Z1 M.cartierDual.ρ) := by
        rw [card_pairingAnnihilator_mul_card _ (.ofBijective _ classOfInvariant_bijective),
          h_ker_bot, card_bot, mul_one]
      _ ≤ Nat.card M ^ (2 + d) := card_dual_cocycles_le_of_trivial hd h_kill h_triv
  -- Extensions `M' → M → M''` of finite modules. A map on `M` that kills `M'` comes from `M''`.
  have ⟨ι_inj, h_exact, π_surj⟩ : Injective ι ∧ Exact ι π ∧ Surjective π := s
  have := hM.finite
  have := (hM.left_of_isShortExact s).finite
  have := (hM.right_of_isShortExact s).finite
  -- The dual maps `f ↦ f ∘ ι` and `f ↦ f ∘ π`, again equivariant.
  let ι' : M.cartierDual.Hom M'.cartierDual :=
    ⟨(AddMonoidHom.compHom' ↑ι).toIntLinearMap, by simp [ι.isIntertwining, ext_iff]⟩
  let π' : M''.cartierDual.Hom M.cartierDual :=
    ⟨(AddMonoidHom.compHom' ↑π).toIntLinearMap, by simp [π.isIntertwining, ext_iff]⟩
  have π'_inj : Injective π' := fun f f' h_eq ↦
    ext f f' (π_surj.forall.mpr (DFunLike.congr_fun h_eq))
  have dual_exact : Exact π' ι' := by
    refine fun f ↦ ⟨fun hf ↦ ?_, ?_⟩
    · -- A map on `M` that kills `M'` extends from `M''`.
      have h_kills (m : M') : f (ι m) = 0 := DFunLike.congr_fun hf m
      obtain ⟨f', hf'⟩ : ∃ f' : M'' →+ DiscreteUnits Ω, ∀ m : M, f' (π m) = f m :=
        exists_extend π.toAddMonoidHom f fun m hm ↦ by
          obtain ⟨m', rfl⟩ := (h_exact m).mp hm
          exact h_kills m'
      exact ⟨f', ext _ _ hf'⟩
    · rintro ⟨f', rfl⟩
      -- `π ∘ ι = 0`.
      exact ext _ _ fun m ↦ by simp [ι', π', h_exact.apply_apply_eq_zero]
  -- The part of `X` from `M''` is orthogonal to the image of `W`, and symmetrically: a map and its
  -- dual are adjoint for the cup products, already on the level of cocycles.
  have orth'' : comap π'.mapZ1 X ≤ pairingAnnihilator M''.evalCup.flip (map π.mapZ1 W) := by
    rintro x hx _ ⟨w, hw, rfl⟩
    have h_cup : M''.evalCup x (π.mapZ1 w) = M.evalCup (π'.mapZ1 x) w :=
      congrArg (Quotient.mk _) (by simp [π', π.isIntertwining])
    exact h_cup.trans (h hx w hw)
  have orth' : map ι'.mapZ1 X ≤ pairingAnnihilator M'.evalCup.flip (comap ι.mapZ1 W) := by
    rintro _ ⟨x, hx, rfl⟩ w hw
    have h_cup : M'.evalCup (ι'.mapZ1 x) w = M.evalCup x (ι.mapZ1 w) :=
      congrArg (Quotient.mk _) (by simp [ι', ι.isIntertwining])
    exact h_cup.trans (h hx (ι.mapZ1 w) hw)
  -- Count `X` and `W` by their two parts, pair the parts crosswise, and multiply the bounds.
  calc Nat.card X * Nat.card W
      = (Nat.card (comap π'.mapZ1 X) * Nat.card (map π.mapZ1 W)) *
          (Nat.card (map ι'.mapZ1 X) * Nat.card (comap ι.mapZ1 W)) := by
        rw [π'.card_eq_card_comap_mul_card_map π'_inj dual_exact X,
          ι.card_eq_card_comap_mul_card_map ι_inj h_exact W]
        ring
    _ ≤ Nat.card M'' ^ (2 + d) * Nat.card M' ^ (2 + d) :=
        Nat.mul_le_mul (ih'' _ _ orth'') (ih' _ _ orth')
    _ = Nat.card M ^ (2 + d) := by rw [s.card_eq_card_mul_card, mul_pow, mul_comm]

/-- Let `M` be a finite module killed by `l ^ r` and fixed by `Q` (`hM`), where every `g : Γ` has a
power `g ^ l ^ i` in `Q`, and let `#(O / l) = l ^ d` for the valuation ring `O = A ∩ k` of the local
field `k`. If groups `X` of cocycles in `Hom(M, Ωˣ)` and `W` of cocycles in `M` are orthogonal under
the cup product `M.evalCup`, then `#X · #W ≤ #M ^ (2 + d)`. This is
`card_mul_card_le_of_le_pairingAnnihilator`, with the finiteness of `M` taken from `hM` inside the
statement.

This inequality is a numerical consequence of Tate local duality and the local Euler characteristic
formula, for 1-cocycles and `l`-primary `M` on which `Γ` acts through an `l`-group; perfectness of
the pairing is not asserted. -/
lemma card_mul_card_le_of_orthogonal {d : ℕ} (Q : Subgroup Γ)
    (hd : Nat.card (valRingBelow k A ⧸ span {(l : valRingBelow k A)}) = l ^ d)
    (hM : FiniteKilledFixedInj (l ^ r) Q 1 0 M) (h_pow : ∀ g : Γ, ∃ i : ℕ, g ^ l ^ i ∈ Q) :
    have : Finite M := hM.finite
    ∀ (X : AddSubgroup ↥(Z1 M.cartierDual.ρ)) (W : AddSubgroup ↥(Z1 M.ρ)),
      X ≤ pairingAnnihilator M.evalCup.flip W → Nat.card X * Nat.card W ≤ Nat.card M ^ (2 + d) :=
  fun X W h_orth ↦
    have : Finite M := hM.finite
    card_mul_card_le_of_le_pairingAnnihilator Q hd hM h_pow X W h_orth

/-- A divisibility form of local duality. Let `M` be finite and `U` an open subgroup of index prime
to `#M`. Let `X'`, `W'` be groups of cocycles of `U` in `Hom(M, Ωˣ)` and `M` that are orthogonal
under the cup product, with `#X' · #W'` largest among such pairs, and let `X`, `W` contain the
coboundaries and corestrictions of `X'`, `W'` (`New.DiscreteModule.HoldsCorestrictions`). Then
`#L^⊥ · #L` divides `#W · #X` for every group `L` of cocycles of `Γ` in `Hom(M, Ωˣ)`, where `L^⊥`
is the annihilator of `L` among the cocycles in `M`. -/
lemma DiscreteModule.local_duality_card_dvd [Finite M] {U : OpenSubgroup Γ}
    {X : AddSubgroup ↥(Z1 M.cartierDual.ρ)} {W : AddSubgroup ↥(Z1 M.ρ)}
    {X' : AddSubgroup ↥(Z1 (M.cartierDual.restrictTo U).ρ)}
    {W' : AddSubgroup ↥(Z1 (M.restrictTo U).ρ)}
    (hX : M.cartierDual.HoldsCorestrictions U X' X) (hW : M.HoldsCorestrictions U W' W)
    (h_coprime : (Nat.card M).Coprime U.index)
    (h_orth : W' ≤ pairingAnnihilator (M.restrictTo U).evalCup X')
    (h_max : ∀ (Y : AddSubgroup ↥(Z1 (M.restrictTo U).cartierDual.ρ))
      (Z : AddSubgroup ↥(Z1 (M.restrictTo U).ρ)),
      Y ≤ pairingAnnihilator (M.restrictTo U).evalCup.flip Z →
      Nat.card Y * Nat.card Z ≤ Nat.card X' * Nat.card W')
    (L : AddSubgroup ↥(Z1 M.cartierDual.ρ)) :
    Nat.card (pairingAnnihilator M.evalCup L) * Nat.card L ∣ Nat.card W * Nat.card X := by
  -- The index of `U` acts invertibly on `M`, being prime to its order.
  obtain ⟨i, index_inv⟩ : ∃ i : ℤ, ∀ m : M, i • U.index • m = m :=
    ⟨_, (nsmulCoprime h_coprime).left_inv⟩
  -- `classOfInvariant` identifies `ℚ/ℤ` with `H²(Γ, Ωˣ)`.
  let e : QZ ≃+ New.H2 unitsRep := AddEquiv.ofBijective _ J.classOfInvariant_bijective
  have := (of_finite U).isLocalGalois.finite_Z1
  -- The orthogonality of `X'` and `W'`, read from the side of `X'`.
  have h_orth' : X' ≤ pairingAnnihilator (M.restrictTo U).evalCup.flip W' := fun x hx w hw ↦
    h_orth hw x hx
  -- `X'` pairs to zero with everything that annihilates it.
  have h_double : X' ≤ pairingAnnihilator (M.restrictTo U).evalCup.flip
      (pairingAnnihilator (M.restrictTo U).evalCup X') := fun x hx w hw ↦ hw x hx
  -- By maximality each of `X'`, `W'` is the whole annihilator of the other.
  have X'_eq : X' = pairingAnnihilator (M.restrictTo U).evalCup.flip W' :=
    eq_of_le_of_card_ge h_orth' (le_of_mul_le_mul_right (h_max _ _ le_rfl) card_pos)
  have W'_eq : W' = pairingAnnihilator (M.restrictTo U).evalCup X' :=
    eq_of_le_of_card_ge h_orth (le_of_mul_le_mul_left (h_max _ _ h_double) (card_pos (α := X')))
  -- Annihilators descend to `Γ`, on both sides; the second uses anticommutativity of the cup.
  -- On `Hom(M, Ωˣ)` too, `i · [Γ : U]` acts as the identity.
  have index_inv_dual (f : M.cartierDual) : i • U.index • f = f :=
    ext _ _ fun m ↦ by simpa using congrArg f (index_inv m)
  have ann_W : pairingAnnihilator M.evalCup.flip W ≤ X :=
    hX.pairingAnnihilator_le hW (i := i) index_inv_dual (by simp) X'_eq.ge
  -- Over `U`, what annihilates `X'` in the flipped pairing annihilates it in the pairing, as the
  -- cup product changes sign when flipped; over `Γ` the same holds for `w` and `X`.
  have ann_X : pairingAnnihilator M.evalCup X ≤ W := fun w hw ↦
    hW.pairingAnnihilator_le hX index_inv (by simp)
      (fun w' hw' ↦ W'_eq.ge fun x hx ↦
        neg_eq_zero.mp ((cupProduct_flip ..).symm.trans (hw' x hx)))
      (fun x hx ↦ (cupProduct_flip ..).trans (by simpa using hw x hx))
  have ker_le : M.evalCup.ker ≤ X := fun x hx ↦ ann_W fun w _ ↦ ext_iff.mp hx w
  calc
    Nat.card (pairingAnnihilator M.evalCup L) * Nat.card L
    _ = Nat.card (Z1 M.ρ) * Nat.card ↥(M.evalCup.ker ⊓ L) := card_pairingAnnihilator_mul_card _ e L
    _ ∣ Nat.card (Z1 M.ρ) * Nat.card ↥(M.evalCup.ker ⊓ X) :=
      mul_dvd_mul_left _ (card_dvd_of_le (inf_le_of_left_le (le_inf le_rfl ker_le)))
    _ = Nat.card (pairingAnnihilator M.evalCup X) * Nat.card X :=
      (card_pairingAnnihilator_mul_card _ e X).symm
    _ ∣ Nat.card W * Nat.card X := mul_dvd_mul_right (card_dvd_of_le ann_X) _

end New
