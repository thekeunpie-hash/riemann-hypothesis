module

import Mathlib.Algebra.Order.Star.Int
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.Adelic.TraceFormula.OrbitalUnfolding
public import Lib.DiscreteSeries.Character.WeylCharacterFormula
import Lib.Adelic.Landherr
import Lib.Adelic.Reduction.DefiniteClassSums
import Lib.Adelic.Unitary.WeakApproximation
import Lib.DiscreteSeries.Character.FormalDegree
import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
import Lib.General.LinearAlgebra.Eigenvalues
import Lib.General.LinearAlgebra.MatrixPolynomials
import Lib.Weil.Periods.Grading
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Analysis.InnerProductSpace.NormDet
public import Lib.Speed
public import Lib.Adelic.TraceFormula.TestFunction
public import Lib.Shimura.HeckeTower.HeckeData
public import Lib.Weil.Unramified.SplitHecke
import TauCeti.RepresentationTheory.AsAlgebraHom
public import Lib.Adelic.TraceFormula.LevelAlgebra
public import Lib.Adelic.TraceFormula.LineStabiliser
public import Lib.Adelic.AutomorphicForms.Basic
import Lib.ClassField.HeckeL.EulerProduct
import Lib.General.NumberTheory.FrobeniusOrbits

section
/-!
# Comparison of traces of operators on forms for different spaces and signs

A simple trace formula for the unitary group of a hermitian space `V`, with terms sorted by the
characteristic polynomials `R` of rational points. The test function is `e ⊗ φ`, with `e` a cusp
kernel on the real group and `φ` locally constant of compact support on the finite adelic group.

This file proves the Selberg principle: orbital integrals of an irreducible `R` with a root off
the unit circle vanish. For `R` with all roots on the unit circle, it splits orbital integrals into
real and finite factors and matches the classes of different signs. It concludes that the trace on
forms depends neither on the space nor on its signs.

## Main definitions and results

* `New.Space.orbitalIntegral_eq_zero`: the orbital integral is `0` if `R` is irreducible with a root
  off the unit circle.
* `New.Space.exists_geometricSide_singleton_eq`: if `R` is irreducible with all roots on the unit
  circle, `E` contains the 5040th roots of unity and has an even number of infinite places, and the
  parameter has a large gap, its term is a product of characters of the compact unitary group times
  a number that depends only on `R` and `φ`.
* `New.trace_comparison`: let `E` contain the 5040th roots of unity and have an even number of
  infinite places, let `n ≥ 2`, and let the parameter have a large gap. If `φ` is cuspidal at a
  split place and, at a place `w'`, the elements of its support are integral with `0` a simple root
  of the characteristic polynomial modulo `w'`, the reducible `R` contribute nothing, so the trace
  depends neither on the space nor on its signs.

Notions from other files:
* `New.Space E n s`: a hermitian form `J` over `E` with an adelic frame `x` in which it is `diag s`
  at infinity and `1` at the finite places. `V.ratEmbed` embeds `U(J)(E)` in `G = G_∞ × G_f` with
  image `Γ = V.Γ`, and `V.quotMeasure` integrates over `[G] = Γ \ G`.
* `New.IsCuspKernel B e`: `e` is a minimal convolution idempotent on `G_∞` with moment of order
  `B + 1` and decay of order `B`, and `α ⋆ e = e` for some continuous compactly supported `α`.
* `V.polyTerm k φ S γ x`: the value of `k ⊗ φ` at `x⁻¹ γ x` if the characteristic polynomial of `γ`
  lies in `S`, and `0` otherwise.
* `V.formRep e`: the action of `G_f` on the forms of type `e`, which for integrable `e` are the
  bounded automorphic functions on `G` fixed by right convolution with `e`; a level `K` is an open
  subgroup of the standard compact subgroup.
* `New.Space.orbitalIntegral` (in `Lib.Adelic.TraceFormula.OrbitalUnfolding`): the orbital integral
  `I_γ`, the integral of the term of `γ` over `G` modulo the rational centraliser of `γ`.

## Relation to the literature

Comparison of simple trace formulas for unitary groups that differ only at real places. Here
integrable idempotent kernels of very regular discrete series replace pseudo-coefficients, and the
CM field contains the 5040th roots of unity and has an even number of infinite places. There is no
truncation and no endoscopy. Source: Labesse, Changement de base CM et séries discrètes (2011),
Thms 5.4, 5.5 and their proofs; Arthur and Clozel (1989), ch. 1, Lemmas 2.4-2.6; integrable test
functions as in Knightly and Li, Traces of Hecke operators (2006); for the simple trace formula
with a cuspidal component, Flicker and Kazhdan (1988) and Harris and Labesse (2004), Prop. 1.10.5.

Selberg principle that orbital integrals of an idempotent vanish off the elliptic set. Here the
idempotent is a minimal convolution idempotent with polynomial decay on a product of groups
U(p,q), placed inside the adelic orbital integral of a rational point with irreducible
characteristic polynomial. If some eigenvalue has absolute value other than 1, this integral is
zero. Source: Harish-Chandra, Discrete series II, Acta Math. 116 (1966), Thm 11; Blanc and
Brylinski, Cyclic homology and the Selberg principle, J. Funct. Anal. 109 (1992); Hochs and Wang,
Orbital integrals and K-theory classes (2019), Cor 4.8.
-/

@[expose] public section

noncomputable section

open MeasureTheory Fintype

open NumberField Measure Matrix Polynomial Module Subgroup Complex MulAction New.Variety Finset
  Equiv Real ConjAct ENNReal

open scoped Norms.L2Operator InnerProductSpace ComplexOrder

namespace New

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]

namespace Space

variable {s : n → ℤˣ} (V : Space E n s) {B : ℕ} {k e : GInf E s → ℂ}

/-! ### The Selberg principle -/

/-- The trace property for the triple kernel of `e ⊗ φ` at the rational point `γ`. Let `a` be a
weight on triples that is invariant under left translation by the rational centraliser of `γ`, and
let `b` be `a` composed with the rotation of triples. Then the kernel has the same integral against
`a` and against `b`, if both converge. -/
lemma integral_mul_tripleKernel_tripleRotate (φ : TestFunction (Gf E n)) (he : Measurable e)
    {γ : U V.J} {a b : G E s × GInf E s × GInf E s → ℝ} (ha_meas : Measurable a)
    (ha : Integrable (fun p : G E s × GInf E s × GInf E s ↦ a p * V.tripleKernel e φ γ p)
      (V.tripleMeasure γ))
    (hb : Integrable (fun p : G E s × GInf E s × GInf E s ↦ b p * V.tripleKernel e φ γ p)
      (V.tripleMeasure γ))
    (hab : ∀ p : G E s × GInf E s × GInf E s, a (V.tripleRotate γ p) = b p)
    (ha_inv : ∀ t : U V.J, Commute γ t → ∀ (x : G E s) (q : GInf E s × GInf E s),
      a (V.ratEmbed t * x, q) = a (x, q)) :
    ∫ p : G E s × GInf E s × GInf E s, b p * V.tripleKernel e φ γ p ∂V.tripleMeasure γ =
      ∫ p : G E s × GInf E s × GInf E s, a p * V.tripleKernel e φ γ p ∂V.tripleMeasure γ := by
  let f (p : G E s × GInf E s × GInf E s) : ℂ := a p * V.tripleKernel e φ γ p
  have h_comp (p : G E s × GInf E s × GInf E s) :
      f (V.tripleRotate γ p) = b p * V.tripleKernel e φ γ p := by
    simp only [f, hab, V.tripleKernel_tripleRotate]
  simpa only [h_comp] using V.integral_comp_tripleRotate (f := f) (by fun_prop) ha
    (by simpa only [h_comp] using hb)
    fun t ht x q ↦ by simp only [f, ha_inv t ht, V.tripleKernel_ratEmbed_mul φ ht]

/-- Let `V` be a hermitian space with a frame, and let `e` be a cusp kernel of order `B ≥ 13 n ^ 3`:
a minimal idempotent with `‖x‖^(B+1) e(x)` integrable, `‖x‖^B e(x)` bounded, and `α ⋆ e = e` for
some continuous compactly supported `α`. Let the rational point `γ` have an irreducible
characteristic polynomial, and let `H` be a measurable function on the real group that moves by at
most `∏_w ‖b_w‖` under right multiplication by `b`. If the real part of `γ` shifts `H` by `ℓ` on the
left and every rational point that commutes with `γ` shifts it by a constant, then `ℓ` times the
orbital integral of `e ⊗ φ` at `γ` (over `G` modulo the rational centraliser of `γ`) vanishes. -/
lemma mul_orbitalIntegral_eq_zero [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) (he : IsCuspKernel B e) {γ : U V.J}
    (hγ : Irreducible (γ : GL n E).val.charpoly) {H : GInf E s → ℝ} {ℓ : ℝ} (hH : Measurable H)
    (h_lip : ∀ a b : GInf E s, |H (a * b) - H a| ≤ ∏ w : InfinitePlace E, ‖(b w : Matrix n n ℂ)‖)
    (h_shift : ∀ y : GInf E s, H ((V.ratEmbed γ).1 * y) = ℓ + H y)
    (h_cent : ∀ t : U V.J, Commute γ t →
      ∃ r : ℝ, ∀ y : GInf E s, H ((V.ratEmbed t).1 * y) = r + H y) :
    ℓ * V.orbitalIntegral e φ γ = 0 := by
  -- Write `I_γ = tr (p p p γ)` for the projection `p(a, b) = e(a⁻¹ b)`; let `∂` multiply a kernel
  -- by `H b - H a`. On triples `(x, y, u)` the weights `a₁`, `a₂`, `a₃` are the increments of `H`
  -- along `x, x y, x y u, γ x`; they give `∂p p p`, `p ∂p p` and `p p ∂p`.
  have h_meas : Measurable e := he.continuous.measurable
  let P : G E s × GInf E s × GInf E s → ℂ := V.tripleKernel e φ γ
  let m : Measure (G E s × GInf E s × GInf E s) := V.tripleMeasure γ
  let a₁ (p : G E s × GInf E s × GInf E s) : ℝ := H (p.1.1 * p.2.1) - H p.1.1
  let a₂ (p : G E s × GInf E s × GInf E s) : ℝ := H (p.1.1 * p.2.1 * p.2.2) - H (p.1.1 * p.2.1)
  let a₃ (p : G E s × GInf E s × GInf E s) : ℝ := ℓ + H p.1.1 - H (p.1.1 * p.2.1 * p.2.2)
  have h_sum (p : G E s × GInf E s × GInf E s) :
      ℓ * P p = a₁ p * P p + a₂ p * P p + a₃ p * P p := by
    simp [a₁, a₂, a₃, ← add_mul]
  have one_le (y : GInf E s) : 1 ≤ ∏ w, ‖(y w).val.val‖ := (le_prod_opNorm y).1
  have h₀ : Integrable P m := by
    simpa using V.integrable_mul_tripleKernel hB φ he hγ (a := 1) measurable_one
      fun _ y u ↦ abs_one.trans_le (one_le_mul_of_one_le_of_one_le (one_le y) (one_le u))
  have h₁ : Integrable (fun p ↦ a₁ p * P p) m :=
    V.integrable_mul_tripleKernel hB φ he hγ (by fun_prop) fun x y u ↦
      (h_lip x.1 y).trans (le_mul_of_one_le_right (by positivity) (one_le u))
  have h₂ : Integrable (fun p ↦ a₂ p * P p) m :=
    V.integrable_mul_tripleKernel hB φ he hγ (by fun_prop) fun x y u ↦
      (h_lip (x.1 * y) u).trans (le_mul_of_one_le_left (by positivity) (one_le y))
  have h₁₂ : Integrable (fun p ↦ a₁ p * P p + a₂ p * P p) m := h₁.add h₂
  have h₃ : Integrable (fun p ↦ a₃ p * P p) m :=
    ((h₀.const_mul ℓ).sub h₁₂).congr (.of_forall fun p ↦ sub_eq_of_eq_add' (h_sum p))
  -- As `e ⋆ e = e`, the integral of `P` is `I_γ`, and that of `(a₁ + a₂) P` is that of `a₁ P`.
  have h_orb : ∫ p, P p ∂m = V.orbitalIntegral e φ γ := by
    rw [V.integral_tripleMeasure h₀ (.id _)]
    simp only [P, tripleKernel, id, integral_const_mul, integral_mul_const, he.convolution_self,
      orbitalIntegral, orbitalIntegrand]
  have h_add (p : G E s × GInf E s × GInf E s) : a₁ p * P p + a₂ p * P p =
      (H (p.1.1 * (p.2.1 * p.2.2)) - H p.1.1 : ℝ) * P p := by
    simp [a₁, a₂, mul_assoc, ← add_mul]
  have h_zero : ∫ p, a₂ p * P p ∂m = 0 := by
    rw [← add_eq_left (a := ∫ p, a₁ p * P p ∂m), ← integral_add h₁ h₂]
    simp only [h_add] at h₁₂ ⊢
    exact V.integral_mul_tripleKernel_mul φ he (b := fun x y ↦ H (x.1 * y) - H x.1) h₁₂ h₁
  -- The rotation carries `a₁` to `a₂` and `a₂` to `a₃`, so the three integrals agree.
  have h_incr {t : U V.J} (ht : Commute γ t) (a b : GInf E s) :
      H ((V.ratEmbed t).1 * a) - H ((V.ratEmbed t).1 * b) = H a - H b := by
    obtain ⟨r, hr⟩ := h_cent t ht
    simp [hr]
  have h₂₁ : ∫ p, a₂ p * P p ∂m = ∫ p, a₁ p * P p ∂m :=
    V.integral_mul_tripleKernel_tripleRotate φ h_meas (by fun_prop) h₁ h₂ (fun p ↦ rfl)
      fun t ht x q ↦ by simp only [a₁, Prod.fst_mul, mul_assoc, h_incr ht]
  have h₃₂ : ∫ p, a₃ p * P p ∂m = ∫ p, a₂ p * P p ∂m :=
    V.integral_mul_tripleKernel_tripleRotate φ h_meas (by fun_prop) h₂ h₃
      (fun p ↦ by simp [a₂, a₃, tripleRotate, mul_assoc, h_shift])
      fun t ht x q ↦ by simp only [a₂, Prod.fst_mul, mul_assoc, h_incr ht]
  calc ℓ * V.orbitalIntegral e φ γ
      = ∫ p, a₁ p * P p + a₂ p * P p + a₃ p * P p ∂m := by
        simp only [← h_orb, ← integral_const_mul, h_sum]
    _ = 0 := by rw [integral_add h₁₂ h₃, integral_add h₁ h₂, h₃₂, ← h₂₁, h_zero, add_zero, add_zero]

/-- The Selberg principle: let `e` be a cusp kernel of order `B ≥ 13 n ^ 3`. If the characteristic
polynomial of the rational point `γ` is irreducible and its `i`-th complex root (`numberedRoots`)
under the embedding `Φ w` at the infinite place `w` lies off the unit circle, then the orbital
integral of `e ⊗ φ` at `γ` is zero. -/
theorem orbitalIntegral_eq_zero [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) (he : IsCuspKernel B e) {γ : U V.J}
    (hγ : Irreducible (γ : GL n E).val.charpoly) {w : InfinitePlace E} {i : n}
    (h_root : ‖numberedRoots (Φ w) (γ : GL n E).val.charpoly i‖ ≠ 1) :
    V.orbitalIntegral e φ γ = 0 := by
  -- Let `ℓ ≠ 0` be the logarithm of the modulus of the root, and `H y` the logarithm of the norm
  -- of the `i`-th row of `k y`, with `k` diagonalising `γ` at `w`. Then `H (γ y) = ℓ + H y`.
  let A : Matrix n n ℂ := ((V.ratEmbed γ).1 w).val.val
  let d : n ↪ ℂ := numberedRoots (Φ w) γ.val.val.charpoly
  obtain ⟨k, hk⟩ : ∃ k : (Matrix n n ℂ)ˣ, SemiconjBy k.val A (diagonal d) := by
    refine IsConj.symm (isConj_diagonal_of_isRoot_charpoly fun j ↦ ?_)
    have hA : A = (V.x.map (evalInf w))⁻¹.val * γ.val.val.map (Φ w) * (V.x.map (evalInf w)).val :=
      V.coe_ratEmbed_fst γ w
    rw [hA, charpoly_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
    exact isRoot_numberedRoots hγ.separable (Φ w) j
  let Q : Matrix n n ℂ := diagonal (Pi.single i 1) * k.val
  have hQ_ne : Q ≠ 0 := by simp [Q]
  let H (y : GInf E s) : ℝ := ‖Q * (y w).val.val‖.log
  have hQ_mul (y : GInf E s) : Q * (y w).val.val ≠ 0 := (y w).val.isUnit.mul_left_eq_zero.ne.2 hQ_ne
  -- An element that multiplies `Q` by a scalar `m` shifts `H` by `log ‖m‖`.
  have h_ne {t : GInf E s} {m : ℂ} (ht : Q * (t w).val.val = m • Q) : m ≠ 0 :=
    fun h ↦ hQ_mul t (by rw [ht, h, zero_smul])
  have hH {t : GInf E s} {m : ℂ} (ht : Q * (t w).val.val = m • Q) (y : GInf E s) :
      H (t * y) = ‖m‖.log + H y := by
    have h_mul : Q * ((t * y) w).val.val = m • (Q * (y w).val.val) := by
      simp [← smul_mul_assoc, ← ht, mul_assoc]
    simp only [H, h_mul, norm_smul]
    exact Real.log_mul (norm_ne_zero_iff.2 (h_ne ht)) (norm_ne_zero_iff.2 (hQ_mul y))
  have hQ {t : Matrix n n ℂ} (ht : Commute t A) : Q * t = (k * t * k⁻¹.val) i i • Q :=
    row_mul_eq_smul_of_commute hk ht i
  have hQA : Q * A = d i • Q := by simpa [hk.eq] using hQ (.refl A)
  have hℓ : (‖d i‖.log : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 (h_ne hQA)) h_root)
  have h_lip (a b : GInf E s) : |H (a * b) - H a| ≤ ∏ v, ‖(b v).val.val‖ :=
    (abs_log_norm_mul_sub_le hQ_ne w a b).trans ((le_prod_opNorm b).2 w)
  have h_cent (t : U V.J) (ht : Commute γ t) :
      ∃ r : ℝ, ∀ y, H ((V.ratEmbed t).1 * y) = r + H y := by
    have h_comm : Commute ((V.ratEmbed t).1 w).val.val A :=
      congrArg (fun g : G E s ↦ (g.1 w).val.val) (ht.map V.ratEmbed).symm.eq
    exact ⟨_, hH (hQ h_comm)⟩
  have h_mul_zero : (‖d i‖.log : ℂ) * V.orbitalIntegral e φ γ = 0 :=
    V.mul_orbitalIntegral_eq_zero hB φ he hγ (by fun_prop) h_lip (hH hQA) h_cent
  exact (mul_eq_zero.1 h_mul_zero).resolve_left hℓ

/-- An irreducible polynomial `R` whose `i`-th complex root at the infinite place `w` lies off the
unit circle does not contribute to the geometric side for `e ⊗ φ` (the integral over `Γ \ G` of the
terms of the rational points with characteristic polynomial `R` is zero). Here `e` is a cusp kernel
of order `B ≥ 13 n ^ 3`. -/
theorem geometricSide_singleton_eq_zero_of_norm_ne_one [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) (he : IsCuspKernel B e) {R : E[X]} (hR : Irreducible R)
    {w : InfinitePlace E} {i : n} (h_root : ‖numberedRoots (Φ w) R i‖ ≠ 1) :
    V.geometricSide hB he {R} φ = 0 := by
  have h_class (c : FrameClass E n) : V.classIntegral e φ R c = 0 := by
    by_contra hc
    obtain ⟨γ, rfl, rfl⟩ := V.exists_frameClass_eq_of_classIntegral_ne_zero hc
    rw [(V.orbitalIntegral_unfold hB φ he.decay he.continuous.measurable hR).2] at hc
    exact hc (V.orbitalIntegral_eq_zero hB φ he hR h_root)
  refine (V.hasSum_classIntegral hB φ he.decay he.continuous.measurable hR).unique ?_
  rw [_root_.funext h_class]
  exact hasSum_zero

/-! ### All roots on the unit circle -/

/-- A rational point `γ` is an elliptic similitude of `V.J` with multiplier `1` if its
characteristic polynomial is irreducible with all complex roots on the unit circle. -/
lemma isEllipticSimilitude_of_norm_eq_one {γ : U V.J} (hγ : Irreducible (γ : GL n E).val.charpoly)
    (h_norm : ∀ (w : InfinitePlace E) (i : n),
      ‖numberedRoots (Φ w) (γ : GL n E).val.charpoly i‖ = 1) :
    IsEllipticSimilitude 1 γ V.J := by
  refine ⟨hγ, one_ne_zero, by simpa [star_eq_conjTranspose] using mem_unitaryGroupOf_iff.1 γ.2,
    fun w r hr ↦ ?_⟩
  rw [roots_eq_map_numberedRoots hγ.separable] at hr
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hr
  simp [mul_conj', h_norm]

/-- Splitting of an orbital integral into real and finite factors, for the product
`typeKernel l s` of the discrete series kernels of parameters `l w`. Let the rational point `γ` be
conjugate by `g` to `(t, y)`, and let `β` be a function on `G_f` such that `x ↦ β (g⁻¹ x)_f` is a
cutoff (a weight of sum one on each orbit) for the rational centraliser of `γ`. Then `I_γ` is the
product of the real orbital integrals at the `t w` and the finite orbital integral at `y`, which is
written with `β`. -/
theorem orbitalIntegral_eq_prod_mul (φ : TestFunction (Gf E n)) {l : InfinitePlace E → n → ℤ}
    (hl : Measurable (typeKernel l s)) {γ : U V.J} {g : G E s} {t : GInf E s} {y : Gf E n}
    (hγ : V.ratEmbed γ = g * (t, y) * g⁻¹) {β : Gf E n → ℝ≥0∞}
    (hβ : IsCutoff (Measure.count : Measure ((centralizer {γ}).map V.ratEmbed))
      fun x : G E s ↦ β (g⁻¹ * x).2) :
    V.orbitalIntegral (typeKernel l s) φ γ =
      (∏ w : InfinitePlace E, ∫ h : USign s, (toHCParam s (l w)).dsKernel (h⁻¹ * t w * h)) *
        ∫ v : Gf E n, (β v).toReal • (φ : Gf E n → ℂ) (v⁻¹ * y * v) := by
  -- Insert the cutoff, translate by `g`, and split `G` into its real and finite parts.
  rw [orbitalIntegral,
    hβ.integral_orbitMeasure (fun u ↦ V.fixesLeft_orbitalIntegrand (typeKernel l s) φ γ _ u.2)
      (V.measurable_orbitalIntegrand hl φ γ),
    ← integral_fintype_prod_eq_prod, ← integral_prod_mul, ← integral_mul_left_eq_self _ g]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [typeKernel, orbitalIntegrand, hγ, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left,
    Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv, Pi.mul_apply, Pi.inv_apply,
    mul_smul_comm]

/-- Let `y` be an elliptic isometry (multiplier `1`) of a form with Gram matrix `1` in the finite
frame `x` and the sign `s i` on the eigenline of the root `z w (σ w i)`. Then there is a space of
signs `s` with finite frame `x` in which `y` is an isometry, with real component
`diag(z w ∘ σ w)` at each place `w`. -/
lemma exists_ratEmbed_eq_diagTorus {x : GL n (𝔸f E)} {y : GL n E} {σ : InfinitePlace E → Perm n}
    (hx : HasSignType (fun w : InfinitePlace E ↦ s ∘ (σ w).symm) 1 y {1} x)
    {z : InfinitePlace E → n ↪ Circle}
    (hz : ∀ (w : InfinitePlace E) (i : n), (z w i : ℂ) = numberedRoots (Φ w) y.val.charpoly i) :
    ∃ W : Space E n s, W.xFin = x ∧
      ∃ hy : y ∈ U W.J, ∀ w : InfinitePlace E,
        (W.ratEmbed ⟨y, hy⟩).1 w = diagTorus s (z w ∘ σ w) := by
  obtain ⟨β, h_ell, h_frame, h_pos⟩ := hx
  -- At each infinite place an eigenbasis of `y`, in the order `σ w`, has Gram matrix
  -- `signMatrix s`.
  have h_basis (w : InfinitePlace E) : ∃ k : GL n ℂ, k.valᴴ * β.map (Φ w) * k = signMatrix s ∧
      k⁻¹.1 * y.1.map (Φ w) * k = diagonal fun i ↦ numberedRoots (Φ w) y.1.charpoly (σ w i) := by
    obtain ⟨k, d, -, h_pos_iff, h_signs⟩ := exists_eigenbasis_diag_form h_ell w (σ w)
    have h_sign (i : n) : 0 < d i * s i := by
      simpa only [eval_interpolate_univ_node, Function.comp_apply, symm_apply_apply]
        using (h_pos_iff _).1 (h_pos w) i
    exact h_signs s h_sign
  choose k h_gram h_eigen using h_basis
  let W : Space E n s :=
    { J := β
      x := mkAdelicGL (k, x)
      gram_point := gram_mkAdelicGL h_gram h_frame }
  have hy : y ∈ U β := by
    simpa [mem_unitaryGroupOf_iff, star_eq_conjTranspose] using h_ell.conjTranspose_mul_mul
  refine ⟨W, rfl, hy, fun w ↦ ?_⟩
  have h_point : W.x.map (evalInf w) = k w := rfl
  have h_torus : (diagTorus s (z w ∘ σ w)).val.val =
      diagonal fun i ↦ numberedRoots (Φ w) y.val.charpoly (σ w i) := by
    simp only [← hz]
    rfl
  ext : 2
  rw [h_torus, coe_ratEmbed_fst, h_point, h_eigen w]

/-- If the finite frames of two spaces conjugate the rational centraliser of `y` in the same way,
then the image in `G_f` of the centraliser of `y` in the first unitary group lies in that for the
second. -/
lemma map_embFin_centralizer_le {s' : n → ℤˣ} (W : Space E n s') {y : GL n E} (hy : y ∈ U V.J)
    (hy' : y ∈ U W.J) (h_conj : ∀ a : GL n E, Commute y a →
      V.xFin⁻¹ * toFinGL a * V.xFin = W.xFin⁻¹ * toFinGL a * W.xFin) :
    (centralizer {⟨y, hy⟩}).map V.embFin ≤ (centralizer {⟨y, hy'⟩}).map W.embFin := by
  rintro _ ⟨⟨a, ha⟩, h_cent, rfl⟩
  have h_comm : Commute y a := (Subtype.ext_iff.1 (mem_centralizer_singleton_iff.1 h_cent)).symm
  -- `a` is an isometry of `V` or `W` exactly if its conjugate by the frame is unitary.
  have ha' : a ∈ U W.J := by
    rw [mem_unitaryGroupOf_iff, star_eq_conjTranspose, ← W.mem_U_one_iff_gram_eq gram_xFin,
        ← h_conj a h_comm,
      V.mem_U_one_iff_gram_eq gram_xFin]
    exact mem_unitaryGroupOf_iff.1 ha
  refine ⟨⟨a, ha'⟩, mem_centralizer_singleton_iff.2 (Subtype.ext h_comm.symm), ?_⟩
  simp [Gf.val_ext_iff, coe_embFin, h_conj a h_comm]

/-- If the finite frames of two spaces conjugate the rational centraliser of `y` in the same way,
then the centralisers of `y` in the two unitary groups have the same image in `G_f`. -/
lemma map_embFin_centralizer_eq {s' : n → ℤˣ} (W : Space E n s') {y : GL n E} (hy : y ∈ U V.J)
    (hy' : y ∈ U W.J) (h_conj : ∀ a : GL n E, Commute y a →
      V.xFin⁻¹ * toFinGL a * V.xFin = W.xFin⁻¹ * toFinGL a * W.xFin) :
    (centralizer {⟨y, hy⟩}).map V.embFin = (centralizer {⟨y, hy'⟩}).map W.embFin :=
  (V.map_embFin_centralizer_le W hy hy' h_conj).antisymm
    (W.map_embFin_centralizer_le V hy' hy fun a ha ↦ (h_conj a ha).symm)

/-- The inverse of a group isomorphism `f` maps the centraliser of `f a` onto that of `a`. -/
lemma map_symm_centralizer_singleton {M N : Type*} [Group M] [Group N] (f : M ≃* N) (a : M) :
    (centralizer {f a}).map f.symm.toMonoidHom = centralizer {a} := by
  ext b
  rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    MulEquiv.symm_symm, commute_map_iff f.injective]

/-- Let `E` contain the 5040th roots of unity. Let `y` be an elliptic isometry of a positive form
with orthonormal finite frame `u` (`HasSignType 1 1 y {1} u`), and let `z w` list the roots of its
characteristic polynomial at the place `w`. There is a number `c`, the finite orbital integral of
`φ`, with the following property. Suppose `typeKernel l s`, the product over `w` of the discrete
series kernels `dsKernel` for the parameters `l w`, is a cusp kernel of order `B ≥ 13 n ^ 3`.
Suppose `y` is an elliptic isometry of a form with orthonormal finite frame `x` and signs `s` at the
roots in the order `σ`. Suppose also that `x` conjugates the rational centraliser of `y` as `u`
does. Then on a space `V` of signs `s`, `V.classIntegral` of the class of `(x, y)` is `c` times the
product over `w` of the integrals over `U(diag s)` of `dsKernel` at conjugates of
`diag(z w ∘ σ w)`. -/
theorem exists_classIntegral_eq [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) [HasPrimitiveRoot5040 E] {u : GL n (𝔸f E)} {y : GL n E}
    (hu : HasSignType 1 1 y {1} u) {z : InfinitePlace E → n ↪ Circle}
    (hz : ∀ (w : InfinitePlace E) (i : n), (z w i : ℂ) = numberedRoots (Φ w) y.val.charpoly i) :
    ∃ c : ℂ, ∀ {s : n → ℤˣ} (V : Space E n s) {l : InfinitePlace E → n → ℤ}
      {σ : InfinitePlace E → Perm n} {x : GL n (𝔸f E)}, IsCuspKernel B (typeKernel l s) →
      HasSignType (fun w : InfinitePlace E ↦ s ∘ (σ w).symm) 1 y {1} x →
      (∀ a : GL n E, Commute y a → u⁻¹ * toFinGL a * u = x⁻¹ * toFinGL a * x) →
      V.classIntegral (typeKernel l s) φ y.val.charpoly (frameClass (x, y)) =
        (∏ w : InfinitePlace E, ∫ h : USign s,
          (toHCParam s (l w)).dsKernel (h⁻¹ * diagTorus s (z w ∘ σ w) * h)) * c := by
  -- The constant is the finite orbital integral in the definite space `W₀` with frame `u`.
  obtain ⟨W₀, rfl, hy₀, -⟩ := exists_ratEmbed_eq_diagTorus (s := 1) (σ := 1) hu hz
  -- The centraliser is cut with `W₀.Γf`, which contains it, so that it is seen to be discrete.
  obtain ⟨β, hβ_meas, hβ⟩ : ∃ β : Gf E n → ℝ≥0∞, IsCutoff
      (Measure.count : Measure ↥(W₀.Γf ⊓ (centralizer {⟨y, hy₀⟩}).map W₀.embFin)) β :=
    (hasCutoff_count _).out
  refine ⟨∫ v, (β v).toReal • φ.val (v⁻¹ * W₀.embFin ⟨y, hy₀⟩ * v),
    fun {s} V l σ x he hx same_conj ↦ ?_⟩
  -- `W` is a space of signs `s` with frame `x` in which `y` is diagonal at infinity.
  obtain ⟨W, rfl, hy, h_diag⟩ := exists_ratEmbed_eq_diagTorus hx hz
  -- Landherr: `b` is a rational isometry from `W.J` to `V.J`, and conjugation by `b` becomes
  -- conjugation by `g ∈ G` under the embeddings.
  obtain ⟨b, g, hb, -, emb_conj⟩ := V.exists_x_eq_and_ratEmbed_conj_eq W
  set conj : U W.J ≃* U V.J := U.conj b hb
  let γ : U V.J := conj ⟨y, hy⟩
  have class_eq : frameClass (V.xFin, γ.val) = frameClass (W.xFin, y) :=
    frameClass_eq_iff.2 ⟨b, (V.mem_U_one_iff_gram_eq gram_xFin).2 hb, rfl⟩
  -- By `same_conj`, `y` and its centraliser have the same finite images for `W₀` and for `W`.
  have embf_eq : W₀.embFin ⟨y, hy₀⟩ = W.embFin ⟨y, hy⟩ := by
    simp [Gf.val_ext_iff, coe_embFin, same_conj]
  have centralizer_eq : W₀.Γf ⊓ (centralizer {⟨y, hy₀⟩}).map W₀.embFin =
      (centralizer {γ}).map (W.embFin.comp conj.symm) := by
    rw [inf_eq_right.2 (map_le_range _ _), W₀.map_embFin_centralizer_eq W hy₀ hy same_conj,
      ← map_symm_centralizer_singleton conj, Subgroup.map_map]
    rfl
  -- So `β` of the finite part of `g⁻¹ x` is a cutoff for the centraliser of `γ` in `V`.
  have cutoff : IsCutoff (Measure.count : Measure ((centralizer {γ}).map V.ratEmbed))
      fun x : G E s ↦ β (g⁻¹ * x).2 := by
    refine ⟨by fun_prop, fun x ↦ ?_⟩
    have emb_eq (a : U V.J) : V.ratEmbed a = g * W.ratEmbed (conj.symm a) * g⁻¹ := by
      rw [← emb_conj, MulEquiv.apply_symm_apply]
    rw [← hβ (g⁻¹ * x).2, centralizer_eq, lintegral_count, lintegral_count]
    calc _ = ∑' a : centralizer {γ}, β (g⁻¹ * (V.ratEmbed a * x)).2 :=
          tsum_image (fun t : G E s ↦ β (g⁻¹ * (t * x)).2) V.ratEmbed_injective.injOn
      _ = ∑' a : centralizer {γ}, β (W.embFin (conj.symm a) * (g⁻¹ * x).2) := by
          simp [embFin, mul_assoc, emb_eq]
      _ = ∑' t : (centralizer {γ}).map (W.embFin.comp conj.symm), β (t • (g⁻¹ * x).2) :=
          (tsum_image (fun t : Gf E n ↦ β (t * (g⁻¹ * x).2))
            (W.fact_embFin_injective.out.comp conj.symm.injective).injOn).symm
  have h_poly : γ.val.val.charpoly = y.val.charpoly := by simp [γ, conj]
  have h_irr : Irreducible γ.val.val.charpoly := by
    obtain ⟨_, h_ell, -⟩ := hu
    simpa only [h_poly] using h_ell.irreducible_charpoly
  have h_embed : V.ratEmbed γ =
      g * (fun w ↦ diagTorus s (z w ∘ σ w), W₀.embFin ⟨y, hy₀⟩) * g⁻¹ := by
    rw [emb_conj, embf_eq, ← _root_.funext h_diag]
    rfl
  have h_unfold : V.classIntegral (typeKernel l s) φ (γ : Matrix n n E).charpoly
      (frameClass (V.xFin, (γ : GL n E))) = V.orbitalIntegral (typeKernel l s) φ γ :=
    (V.orbitalIntegral_unfold hB φ he.decay he.continuous.measurable h_irr).2
  rw [← class_eq, ← h_poly, h_unfold,
    V.orbitalIntegral_eq_prod_mul φ he.continuous.measurable h_embed cutoff]

/-- Matching the classes. Let `E` contain the 5040th roots of unity, and let `ε`, `ε'` be families
of signs, each with product `1`. There is a permutation `f` of the classes of pairs (finite frame,
rational matrix) that carries those with polynomial `R` and signs `ε` onto those with polynomial
`R` and signs `ε'`. If `(u, y)` has the signs `ε` (`y` is an elliptic isometry, with the signs `ε`
on its eigenlines, of a form with orthonormal frame `u`), then `f` sends its class to the class of
a pair `(x, y)` with signs `ε'` such that `u` and `x` conjugate the rational centraliser of `y` in
the same way. -/
theorem exists_perm_signedClasses {ε ε' : InfinitePlace E → n → ℤˣ}
    (hε : ∏ w : InfinitePlace E, ∏ i : n, ε w i = 1)
    (hε' : ∏ w : InfinitePlace E, ∏ i : n, ε' w i = 1) (R : E[X]) :
    ∃ f : Perm (FrameClass E n), f '' signedClasses R ε = signedClasses R ε' ∧
      ∀ (u : GL n (𝔸f E)) (y : GL n E) (_hu : HasSignType ε 1 y {1} u),
        ∃ x : GL n (𝔸f E), HasSignType ε' 1 y {1} x ∧
          f (frameClass (u, y)) = frameClass (x, y) ∧
          ∀ a : GL n E, Commute y a → u⁻¹ * toFinGL a * u = x⁻¹ * toFinGL a * x := by
  -- The frame is moved by an adelic matrix `Z y` that commutes with the centraliser of `y` and
  -- changes the signs by `ε / ε'`.
  have h_prod : ∏ w, ∏ i, (ε'⁻¹ * ε) w i = 1 := by simp [prod_mul_distrib, hε, hε']
  obtain ⟨f, hf⟩ := exists_hasSignType_mul_iff (fun _ : Unit ↦ ε'⁻¹ * ε) (fun _ ↦ h_prod) (U 1)
  have h_move (y : GL n E) : ∃ Z : GL n (𝔸f E),
      (∀ u, HasSignType ε 1 y {1} u ↔ HasSignType ε' 1 y {1} (Z * u)) ∧
      (∀ a, Commute y a → Commute (toFinGL a) Z) ∧
      ∀ u, f (frameClass (u, y)) = frameClass (Z * u, y) := by
    obtain ⟨Z, h_sign, h_comm, h_map⟩ := hf y ()
    refine ⟨Z, fun u ↦ ?_, h_comm, fun u ↦ h_map ⟦u⟧⟩
    simpa using h_sign 1 ε' {1} u
  choose Z h_iff h_comm h_class using h_move
  refine ⟨f, Set.Subset.antisymm ?_ ?_, fun u y hu ↦
    ⟨Z y * u, (h_iff y u).1 hu, h_class y u, fun a ha ↦ ?_⟩⟩
  · rintro _ ⟨_, ⟨u, y, hy, hu, rfl⟩, rfl⟩
    exact ⟨Z y * u, y, hy, (h_iff y u).1 hu, (h_class y u).symm⟩
  · rintro _ ⟨x, y, hy, hx, rfl⟩
    exact ⟨_, ⟨(Z y)⁻¹ * x, y, hy, (h_iff y _).2 (by simpa using hx), rfl⟩, by simp [h_class]⟩
  · simp only [_root_.mul_inv_rev, mul_assoc, (h_comm y a ha).left_comm, inv_mul_cancel_left]

omit [DecidableEq n] in
/-- If the number of infinite places is even, a family of signs that is a rearrangement of the same
`s` at each place has product `1`. -/
lemma prod_prod_comp_symm_eq_one (hE : Even (Core.numInfPlaces E)) (s : n → ℤˣ)
    (σ : InfinitePlace E → Perm n) :
    ∏ w : InfinitePlace E, ∏ i : n, (s ∘ (σ w).symm) i = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, card (InfinitePlace E) = m + m := hE
  have h_place (w : InfinitePlace E) : ∏ i, (s ∘ (σ w).symm) i = ∏ i, s i := (σ w).symm.prod_comp s
  simp only [h_place, prod_const, card_univ, hm, pow_add, Int.units_mul_self]

/-- Let `E` contain the 5040th roots of unity and have an even number of infinite places, and let
`z` be the numbered roots of `R`, on the unit circle. There is a number `c` with the following
property. On every space, suppose the product `typeKernel l s` of the discrete series kernels is a
cusp kernel of order `B ≥ 13 n ^ 3`. Then the contributions of the classes with polynomial `R` and
signs `s` in the order `σ` of the roots add up to the product of the real orbital integrals times
`c`. These classes are `signedClasses`: classes of pairs `(x, y)` with `y` an elliptic isometry of
characteristic polynomial `R`, with those signs on its eigenlines, of a form for which `x` is an
orthonormal frame. -/
theorem exists_tsum_signedClasses_eq [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) [HasPrimitiveRoot5040 E] (hE : Even (Core.numInfPlaces E))
    {R : E[X]} {z : InfinitePlace E → n ↪ Circle}
    (hz : ∀ (w : InfinitePlace E) (i : n), (z w i : ℂ) = numberedRoots (Φ w) R i) :
    ∃ c : ℂ, ∀ {s : n → ℤˣ} (V : Space E n s) {l : InfinitePlace E → n → ℤ},
      IsCuspKernel B (typeKernel l s) → ∀ σ : InfinitePlace E → Perm n,
      ∑' a : signedClasses R fun w : InfinitePlace E ↦ s ∘ (σ w).symm,
          V.classIntegral (typeKernel l s) φ R a =
        (∏ w : InfinitePlace E, ∫ h : USign s,
          (toHCParam s (l w)).dsKernel (h⁻¹ * diagTorus s (z w ∘ σ w) * h)) * c := by
  -- Match the classes with those of signs `1`, and add up their finite orbital integrals `C a`.
  have h_repr (a : signedClasses (n := n) R 1) : ∃ (u : GL n (𝔸f E)) (y : GL n E),
      y.val.charpoly = R ∧ HasSignType 1 1 y {1} u ∧ frameClass (u, y) = a := a.property
  choose u y h_poly h_sign h_rep using h_repr
  choose C hC using fun a ↦
    exists_classIntegral_eq hB φ (h_sign a) (z := z) (by simpa only [h_poly] using hz)
  refine ⟨∑' a, C a, fun {s} V l he σ ↦ ?_⟩
  obtain ⟨f, h_image, hf⟩ :=
    exists_perm_signedClasses (ε := 1) (by simp) (prod_prod_comp_symm_eq_one hE s σ) R
  rw [← h_image, tsum_image _ f.injective.injOn, ← tsum_mul_left]
  refine tsum_congr fun a ↦ ?_
  obtain ⟨x, hx, h_class, h_conj⟩ := hf (u a) (y a) (h_sign a)
  rw [← h_rep, h_class, ← hC a V he hx h_conj, h_poly]

/-- The class of an elliptic rational point `γ` has the signs `ε` exactly if the form of `V` has
these signs on the eigenlines of `γ`: at each infinite place `w` the matrix `V.J p(γ)` is positive
definite, where `p` takes the value `ε w i` at the `i`-th root. -/
lemma frameClass_mem_signedClasses_iff {γ : U V.J} (hγ : IsEllipticSimilitude 1 γ V.J)
    (ε : InfinitePlace E → n → ℤˣ) :
    frameClass (V.xFin, (γ : GL n E)) ∈ signedClasses (γ : GL n E).val.charpoly ε ↔
      ∀ w : InfinitePlace E,
        (V.J.map (Φ w) * aeval ((γ : GL n E).val.map (Φ w)) (Lagrange.interpolate univ
          (numberedRoots (Φ w) (γ : GL n E).val.charpoly) fun i : n ↦ (ε w i : ℂ))).PosDef := by
  refine ⟨?_, fun h_pos ↦ ⟨V.xFin, γ, rfl, ⟨V.J, hγ, by simp [gram_xFin], h_pos⟩, rfl⟩⟩
  rintro ⟨x, a, h_poly, ⟨β, -, h_frame, h_pos⟩, h_class⟩ w
  -- The rational matrix `g` that identifies the classes carries `V.J` to the form `β` of `a`.
  obtain ⟨g, hg, hgγ⟩ : ∃ g : GL n E, V.xFin⁻¹ * toFinGL g * x ∈ U 1 ∧ g * a * g⁻¹ = γ :=
    frameClass_eq_iff.1 h_class.symm
  obtain rfl : g.valᴴ * V.J * g.val = β := (V.mem_U_one_iff_gram_eq h_frame).1 hg
  -- Conjugation by `g` keeps positivity and turns the polynomial in `γ` into that in `a`.
  have h_conj : SemiconjBy (g.map (Φ w)).val (a.val.map (Φ w)) (γ.val.val.map (Φ w)) := by
    simp [SemiconjBy, ← hgγ, ← Matrix.map_mul]
  have h_form : (g.valᴴ * V.J * g.val).map (Φ w) =
      star (g.map (Φ w)).val * V.J.map (Φ w) * (g.map (Φ w)).val :=
    map_conjTranspose_mul_mul (Φ w) (by simp) g.val V.J
  rw [← (g.map (Φ w)).isUnit.posDef_star_left_conjugate_iff, mul_assoc, mul_assoc,
    ← aeval_semiconj h_conj, ← h_poly, ← mul_assoc, ← mul_assoc, ← h_form]
  exact h_pos w

/-- At the infinite place `w` the frame `V.x` carries the form `V.J` to the diagonal matrix of the
signs `s`. -/
lemma gram_map_evalInf (w : InfinitePlace E) :
    (V.x.map (evalInf w)).valᴴ * V.J.map (Φ w) * (V.x.map (evalInf w)).val = signMatrix s := by
  have h_map : (V.x.valᴴ * V.J.map toAdele * V.x.val).map (evalInf w) = signMatrix s := by
    simp [V.gram_point, stdForm, signMatrix]
  rwa [map_conjTranspose_mul_mul (evalInf w) fun _ ↦ rfl, Matrix.map_map] at h_map

/-- Let `γ` be an elliptic rational point of `V`. For a permutation `σ` take the polynomial with
value `s (σ⁻¹ i)` at the `i`-th eigenvalue of `γ` at `w`. The `σ` for which `V.J` times this
polynomial in `γ` is positive definite are as many as those that fix `s`. -/
lemma card_perm_posDef {γ : U V.J} (hγ : IsEllipticSimilitude 1 γ V.J) (w : InfinitePlace E) :
    Nat.card {σ : Perm n //
      (V.J.map (Φ w) * aeval ((γ : GL n E).val.map (Φ w)) (Lagrange.interpolate univ
        (numberedRoots (Φ w) (γ : GL n E).val.charpoly) fun i : n ↦ s (σ.symm i))).PosDef} =
      #{σ : Perm n | s ∘ σ = s} := by
  classical
  -- In an eigenbasis `k` of `γ` the form is `diagonal d`, and positivity is read off from `d`.
  obtain ⟨k, d, hd, h_pos, h_basis⟩ := exists_eigenbasis_diag_form hγ w 1
  have h_frame : (V.x.map (evalInf w))⁻¹.valᴴ * signMatrix s * (V.x.map (evalInf w))⁻¹.val =
      V.J.map (Φ w) := gram_inv_of_gram_eq (V.gram_map_evalInf w)
  -- The form is hermitian and invertible, so the `d i` are real and nonzero; `ε i` is their sign.
  obtain ⟨g, hg⟩ : ∃ g : GL n ℂ, g.valᴴ * diagonal (fun i ↦ (s i : ℂ)) * g.val = diagonal d :=
    ⟨_, gram_mul_of_gram_eq h_frame hd⟩
  have hd_unit : IsUnit (diagonal d) := by simp [← hg, Pi.isUnit_iff]
  have hd_herm : (diagonal d)ᴴ = diagonal d := by simp [← hg, Pi.star_def, mul_assoc]
  have hd_im (i : n) : (d i).im = 0 := conj_eq_iff_im.1 (by simpa using congrFun₂ hd_herm i i)
  have hd_re (i : n) : (d i).re ≠ 0 := fun h ↦
    ((isUnit_diagonal.1 hd_unit).apply i).ne_zero (Complex.ext h (hd_im i))
  let ε (i : n) : ℤˣ := if 0 < d i then 1 else -1
  have h_sign (i : n) (u : ℤˣ) : 0 < d i * u ↔ ε i = u := by
    rcases Int.units_eq_one_or u with rfl | rfl
    · simp [ε]
    · simp [ε, Complex.lt_def, (hd_re i).le_iff_lt, hd_im i]
  -- By Sylvester's law `ε` is a rearrangement `s ∘ τ` of `s`.
  obtain ⟨k', hk', -⟩ := h_basis ε fun i ↦ (h_sign i _).2 rfl
  obtain ⟨τ, hτ⟩ : ∃ τ : Perm n, ∀ i, s (τ i) = ε i :=
    sylvester_law_of_inertia (gram_mul_of_gram_eq h_frame hk')
  -- `σ` counts on the left iff `s ∘ σ⁻¹ = ε = s ∘ τ`, that is, iff `τ σ` fixes `s`.
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (subtypeEquiv (.mulLeft τ) fun σ ↦ ?_)
  rw [h_pos, σ.surjective.forall]
  simp only [Perm.coe_one, id, eval_interpolate_univ_node, h_sign, symm_apply_apply, ← hτ]
  exact funext_iff.symm

/-- The class of an elliptic rational point `γ` has the signs `s` in as many orders `σ` of the roots
as there are families, indexed by the infinite places, of permutations that fix `s`. -/
lemma card_mem_signedClasses {γ : U V.J} (hγ : IsEllipticSimilitude 1 γ V.J) :
    Nat.card {σ : InfinitePlace E → Perm n // frameClass (V.xFin, (γ : GL n E)) ∈
      signedClasses (γ : GL n E).val.charpoly fun w : InfinitePlace E ↦ s ∘ (σ w).symm} =
      ∏ _ : InfinitePlace E, #{σ : Perm n | s ∘ σ = s} := by
  simp only [V.frameClass_mem_signedClasses_iff hγ, Function.comp_apply]
  -- The condition is one condition on `σ w` for each place `w`.
  rw [← _root_.funext (V.card_perm_posDef hγ), ← Nat.card_pi, ← Nat.card_congr subtypePiEquivPi]

/-- Let the doubled Harish-Chandra parameters `l w` have gap at least `500 n³ + 10 n⁵` and let `z w`
be regular points of the compact torus. The sum over all orders `σ` of the products of the real
orbital integrals of the discrete series kernels is the number of families of permutations that fix
`s` times the product of the conjugate characters of the compact group `U(n)` at the `z w`. The
signs in Harish-Chandra's formula cancel because the number of infinite places is even. -/
lemma sum_prod_integral_dsKernel [Nonempty n] (hE : Even (Core.numInfPlaces E))
    {l : InfinitePlace E → n → ℤ}
    (h_gap : ∀ w : InfinitePlace E, (toHCParam s (l w)).HasLargeGap (10 * card n ^ 5))
    (z : InfinitePlace E → n ↪ Circle) :
    ∑ σ : InfinitePlace E → Perm n, ∏ w : InfinitePlace E, ∫ h : USign s,
        (toHCParam s (l w)).dsKernel (h⁻¹ * diagTorus s (z w ∘ σ w) * h) =
      (∏ _ : InfinitePlace E, #{σ : Perm n | s ∘ σ = s} : ℕ) *
        ∏ w : InfinitePlace E,
          star ((toHCParam 1 (l w)).lowestKType.kTypeChar (diagTorusK (z w))) := by
  let I (w : InfinitePlace E) (σ : Perm n) : ℂ :=
    ∫ h : USign s, (toHCParam s (l w)).dsKernel (h⁻¹ * diagTorus s (z w ∘ σ) * h)
  let ε : ℂ := (-1) ^ #(Orbital.oppositePairs s)
  have h_place (w : InfinitePlace E) : ε * ∑ σ, I w σ = #{σ : Perm n | s ∘ σ = s} *
      star ((toHCParam 1 (l w)).lowestKType.kTypeChar (diagTorusK (z w))) :=
    (Orbital.harish_chandra_degree_and_orbital (h_gap w)).2 (z w) (z w).injective
  have h_sign : ∏ _ : InfinitePlace E, ε = 1 := by
    rw [prod_const, ← pow_mul]
    exact (hE.mul_left _).neg_one_pow
  calc ∑ σ : InfinitePlace E → Perm n, ∏ w, I w (σ w)
      = ∏ w, ∑ σ, I w σ := (Fintype.prod_sum I).symm
    _ = ∏ w, ε * ∑ σ, I w σ := by rw [prod_mul_distrib, h_sign, one_mul]
    _ = _ := by simp only [h_place, prod_mul_distrib, Nat.cast_prod]

/-- Elliptic terms. Let `E` contain the 5040th roots of unity and have an even number of infinite
places, and let `R` be irreducible with all roots `z w i` on the unit circle. There is a number `c`,
independent of the space, its signs and `l`, such that for all parameters `l` with gap at least
`500 n³ + 10 n⁵` whose kernel is a cusp kernel of order `B ≥ 13 n ^ 3`, the integral over `Γ \ G` of
the terms with characteristic polynomial `R` is `c` times the product of the conjugate characters
of the compact group `U(n)`. -/
theorem exists_geometricSide_singleton_eq [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) [HasPrimitiveRoot5040 E] (hE : Even (Core.numInfPlaces E))
    {R : E[X]} (hR : Irreducible R) {z : InfinitePlace E → n ↪ Circle}
    (hz : ∀ (w : InfinitePlace E) (i : n), (z w i : ℂ) = numberedRoots (Φ w) R i) :
    ∃ c : ℂ, ∀ {s : n → ℤˣ} (V : Space E n s) {l : InfinitePlace E → n → ℤ}
      (he : IsCuspKernel B (typeKernel l s)),
      ∀ (_h_gap : ∀ w : InfinitePlace E, (toHCParam s (l w)).HasLargeGap (10 * card n ^ 5)),
      V.geometricSide hB he {R} φ =
        c * ∏ w : InfinitePlace E,
          star ((toHCParam 1 (l w)).lowestKType.kTypeChar (diagTorusK (z w))) := by
  classical
  obtain ⟨c, hc⟩ := exists_tsum_signedClasses_eq hB φ hE hz
  refine ⟨c, fun {s} V l he h_gap ↦ ?_⟩
  let I : FrameClass E n → ℂ := V.classIntegral (typeKernel l s) φ R
  let S (σ : InfinitePlace E → Perm n) : Set (FrameClass E n) :=
    signedClasses R fun w ↦ s ∘ (σ w).symm
  let N : ℕ := ∏ _ : InfinitePlace E, #{σ : Perm n | s ∘ σ = s}
  have hN : (N : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (prod_ne_zero_iff.2 fun _ _ ↦ card_ne_zero.2 ⟨1, by simp⟩)
  have h_sum : HasSum I (V.geometricSide hB he {R} φ) :=
    V.hasSum_classIntegral hB φ he.decay he.continuous.measurable hR
  -- A class that contributes lies in `S σ` for exactly `N` values of `σ`.
  have h_count (a : FrameClass E n) : ∑ σ, (S σ).indicator I a = N * I a := by
    by_cases ha : I a = 0
    · simp [Set.indicator, ha]
    obtain ⟨γ, rfl, rfl⟩ := V.exists_frameClass_eq_of_classIntegral_ne_zero ha
    have h_ell : IsEllipticSimilitude 1 γ V.J :=
      V.isEllipticSimilitude_of_norm_eq_one hR fun w i ↦ by rw [← hz, Circle.norm_coe]
    have h_card : #{σ | frameClass (V.xFin, γ.val) ∈ S σ} = N := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact V.card_mem_signedClasses h_ell
    simp only [Set.indicator, ← sum_filter, sum_const, nsmul_eq_mul, h_card]
  have h_parts : HasSum (fun a ↦ ∑ σ, (S σ).indicator I a) (∑ σ, ∑' a : S σ, I a) :=
    hasSum_sum fun σ _ ↦ hasSum_subtype_iff_indicator.1 (h_sum.summable.subtype (· ∈ S σ)).hasSum
  refine mul_left_cancel₀ hN ?_
  calc N * V.geometricSide hB he {R} φ
      = ∑ σ, ∑' a : S σ, I a := (h_sum.mul_left _).unique (by simpa only [h_count] using h_parts)
    _ = (∑ σ : InfinitePlace E → Perm n, ∏ w, ∫ h : USign s,
          (toHCParam s (l w)).dsKernel (h⁻¹ * diagTorus s (z w ∘ σ w) * h)) * c := by
        rw [sum_mul]
        exact sum_congr rfl fun σ _ ↦ hc V he σ
    _ = N * (c * ∏ w, star ((toHCParam 1 (l w)).lowestKType.kTypeChar (diagTorusK (z w)))) := by
        rw [sum_prod_integral_dsKernel hE h_gap z]
        ring

end Space

/-- Comparison of traces. Let the CM field `E` contain the 5040th roots of unity and have an even
number of infinite places, let `V`, `V'` be spaces of rank `n ≥ 2` over `E`, and let `l` be a family
of doubled Harish-Chandra parameters with gap at least `500 n³ + 10 n⁵` for the signs of both;
`typeKernel l s` is the product of their discrete series kernels. Let `K` be a level and `a` an
element of the group algebra of the finite adelic group. Suppose that the test function `a ⋆ 1_K`
is cuspidal at a split place `w`, and that the elements of its support are integral at `w'` with
`0` a simple root of the characteristic polynomial modulo `w'`. Then operators that act as `a` on
the forms of parameter `l` and level `K` on `V` and on `V'` have the same trace. -/
theorem trace_comparison [Nonempty n] [HasPrimitiveRoot5040 E] (hE : Even (Core.numInfPlaces E))
    (hn : 2 ≤ card n) {s s' : n → ℤˣ} (V : Space E n s) (V' : Space E n s')
    {l : InfinitePlace E → n → ℤ}
    (h_gap : ∀ v : InfinitePlace E, (toHCParam s (l v)).HasLargeGap (10 * card n ^ 5))
    (h_gap' : ∀ v : InfinitePlace E, (toHCParam s' (l v)).HasLargeGap (10 * card n ^ 5))
    {K : Subgroup (Gf E n)} [hK : IsLevel K] {a : MonoidAlgebra ℂ (Gf E n)} {w w' : FinPlace E}
    (hw : w.IsSplit) (h_cusp : IsCuspidalAt hw (convIndicator hK.isOpen hK.isCompact a))
    (h_simple : ∀ g : Gf E n, (convIndicator hK.isOpen hK.isCompact a : Gf E n → ℂ) g ≠ 0 →
      HasSimpleZero (g.atPlace w'))
    {T : End ℂ (levelSpace (V.formRep (typeKernel l s)) K)}
    (hT : ∀ y : levelSpace (V.formRep (typeKernel l s)) K,
      (T y).val = (V.formRep (typeKernel l s)).asAlgebraHom a y.val)
    {T' : End ℂ (levelSpace (V'.formRep (typeKernel l s')) K)}
    (hT' : ∀ y : levelSpace (V'.formRep (typeKernel l s')) K,
      (T' y).val = (V'.formRep (typeKernel l s')).asAlgebraHom a y.val) :
    LinearMap.trace ℂ (levelSpace (V.formRep (typeKernel l s)) K) T =
      LinearMap.trace ℂ (levelSpace (V'.formRep (typeKernel l s')) K) T' := by
  -- Up to `vol K` each trace is the geometric side, a sum over characteristic polynomials `R`.
  let φ : TestFunction (Gf E n) := convIndicator hK.isOpen hK.isCompact a
  have hB : 13 * card n ^ 3 ≤ 10 * card n ^ 5 := by
    nlinarith [Nat.mul_le_mul_left (card n ^ 3) (Nat.pow_le_pow_left hn 2)]
  have he : IsCuspKernel (10 * card n ^ 5) (typeKernel l s) := isCuspKernel_typeKernel h_gap
  have he' : IsCuspKernel (10 * card n ^ 5) (typeKernel l s') := isCuspKernel_typeKernel h_gap'
  -- The terms of each polynomial `R` agree: elliptic terms match, the others are zero.
  have h_term (R : E[X]) : V.geometricSide hB he {R} φ = V'.geometricSide hB he' {R} φ := by
    by_cases hR : Irreducible R
    · by_cases h_norm : ∀ (v : InfinitePlace E) (i : n), ‖numberedRoots (Φ v) R i‖ = 1
      · let z (v : InfinitePlace E) : n ↪ Circle :=
          (numberedRoots (Φ v) R).codRestrict _ fun i ↦ mem_sphere_zero_iff_norm.2 (h_norm v i)
        obtain ⟨c, hc⟩ := Space.exists_geometricSide_singleton_eq hB φ hE hR (z := z) fun _ _ ↦ rfl
        rw [hc V he h_gap, hc V' he' h_gap']
      · obtain ⟨v, i, h_root⟩ : ∃ v i, ‖numberedRoots (Φ v) R i‖ ≠ 1 := by simpa using h_norm
        rw [V.geometricSide_singleton_eq_zero_of_norm_ne_one hB φ he hR h_root,
          V'.geometricSide_singleton_eq_zero_of_norm_ne_one hB φ he' hR h_root]
    · rw [V.geometricSide_singleton_eq_zero hB he h_cusp h_simple hR,
        V'.geometricSide_singleton_eq_zero hB he' h_cusp h_simple hR]
  refine mul_left_cancel₀ (ofReal_ne_zero.2 (measureReal_pos_of_isLevel K).ne') ?_
  calc volume.real (K : Set (Gf E n)) * LinearMap.trace ℂ _ T
      = V.geometricSide hB he .univ φ := V.volume_mul_trace_eq hB he hT
    _ = ∑' R : E[X], V.geometricSide hB he {R} φ := (V.hasSum_geometricSide hB he φ).tsum_eq.symm
    _ = ∑' R : E[X], V'.geometricSide hB he' {R} φ := tsum_congr h_term
    _ = V'.geometricSide hB he' .univ φ := (V'.hasSum_geometricSide hB he' φ).tsum_eq
    _ = volume.real (K : Set (Gf E n)) * LinearMap.trace ℂ _ T' :=
        (V'.volume_mul_trace_eq hB he' hT').symm

end New

end
end
end

section
/-!
# Traces on the range of an idempotent from traces of a raising operator

Let `T⁺`, `T⁻` be adjoint operators on a finite-dimensional inner product space with
`T⁺ * T⁻ = d • (1 + c • e)`, where `d, c > 0`, `e` is idempotent and `A` commutes with `T⁺` and
`T⁻`. The traces of the `A ^ l * T⁺ ^ i`, `l, i ≥ 1`, determine the trace of `A` on the range of `e`
(`LineRelation.trace_mul_mean_eq`): on the generalised eigenspace of `A` for each non-zero
eigenvalue they give the eigenvalues of `T⁺`, hence the dimension and
`|det T⁺| ^ 2 = d ^ dim * (1 + c) ^ rank e`.

The first section collects what traces determine on generalised eigenspaces; in particular the
traces of all positive powers of an invertible operator determine its characteristic polynomial
(`charpoly_eq_of_trace_pow_succ_eq`).
-/

@[expose] public section

open Module LinearMap Polynomial InnerProductSpace

noncomputable section

namespace New

section GenEigenspace

variable {B B' : Type*} [AddCommGroup B] [Module ℂ B] [AddCommGroup B'] [Module ℂ B']
  {A T : End ℂ B} {A' T' : End ℂ B'}

/-- For an operator `T` that commutes with `A`, the restriction of `T` to the generalised
eigenspace of `A` for `μ`. -/
abbrev restrictGenEigenspace (h : Commute A T) (μ : ℂ) : End ℂ (A.maxGenEigenspace μ) :=
  T.restrict fun _ hx ↦ End.mapsTo_maxGenEigenspace_of_comm h μ hx

/-- Restriction to a generalised eigenspace of `A` commutes with taking powers. -/
lemma restrictGenEigenspace_pow (h : Commute A T) (μ : ℂ) (i : ℕ) :
    restrictGenEigenspace h μ ^ i = restrictGenEigenspace (h.pow_right i) μ :=
  End.pow_restrict i _

variable [Module.Finite ℂ B] [Module.Finite ℂ B']

/-- If `T` commutes with `A`, then on the generalised eigenspace of `A` for `μ` the trace of
`A * T` is `μ` times the trace of `T`, because `A - μ` is nilpotent there and commutes with `T`. -/
lemma trace_restrictGenEigenspace_mul (h : Commute A T) (μ : ℂ) :
    trace ℂ (A.maxGenEigenspace μ)
        (restrictGenEigenspace (T := A * T) ((Commute.refl A).mul_right h) μ) =
      μ * trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) := by
  have h_comm : Commute (restrictGenEigenspace h μ) (restrictGenEigenspace (.refl A) μ) :=
    restrict_commute h.symm _ _
  rw [show restrictGenEigenspace ((Commute.refl A).mul_right h) μ =
      restrictGenEigenspace (.refl A) μ * restrictGenEigenspace h μ from rfl, ← h_comm.eq]
  exact trace_comp_eq_mul_of_commute_of_isNilpotent μ h_comm
    (A.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ)

/-- If `T` commutes with `A`, then on the generalised eigenspace of `A` for `μ` the trace of
`A ^ l * T` is `μ ^ l` times the trace of `T`. -/
lemma trace_restrictGenEigenspace_pow_mul (h : Commute A T) (μ : ℂ) (l : ℕ) :
    trace ℂ (A.maxGenEigenspace μ)
        (restrictGenEigenspace (T := A ^ l * T) ((Commute.self_pow A l).mul_right h) μ) =
      μ ^ l * trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) := by
  induction l with
  | zero => simp only [restrictGenEigenspace, pow_zero, one_mul]
  | succ l ih =>
    have h_comm : Commute A (A ^ l * T) := (Commute.self_pow A l).mul_right h
    rw [pow_succ' μ, mul_assoc, ← ih, ← trace_restrictGenEigenspace_mul h_comm]
    simp only [restrictGenEigenspace, pow_succ', mul_assoc]

/-- Let `T` commute with `A` and let the finite set `S` contain all eigenvalues of `A`. Then the
trace of `A ^ l * T` is the sum over `μ ∈ S` of `μ ^ l` times the trace of `T` on the generalised
eigenspace of `A` for `μ`. -/
lemma trace_pow_mul_eq_sum (h : Commute A T) {S : Finset ℂ}
    (hS : ∀ μ : ℂ, μ ∉ S → A.maxGenEigenspace μ = ⊥) (l : ℕ) :
    trace ℂ B (A ^ l * T) =
      ∑ μ ∈ S, μ ^ l * trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) := by
  have h_subset : {μ : ℂ | A.maxGenEigenspace μ ≠ ⊥} ⊆ (S : Set ℂ) :=
    fun μ hμ ↦ by_contra fun hμS ↦ hμ (hS μ hμS)
  have h_finite : {μ : ℂ | A.maxGenEigenspace μ ≠ ⊥}.Finite := S.finite_toSet.subset h_subset
  have h_internal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    A.independent_maxGenEigenspace A.iSup_maxGenEigenspace_eq_top
  have h_comm : Commute A (A ^ l * T) := (Commute.self_pow A l).mul_right h
  calc _ = ∑ μ ∈ h_finite.toFinset,
          trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h_comm μ) :=
      trace_eq_sum_trace_restrict' h_internal h_finite (End.mapsTo_maxGenEigenspace_of_comm h_comm)
    _ = ∑ μ ∈ S, trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h_comm μ) := by
      refine Finset.sum_subset (h_finite.toFinset_subset.2 h_subset) fun μ _ hμ ↦ ?_
      have : Subsingleton (A.maxGenEigenspace μ) :=
        Submodule.subsingleton_iff_eq_bot.2 (by simpa using hμ)
      rw [Subsingleton.eq_zero (restrictGenEigenspace h_comm μ), map_zero]
    _ = ∑ μ ∈ S, μ ^ l * trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) :=
      Finset.sum_congr rfl fun μ _ ↦ trace_restrictGenEigenspace_pow_mul h μ l

/-- The sequences `l ↦ μ ^ l`, `μ : ℂ`, are linearly independent: two combinations of them that
agree for all `l` have the same coefficients. -/
lemma eq_of_sum_pow_mul_eq {S : Finset ℂ} {a a' : ℂ → ℂ}
    (h_sum : ∀ l : ℕ, ∑ μ ∈ S, μ ^ l * a μ = ∑ μ ∈ S, μ ^ l * a' μ) {μ : ℂ} (hμ : μ ∈ S) :
    a μ = a' μ := by
  have h_indep : LinearIndependent ℂ fun μ : ℂ ↦ ⇑(powersHom ℂ μ) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp _ (powersHom ℂ).injective
  have h_fun : ∑ ν ∈ S, a ν • ⇑(powersHom ℂ ν) = ∑ ν ∈ S, a' ν • ⇑(powersHom ℂ ν) := by
    funext l
    simpa [mul_comm] using h_sum l.toAdd
  exact linearIndependent_iff'ₛ.1 h_indep S a a' h_fun μ hμ

/-- Given operators `A` and `A'` and a number `μ`, there is a finite set that contains `μ` and all
eigenvalues of `A` and of `A'`. -/
lemma exists_finset_maxGenEigenspace_eq_bot (A : End ℂ B) (A' : End ℂ B') (μ : ℂ) :
    ∃ S : Finset ℂ, μ ∈ S ∧
      (∀ ν : ℂ, ν ∉ S → A.maxGenEigenspace ν = ⊥) ∧
      ∀ ν : ℂ, ν ∉ S → A'.maxGenEigenspace ν = ⊥ := by
  have h_finite : {ν : ℂ | A.maxGenEigenspace ν ≠ ⊥}.Finite :=
    Submodule.finite_ne_bot_of_iSupIndep A.independent_maxGenEigenspace
  have h_finite' : {ν : ℂ | A'.maxGenEigenspace ν ≠ ⊥}.Finite :=
    Submodule.finite_ne_bot_of_iSupIndep A'.independent_maxGenEigenspace
  exact ⟨insert μ (h_finite.toFinset ∪ h_finite'.toFinset), Finset.mem_insert_self _ _,
    by simp +contextual, by simp +contextual⟩

/-- Let `T` commute with `A` and `T'` with `A'`. If the traces of `A ^ l * T` and `A' ^ l * T'`
agree for all `l`, then so do the traces of `T` and `T'` on the generalised eigenspaces of `A`
and `A'` for each `μ`. -/
lemma trace_restrictGenEigenspace_eq (h : Commute A T) (h' : Commute A' T')
    (h_trace : ∀ l : ℕ, trace ℂ B (A ^ l * T) = trace ℂ B' (A' ^ l * T')) (μ : ℂ) :
    trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) =
      trace ℂ (A'.maxGenEigenspace μ) (restrictGenEigenspace h' μ) := by
  obtain ⟨S, hμ, hS, hS'⟩ := exists_finset_maxGenEigenspace_eq_bot A A' μ
  refine eq_of_sum_pow_mul_eq
    (a := fun ν ↦ trace ℂ (A.maxGenEigenspace ν) (restrictGenEigenspace h ν))
    (a' := fun ν ↦ trace ℂ (A'.maxGenEigenspace ν) (restrictGenEigenspace h' ν)) (fun l ↦ ?_) hμ
  rw [← trace_pow_mul_eq_sum h hS, ← trace_pow_mul_eq_sum h' hS', h_trace]

/-- Let `T` commute with `A` and `T'` with `A'`. If the traces of `A ^ (l + 1) * T` and
`A' ^ (l + 1) * T'` agree for all `l`, then so do the traces of `T` and `T'` on the generalised
eigenspaces of `A` and `A'` for each non-zero `μ`. -/
lemma trace_restrictGenEigenspace_eq_of_ne_zero (h : Commute A T) (h' : Commute A' T')
    (h_trace : ∀ l : ℕ, trace ℂ B (A ^ (l + 1) * T) = trace ℂ B' (A' ^ (l + 1) * T'))
    {μ : ℂ} (hμ : μ ≠ 0) :
    trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) =
      trace ℂ (A'.maxGenEigenspace μ) (restrictGenEigenspace h' μ) := by
  apply mul_left_cancel₀ hμ
  rw [← trace_restrictGenEigenspace_mul, ← trace_restrictGenEigenspace_mul]
  refine trace_restrictGenEigenspace_eq _ _ (fun l ↦ ?_) μ
  rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_succ, h_trace]

/-- The trace of the identity on a generalised eigenspace is the dimension of that space. -/
lemma trace_restrictGenEigenspace_one (A : End ℂ B) (μ : ℂ) :
    trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace (Commute.one_right A) μ) =
      finrank ℂ (A.maxGenEigenspace μ) :=
  trace_one ℂ (A.maxGenEigenspace μ)

/-- Operators whose generalised eigenspaces have the same dimensions for every `μ` have the same
characteristic polynomial, as these dimensions are the multiplicities of its roots. -/
lemma charpoly_eq_of_finrank_maxGenEigenspace_eq
    (h_finrank : ∀ μ : ℂ, finrank ℂ (A.maxGenEigenspace μ) = finrank ℂ (A'.maxGenEigenspace μ)) :
    A.charpoly = A'.charpoly := by
  have h_roots : A.charpoly.roots = A'.charpoly.roots := by
    ext μ
    simp_rw [count_roots, ← finrank_maxGenEigenspace_eq, h_finrank]
  rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic,
    (IsAlgClosed.splits A'.charpoly).eq_prod_roots_of_monic A'.charpoly_monic, h_roots]

lemma finrank_maxGenEigenspace_zero_of_det_ne_zero (h_det : T.det ≠ 0) :
    finrank ℂ (T.maxGenEigenspace 0) = 0 := by
  have h_unit : IsUnit T := (isUnit_iff_isUnit_det T).2 h_det.isUnit
  rw [T.maxGenEigenspace_eq_genEigenspace_finrank, End.genEigenspace_zero_nat,
    (isUnit_iff_ker_eq_bot _).1 (h_unit.pow _), finrank_bot]

/-- Two invertible operators with the same traces of all positive powers have the same
characteristic polynomial. -/
lemma charpoly_eq_of_trace_pow_succ_eq (h_det : T.det ≠ 0) (h_det' : T'.det ≠ 0)
    (h_trace : ∀ i : ℕ, trace ℂ B (T ^ (i + 1)) = trace ℂ B' (T' ^ (i + 1))) :
    T.charpoly = T'.charpoly := by
  refine charpoly_eq_of_finrank_maxGenEigenspace_eq fun μ ↦ Nat.cast_injective (R := ℂ) ?_
  obtain rfl | hμ := eq_or_ne μ 0
  · simp [finrank_maxGenEigenspace_zero_of_det_ne_zero, h_det, h_det']
  rw [← trace_restrictGenEigenspace_one, ← trace_restrictGenEigenspace_one]
  exact trace_restrictGenEigenspace_eq_of_ne_zero _ _ (fun l ↦ by simp only [mul_one, h_trace]) hμ

/-- For an idempotent `e`, the determinant of `1 + c e` is `(1 + c) ^ rank e`. -/
lemma det_one_add_smul_of_isIdempotentElem {e : End ℂ B} (he : IsIdempotentElem e) (c : ℂ) :
    (1 + c • e).det = (1 + c) ^ finrank ℂ (range e) := by
  -- The operator is `1 + c` on the range of `e` and induces the identity on the quotient.
  have h_range (x : B) (hx : x ∈ range e) : (1 + c • e) x = (1 + c) • x := by
    simp [he.mem_range_iff.1 hx, add_smul]
  have h_stable (x : B) (hx : x ∈ range e) : (1 + c • e) x ∈ range e := by
    simpa only [h_range x hx] using Submodule.smul_mem _ (1 + c) hx
  have h_restrict : (1 + c • e).restrict h_stable = (1 + c) • 1 := by
    ext x
    simpa using h_range x x.property
  have h_quotient : (range e).mapQ (range e) (1 + c • e) h_stable = 1 := by
    ext x
    simp
  simp [det_eq_det_mul_det (range e) _ h_stable, h_restrict, h_quotient, det_smul]

end GenEigenspace

variable {B B' : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup B'] [InnerProductSpace ℂ B']
variable {d c : ℝ}

/-- The line relations among operators `T⁺ = Tp`, `T⁻ = Tm`, `e` and `A`: `T⁻` is the adjoint of
`T⁺`, `e` is idempotent, `T⁺ T⁻ = d (1 + c e)` with `c, d > 0`, and `A` commutes with `T⁺` and
`T⁻`. They are meant for the stabiliser of a line in `GL_n(𝒪)`, `𝒪` a local ring with residue
field of order `q`: there `e` is the mean over `GL_n(𝒪)` (whence `mean` in the names of the
lemmas), `d = q ^ (n - 2)` and `c = q ^ n - 1`. -/
structure LineRelation (d c : ℝ) (A Tp Tm e : End ℂ B) : Prop where
  /-- The constant `d` is positive. -/
  d_pos : 0 < d
  /-- The constant `c` is positive. -/
  c_pos : 0 < c
  /-- `e` is idempotent. -/
  idem : IsIdempotentElem e
  /-- `T⁻` is the adjoint of `T⁺`. -/
  adjoint : ∀ x y : B, ⟪Tp x, y⟫_ℂ = ⟪x, Tm y⟫_ℂ
  /-- `T⁺ T⁻ = d (1 + c e)`. -/
  mul_eq : Tp * Tm = (d : ℂ) • (1 + (c : ℂ) • e)
  /-- `A` commutes with `T⁺`. -/
  commute_plus : Commute A Tp
  /-- `A` commutes with `T⁻`. -/
  commute_minus : Commute A Tm

namespace LineRelation

variable {A Tp Tm e : End ℂ B} {A' Tp' Tm' e' : End ℂ B'}

lemma mean_eq (h : LineRelation d c A Tp Tm e) :
    e = (c : ℂ)⁻¹ • ((d : ℂ)⁻¹ • (Tp * Tm) - 1) := by
  rw [h.mul_eq, inv_smul_smul₀ (Complex.ofReal_ne_zero.2 h.d_pos.ne'), add_sub_cancel_left,
    inv_smul_smul₀ (Complex.ofReal_ne_zero.2 h.c_pos.ne')]

/-- Under the line relations, `A` commutes with `e`, which is a polynomial in `T⁺ T⁻`. -/
lemma commute_mean (h : LineRelation d c A Tp Tm e) : Commute A e := by
  rw [h.mean_eq]
  exact (((h.commute_plus.mul_right h.commute_minus).smul_right _).sub_right
    (.one_right A)).smul_right _

/-- Under the line relations, a subspace that is stable under `T⁺` and `T⁻` is stable under `e`,
as `e` is a linear combination of `T⁺ T⁻` and the identity. -/
lemma mapsTo_mean (h : LineRelation d c A Tp Tm e) {H : Submodule ℂ B}
    (h_plus : ∀ x ∈ H, Tp x ∈ H) (h_minus : ∀ x ∈ H, Tm x ∈ H) : ∀ x ∈ H, e x ∈ H := by
  intro x hx
  simpa [h.mean_eq] using H.smul_mem _ (H.sub_mem (H.smul_mem _ (h_plus _ (h_minus x hx))) hx)

/-- The line relations (`T⁺`, `T⁻` adjoint, `T⁺ T⁻ = d (1 + c e)`, `A` commuting with both) pass
to a subspace that is stable under `A`, `T⁺` and `T⁻`. -/
lemma restrict (h : LineRelation d c A Tp Tm e) {H : Submodule ℂ B} (hA : ∀ x ∈ H, A x ∈ H)
    (h_plus : ∀ x ∈ H, Tp x ∈ H) (h_minus : ∀ x ∈ H, Tm x ∈ H) :
    LineRelation d c (A.restrict hA) (Tp.restrict h_plus) (Tm.restrict h_minus)
      (e.restrict (h.mapsTo_mean h_plus h_minus)) where
  d_pos := h.d_pos
  c_pos := h.c_pos
  idem := by
    ext x
    simpa using LinearMap.congr_fun h.idem.eq x
  adjoint x y := by simpa only [Submodule.coe_inner, restrict_apply] using h.adjoint x y
  mul_eq := by
    ext x
    simpa using LinearMap.congr_fun h.mul_eq x
  commute_plus := restrict_commute h.commute_plus hA h_plus
  commute_minus := restrict_commute h.commute_minus hA h_minus

/-- The line relations (`T⁺`, `T⁻` adjoint, `T⁺ T⁻ = d (1 + c e)`, `A` commuting with both) hold
for the restrictions of `A`, `T⁺`, `T⁻` and `e` to the generalised eigenspace of `A` for `α`. -/
lemma restrict_maxGenEigenspace (h : LineRelation d c A Tp Tm e) (α : ℂ) :
    LineRelation d c (restrictGenEigenspace (T := A) (.refl A) α)
      (restrictGenEigenspace (T := Tp) h.commute_plus α)
      (restrictGenEigenspace (T := Tm) h.commute_minus α)
      (restrictGenEigenspace (T := e) h.commute_mean α) :=
  h.restrict (fun _ hx ↦ End.mapsTo_maxGenEigenspace_of_comm (.refl A) α hx)
    (fun _ hx ↦ End.mapsTo_maxGenEigenspace_of_comm h.commute_plus α hx)
    (fun _ hx ↦ End.mapsTo_maxGenEigenspace_of_comm h.commute_minus α hx)

variable [Module.Finite ℂ B] [Module.Finite ℂ B']

/-- For operators with `T⁻` adjoint to `T⁺` and `T⁺ T⁻ = d (1 + c e)`, `e` idempotent, one has
`|det T⁺| ^ 2 = det (T⁺ T⁻) = d ^ dim B * (1 + c) ^ rank e`. -/
lemma norm_det_sq (h : LineRelation d c A Tp Tm e) :
    ‖Tp.det‖ ^ 2 = d ^ finrank ℂ B * (1 + c) ^ finrank ℂ (range e) := by
  have h_adjoint : Tp.adjoint = Tm := by
    rw [(eq_adjoint_iff Tp Tm).2 h.adjoint, adjoint_adjoint]
  apply Complex.ofReal_injective
  calc _ = (Tm * Tp).det := by
        rw [← normDet_eq_norm_det, ← h_adjoint]
        exact normDet_sq Tp
    _ = (Tp * Tm).det := by rw [map_mul, map_mul, mul_comm]
    _ = (d : ℂ) ^ finrank ℂ B * (1 + c) ^ finrank ℂ (range e) := by
      rw [h.mul_eq, det_smul, det_one_add_smul_of_isIdempotentElem h.idem]
    _ = (d ^ finrank ℂ B * (1 + c) ^ finrank ℂ (range e) : ℝ) := by norm_cast

lemma det_ne_zero (h : LineRelation d c A Tp Tm e) : Tp.det ≠ 0 := by
  refine norm_ne_zero_iff.1 (ne_zero_pow two_ne_zero ?_)
  rw [h.norm_det_sq]
  have := h.d_pos
  have := h.c_pos
  positivity

/-- Let `A, T⁺, T⁻, e` and `A', T⁺', T⁻', e'` satisfy the line relations (`T⁺`, `T⁻` adjoint,
`T⁺ T⁻ = d (1 + c e)`) for the same `c, d > 0`. If `T⁺` and `T⁺'` have the same characteristic
polynomial, then `e` and `e'` have the same rank: the polynomial gives the dimension and
`det T⁺`, hence the rank. -/
lemma finrank_range_eq_of_charpoly_eq (h : LineRelation d c A Tp Tm e)
    (h' : LineRelation d c A' Tp' Tm' e') (h_charpoly : Tp.charpoly = Tp'.charpoly) :
    finrank ℂ (range e) = finrank ℂ (range e') := by
  have h_dim : finrank ℂ B = finrank ℂ B' := by
    rw [← Tp.charpoly_natDegree, h_charpoly, Tp'.charpoly_natDegree]
  have h_det : Tp.det = Tp'.det := by
    rw [det_eq_sign_charpoly_coeff, det_eq_sign_charpoly_coeff, h_dim, h_charpoly]
  have h_pow : (1 + c) ^ finrank ℂ (range e) = (1 + c) ^ finrank ℂ (range e') :=
    mul_left_cancel₀ (pow_pos h.d_pos (finrank ℂ B')).ne'
      (by rw [← h'.norm_det_sq, ← h_det, h.norm_det_sq, h_dim])
  exact pow_right_injective₀ (add_pos one_pos h.c_pos) (lt_add_of_pos_right 1 h.c_pos).ne' h_pow

/-- Let `A, T⁺, T⁻, e` and `A', T⁺', T⁻', e'` satisfy the line relations (`T⁺`, `T⁻` adjoint,
`T⁺ T⁻ = d (1 + c e)`, `A` commuting with both) for the same `c, d > 0`. If the traces of
`A ^ (l + 1) * T⁺ ^ (i + 1)` and `A' ^ (l + 1) * T⁺' ^ (i + 1)` agree for all `l, i`, then for
each non-zero `α` the idempotents `e` and `e'` have the same rank on the generalised eigenspaces
of `A` and `A'` for `α`. -/
lemma finrank_range_restrictGenEigenspace_eq (h : LineRelation d c A Tp Tm e)
    (h' : LineRelation d c A' Tp' Tm' e')
    (h_trace : ∀ l i : ℕ,
      trace ℂ B (A ^ (l + 1) * Tp ^ (i + 1)) = trace ℂ B' (A' ^ (l + 1) * Tp' ^ (i + 1)))
    {α : ℂ} (hα : α ≠ 0) :
    finrank ℂ (range (restrictGenEigenspace (T := e) h.commute_mean α)) =
      finrank ℂ (range (restrictGenEigenspace (T := e') h'.commute_mean α)) := by
  -- On the generalised eigenspaces for `α` the operators `T⁺` are invertible, so the traces of
  -- their positive powers determine their characteristic polynomials.
  have h_charpoly : (restrictGenEigenspace h.commute_plus α).charpoly =
      (restrictGenEigenspace h'.commute_plus α).charpoly := by
    refine charpoly_eq_of_trace_pow_succ_eq (h.restrict_maxGenEigenspace α).det_ne_zero
      (h'.restrict_maxGenEigenspace α).det_ne_zero fun i ↦ ?_
    rw [restrictGenEigenspace_pow, restrictGenEigenspace_pow]
    exact trace_restrictGenEigenspace_eq_of_ne_zero _ _ (fun l ↦ h_trace l i) hα
  exact (h.restrict_maxGenEigenspace α).finrank_range_eq_of_charpoly_eq
    (h'.restrict_maxGenEigenspace α) h_charpoly

/-- Let `A, T⁺, T⁻, e` and `A', T⁺', T⁻', e'` satisfy the line relations (`T⁺`, `T⁻` adjoint,
`T⁺ T⁻ = d (1 + c e)`, `A` commuting with both) for the same `c, d > 0`. If the traces of
`A ^ (l + 1) * T⁺ ^ (i + 1)` and `A' ^ (l + 1) * T⁺' ^ (i + 1)` agree for all `l, i`, then so do
the traces of `A * e` and `A' * e'`, which are those of `A` and `A'` on the ranges of `e` and
`e'`. -/
theorem trace_mul_mean_eq (h : LineRelation d c A Tp Tm e) (h' : LineRelation d c A' Tp' Tm' e')
    (h_trace : ∀ l i : ℕ,
      trace ℂ B (A ^ (l + 1) * Tp ^ (i + 1)) = trace ℂ B' (A' ^ (l + 1) * Tp' ^ (i + 1))) :
    trace ℂ B (A * e) = trace ℂ B' (A' * e') := by
  -- Both traces are sums over a finite set containing the eigenvalues of `A` and `A'`: the term of
  -- `α` is `α` times the rank of the idempotent on the generalised eigenspace for `α`.
  obtain ⟨S, -, hS, hS'⟩ := exists_finset_maxGenEigenspace_eq_bot A A' 0
  rw [← pow_one A, ← pow_one A', trace_pow_mul_eq_sum h.commute_mean hS,
    trace_pow_mul_eq_sum h'.commute_mean hS']
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  obtain rfl | hα := eq_or_ne α 0
  · rw [pow_one, zero_mul, zero_mul]
  -- The trace of an idempotent is its rank.
  simp only [(h.restrict_maxGenEigenspace α).idem.isProj_range.trace,
    (h'.restrict_maxGenEigenspace α).idem.isProj_range.trace,
    h.finrank_range_restrictGenEigenspace_eq h' h_trace hα]

end LineRelation

end New

end
end
end

section
/-!
# Test functions with a deeper level at an auxiliary place

Let `v` be a split place at which the level `K` is maximal, and let `K'` be the part of `K` whose
component at `v` lies in a subgroup `J` of `GL_n(E_v)`. For a group algebra element `a` that is
integral at `v`, removing the components at `v` and its conjugate gives an element whose function
of level `K'` is the function of `a` of level `K`, cut off to the points with component at `v` in
`J`. So it is cuspidal at a place `w` other than `v` and its conjugate if the function of `a` is.
The function of a product with a factor at `v` in a set `S` is supported at `v` in `S J`.

Notions from other files:

* `Gf E n` is the finite adelic unitary group, and `g.atPlace v` is the component of `g` at `v`.
* For a split place `v` (one that differs from its conjugate), `ofSplitPlace hv k` is the element
  with component `k` at `v`, the inverse conjugate transpose of `k` at the conjugate of `v`, and `1`
  at all other places.
* `spanOn ℂ S` is the space of the group algebra elements that are combinations of the elements
  of the set `S`.
* `convIndicator` sends a group algebra element `a` to the test function `a ⋆ 1_K` of level `K`.
* `maxCompactAt n v` is the group of integral elements supported at `v` and its conjugate, and
  `localIntGL n v` is `GL_n(O_v)`.

## Relation to the literature

Known result: Test functions with a deeper level at an auxiliary split place, by removing the
components there. It serves `Lib.Adelic.TraceFormula.CuspidalComparison`.
-/

@[expose] public section

open NumberField MonoidAlgebra

namespace New

open Variety

variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  {v w : FinPlace E}

/-- The homomorphism that removes from an element its components at the split place `v` and at
the conjugate of `v`. -/
noncomputable def offPlace (hv : v.IsSplit) : Gf E n →* Gf E n :=
  MonoidHom.mk' (fun g ↦ g * (ofSplitPlace hv (g.atPlace v))⁻¹) fun g h ↦ by
    have h_comm : Commute (ofSplitPlace hv (g.atPlace v)) (h * (ofSplitPlace hv (h.atPlace v))⁻¹) :=
      Gf.commute_supportedOn_trivialOn (ofSplitPlace_mem_supportedOn hv _) (by simp)
    simp only [map_mul, mul_inv_rev, mul_assoc, h_comm.inv_left.eq]

/-- Removing the components of `g` at `v` and its conjugate is dividing `g` by the element
`ofSplitPlace hv (g.atPlace v)`, which has these components and is `1` at all other places. -/
lemma offPlace_apply (hv : v.IsSplit) (g : Gf E n) :
    offPlace hv g = g * (ofSplitPlace hv (g.atPlace v))⁻¹ := rfl

@[simp] lemma atPlace_offPlace (hv : v.IsSplit) (g : Gf E n) : (offPlace hv g).atPlace v = 1 := by
  simp [offPlace_apply]

variable {K : Subgroup (Gf E n)} {J : Subgroup (GL n (LocField v))}

open scoped Classical in
/-- Let `v` be a split place, let `K` be a compact open subgroup of the adelic unitary group
`Gf E n` that contains the maximal compact group at `v`, let `J` be a subgroup of `GL_n(E_v)`
such that `K ⊓ J.comap (Gf.atPlace v)` is compact open, and let `a` be a combination (`spanOn`)
of elements with component at `v` in `localIntGL n v = GL_n(O_v)`. Removing (`offPlace`)
the components of `a` at `v` and its conjugate and deepening the level to
`K ⊓ J.comap (Gf.atPlace v)` gives the function of `a` of level `K`, cut off outside the points
with component at `v` in `J`. Here `convIndicator` sends a group algebra element to its
convolution with the characteristic function of the level. -/
lemma convIndicator_mapDomain_offPlace {hK_open : IsOpen (K : Set (Gf E n))}
    {hK_compact : IsCompact (K : Set (Gf E n))}
    {hK'_open : IsOpen (↑(K ⊓ J.comap (Gf.atPlace v)) : Set (Gf E n))}
    {hK'_compact : IsCompact (↑(K ⊓ J.comap (Gf.atPlace v)) : Set (Gf E n))}
    (hv : v.IsSplit) (hK_max : maxCompactAt n v ≤ K) {a : ℂ[Gf E n]}
    (ha : a ∈ spanOn ℂ {x : Gf E n | x.atPlace v ∈ localIntGL n v}) (g : Gf E n) :
    (convIndicator hK'_open hK'_compact (mapDomain (offPlace hv) a)).val g =
      if g.atPlace v ∈ J then (convIndicator hK_open hK_compact a).val g else 0 := by
  -- By linearity we may take `a` to be a single element `x` that is integral at `v`. Its part at
  -- `v` then lies in `K`, so removing that part changes only the condition at `v`.
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨x, hx, rfl⟩ : ∃ x : Gf E n, x.atPlace v ∈ localIntGL n v ∧ of ℂ (Gf E n) x = a := ha
    have h_mem : ofSplitPlace hv (x.atPlace v) ∈ K :=
      hK_max ⟨(ofSplitPlace_mem_stdLevel hv _).2 hx, ofSplitPlace_mem_supportedOn hv _⟩
    have h_coset : (offPlace hv x)⁻¹ * g ∈ K ⊓ J.comap (Gf.atPlace v) ↔
        g.atPlace v ∈ J ∧ x⁻¹ * g ∈ K := by
      simp [offPlace_apply, mul_assoc, K.mul_mem_cancel_left h_mem, and_comm]
    simp [convIndicator_single, h_coset, ← ite_and]
  | zero => simp
  | add a b _ _ ha hb => simp [mapDomain_add, ha, hb, ite_add_zero]
  | smul c a _ ha => simp [mapDomain_smul, ha]

/-- Let `v` be a split place, let `K` be a compact open subgroup of the adelic unitary group
`Gf E n` that contains the maximal compact group at `v`, let `J` be a subgroup of `GL_n(E_v)`,
let `a` be a combination (`spanOn`) of elements that are integral at `v` (component in
`localIntGL n v`), and let `w` be a split place other than `v` and its conjugate. If the function
`a ⋆ 1_K` (`convIndicator`) is cuspidal at `w` (its sums of translates over the cosets of each
unipotent radical at `w` vanish), then so is the function of level `K ⊓ J.comap (Gf.atPlace v)`
of `a` with the components at `v` and its conjugate removed (`offPlace`). -/
lemma IsCuspidalAt.convIndicator_offPlace {hK_open : IsOpen (K : Set (Gf E n))}
    {hK_compact : IsCompact (K : Set (Gf E n))}
    {hK'_open : IsOpen (↑(K ⊓ J.comap (Gf.atPlace v)) : Set (Gf E n))}
    {hK'_compact : IsCompact (↑(K ⊓ J.comap (Gf.atPlace v)) : Set (Gf E n))}
    {hw : w.IsSplit} (hv : v.IsSplit) (h_ne : v ≠ w) (h_star_ne : star v ≠ w)
    (hK_max : maxCompactAt n v ≤ K) {a : ℂ[Gf E n]}
    (ha : a ∈ spanOn ℂ {x : Gf E n | x.atPlace v ∈ localIntGL n v})
    (h_cusp : IsCuspidalAt hw (convIndicator hK_open hK_compact a)) :
    IsCuspidalAt hw (convIndicator hK'_open hK'_compact (mapDomain (offPlace hv) a)) := by
  classical
  intro T hT_empty hT_univ t lift h_lift g
  -- A translation at `w` does not change the component at `v`.
  have h_place (k : GL n (LocField w)) : (g * ofSplitPlace hw k).atPlace v = g.atPlace v := by
    rw [map_mul, atPlace_ofSplitPlace_of_ne hw k h_ne h_star_ne, mul_one]
  simp only [convIndicator_mapDomain_offPlace (hK_open := hK_open) (hK_compact := hK_compact)
    hv hK_max ha, h_place]
  split_ifs
  exacts [h_cusp T hT_empty hT_univ t lift h_lift g, finsum_zero]

/-- Let `u` be a combination (`spanOn`) of elements of a set `S` of `GL_n(E_v)`, let `J` be a
subgroup of `GL_n(E_v)`, and let `b` be any element of the group algebra of the adelic unitary
group `Gf E n`. Form the product of `u`, placed at `v` by `ofSplitPlace`, with `b` after removing
(`offPlace`) its components at `v` and its conjugate, and take the function (`convIndicator`) of
level `K ⊓ J.comap (Gf.atPlace v)` of this product. Where it is not zero, the component at `v`
lies in `S J`. -/
lemma exists_atPlace_eq_of_convIndicator_ne_zero
    {hK'_open : IsOpen (↑(K ⊓ J.comap (Gf.atPlace v)) : Set (Gf E n))}
    {hK'_compact : IsCompact (↑(K ⊓ J.comap (Gf.atPlace v)) : Set (Gf E n))}
    (hv : v.IsSplit) {S : Set (GL n (LocField v))}
    {u : ℂ[GL n (LocField v)]} (hu : u ∈ spanOn ℂ S) (b : ℂ[Gf E n]) {g : Gf E n}
    (hg : (convIndicator hK'_open hK'_compact
      (mapDomain (ofSplitPlace hv) u * mapDomain (offPlace hv) b)).val g ≠ 0) :
    ∃ x ∈ S, ∃ k ∈ J, g.atPlace v = x * k := by
  contrapose! hg
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    have h_notMem : x⁻¹ * g.atPlace v ∉ J := fun h_mem ↦
      hg x hx _ h_mem (mul_inv_cancel_left x _).symm
    induction b using induction_linear with
    | zero => simp
    | add b b' hb hb' => simp_all [mapDomain_add, mul_add]
    | single y c =>
      have h_coset : (ofSplitPlace hv x * offPlace hv y)⁻¹ * g ∉ K ⊓ J.comap (Gf.atPlace v) := by
        simp [mul_assoc, h_notMem]
      -- `mul_inv_rev` would rewrite the element in the goal that `h_coset` is about.
      simp [convIndicator_single, h_coset, -mul_inv_rev]
  | zero => simp
  | add u u' _ _ hu hu' => simp [mapDomain_add, add_mul, hu, hu']
  | smul c u _ hu => simp [mapDomain_smul, hu]

end New
end
end

section
/-!
# Passage to the stabiliser of a line at an auxiliary place

Let `w` be a split place at which the level `K` is maximal, and let `K'` be the level that is the
stabiliser `J` of a line at `w` and agrees with `K` elsewhere. On the vectors of level `K'` of a
representation, an operator `A` that comes from the places off `w` commutes with the operators `T⁺`,
`T⁻` of `J`, and the mean `e` over `GL_n(𝒪_w)` projects onto the vectors of level `K`. If the
representation is unitary and the vectors of level `K'` form a finite-dimensional space, then the
traces of the `A ^ l * T⁺ ^ m`, `l, m ≥ 1`, at level `K'` determine the trace of `A` at level `K`
(`trace_eq_of_trace_cutLevel_eq`).

Notions from other files:
* `levelSpace ρ K`: the vectors of the representation `ρ` that are fixed by `K`; `levelAlgebra ρ K`:
  the elements of the group algebra that map this space to itself.
* `Gf E n`: the group of finite-adelic unitary elements, whose component at `w` is `g.atPlace w` in
  `GL n (LocField w)`; `localIntGL n w`: the group `GL_n(𝒪_w)`; `stdLevel E n`: the finite-adelic
  unitary elements that are integral at every place; `maxCompactAt n w`: those elements of
  `stdLevel E n` that are trivial away from `w` and its conjugate.
* `ofSplitPlace hw x`: the finite-adelic unitary element with component `x` at the split place `w`;
  `offPlace hw g`: the part of `g` away from `w` and its conjugate.
* `lineStabilizer w i`: the stabiliser in `GL_n(𝒪_w)` of the `i`-th coordinate line modulo `w`;
  `lineHecke w i` and `lineHeckeLower w i` act as its Hecke operators `T⁺` and `T⁻`.
* `LineRelation d c A T⁺ T⁻ e`: `T⁻` is adjoint to `T⁺`, `T⁺ T⁻ = d (1 + c e)`, `e` is idempotent,
  `A` commutes with `T⁺` and `T⁻`, and `d, c > 0`.
-/

@[expose] public section

noncomputable section

namespace New

open NumberField Module LinearMap MonoidAlgebra InnerProductSpace

open Variety (spanOn)

variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  {w : FinPlace E}

/-- The part of `K` whose component at `w` lies in `J`. -/
abbrev cutLevel (K : Subgroup (Gf E n)) (w : FinPlace E) (J : Subgroup (GL n (LocField w))) :
    Subgroup (Gf E n) := K ⊓ J.comap (Gf.atPlace w)

/-- The cut of a level by the stabiliser of a line at `w` is again a level: it is open and lies in
`stdLevel E n`, the subgroup of elements that are integral at every place. -/
instance isLevel_cutLevel_lineStabilizer (K : Subgroup (Gf E n)) [IsLevel K] (w : FinPlace E)
    (i : n) : IsLevel (cutLevel K w (lineStabilizer w i)) where
  le := inf_le_left.trans IsLevel.le
  isOpen := IsLevel.isOpen.inter ((isOpen_lineStabilizer w i).preimage (Gf.continuous_atPlace w))

/-- The part of `g` off the split place `w` commutes with every element supported at `w`. -/
lemma commute_offPlace_ofSplitPlace (hw : w.IsSplit) (g : Gf E n) (x : GL n (LocField w)) :
    Commute (offPlace hw g) (ofSplitPlace hw x) := by
  refine (Gf.commute_supportedOn_trivialOn (ofSplitPlace_mem_supportedOn hw x) ?_).symm
  simp [Gf.mem_trivialOn, atPlace_offPlace]

/-- If `K` contains the maximal compact subgroup at the split place `w`, it contains the image of
`GL_n(𝒪_w)` under `ofSplitPlace`. -/
lemma ofSplitPlace_mem_of_maxCompactAt_le (hw : w.IsSplit) {K : Subgroup (Gf E n)}
    (hK : maxCompactAt n w ≤ K) {x : GL n (LocField w)} (hx : x ∈ localIntGL n w) :
      ofSplitPlace hw x ∈ K :=
  hK ⟨(ofSplitPlace_mem_stdLevel hw x).2 hx, ofSplitPlace_mem_supportedOn hw x⟩

section Algebraic

variable (hw : w.IsSplit) {K : Subgroup (Gf E n)} {J : Subgroup (GL n (LocField w))}
  {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (Gf E n) M) [IsLevel K]

/-- The action of an element through its part off `w`. -/
abbrev offRep : Representation ℂ (Gf E n) M := ρ.comp (offPlace hw)

/-- The action of the group at `w`. -/
abbrev localRep : Representation ℂ (GL n (LocField w)) M := ρ.comp (ofSplitPlace hw)

/-- An element acts as its component at `w` followed by its part off `w`. -/
lemma apply_eq_offRep_localRep (g : Gf E n) (y : M) :
    ρ g y = offRep hw ρ g (localRep hw ρ (g.atPlace w) y) := by
  simp [← mul_apply_eq_comp, ← map_mul, offPlace_apply]

/-- The action of an element off `w` commutes with the action of the group algebra at `w`. -/
lemma commute_offRep_localRep (g : Gf E n) (u : ℂ[GL n (LocField w)]) :
    Commute (offRep hw ρ g) ((localRep hw ρ).asAlgebraHom u) :=
  Representation.commute_asAlgebraHom_of_forall_commute _
      (fun x ↦ (commute_offPlace_ofSplitPlace hw g x).map ρ) u

/-- The action of an element at `w` commutes with the action of the group algebra through the parts
off `w`. -/
lemma commute_localRep_offRep (x : GL n (LocField w)) (a : ℂ[Gf E n]) :
    Commute (localRep hw ρ x) ((offRep hw ρ).asAlgebraHom a) :=
  Representation.commute_asAlgebraHom_of_forall_commute _
      (fun g ↦ (commute_offPlace_ofSplitPlace hw g x).symm.map ρ) a

/-- Let `a` be a combination of group elements whose components at the split place `w` lie in
`GL_n(𝒪_w)`. On vectors that are spherical at `w` (fixed by the maximal compact subgroup there),
`a` acts through its part off `w`. -/
lemma asAlgebraHom_offRep_apply {a : ℂ[Gf E n]}
    (ha : a ∈ spanOn ℂ {g : Gf E n | g.atPlace w ∈ localIntGL n w}) {y : M}
      (hy : y ∈ sphericalAt ρ w) :
    (offRep hw ρ).asAlgebraHom a y = ρ.asAlgebraHom a y := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨g, hg, rfl⟩ := ha
    have h_fixed : localRep hw ρ (g.atPlace w) y = y :=
      ((mem_sphericalAt_iff hw).1 hy ⟨g.atPlace w, hg⟩).trans (one_smul ℂ y)
    simp only [Representation.asAlgebraHom_of, apply_eq_offRep_localRep hw ρ g, h_fixed]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

/-- The inclusion of the vectors of level `K` in those of the level that is cut down to the
stabiliser of the `i`-th coordinate line at `w`. -/
def cutInclusion (w : FinPlace E) (K : Subgroup (Gf E n)) {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (Gf E n) M) (i : n) :
    levelSpace ρ K →ₗ[ℂ] levelSpace ρ (cutLevel K w (lineStabilizer w i)) :=
  Submodule.inclusion (levelSpace_anti inf_le_left)

/-- If `K` contains the maximal compact subgroup at the split place `w` and `J ≤ GL_n(𝒪_w)`, a
vector is fixed by the cut level `{k ∈ K | k_w ∈ J}` exactly when it is fixed by the part of `K`
off `w` and by `J` acting at `w`. -/
lemma mem_levelSpace_cutLevel_iff (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w) {y : M} :
    y ∈ levelSpace ρ (cutLevel K w J) ↔
      y ∈ levelSpace (offRep hw ρ) K ∧ y ∈ levelSpace (localRep hw ρ) J := by
  refine ⟨fun hy ↦ ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨k, hk⟩
    have hk_off : offPlace hw k ∈ K := K.mul_mem hk <| K.inv_mem <|
      ofSplitPlace_mem_of_maxCompactAt_le hw hK (mem_stdLevel_iff.1 (IsLevel.le hk) w)
    exact hy ⟨offPlace hw k, hk_off, by simp [atPlace_offPlace]⟩
  · rintro ⟨x, hx⟩
    exact hy ⟨ofSplitPlace hw x, ofSplitPlace_mem_of_maxCompactAt_le hw hK (hJ hx),
      by simpa [atPlace_ofSplitPlace] using hx⟩
  · rintro ⟨h_off, h_local⟩ ⟨k, hk, hk_local⟩
    rw [apply_eq_offRep_localRep hw, h_local ⟨k.atPlace w, hk_local⟩, MonoidHom.one_apply, one_smul]
    exact h_off ⟨k, hk⟩

/-- If `K` is maximal at `w`, a vector is fixed by `K` exactly when it is fixed by the part of `K`
off `w` and by `GL_n(𝒪_w)`. -/
lemma mem_levelSpace_iff_offRep_localRep (hK : maxCompactAt n w ≤ K) {y : M} :
    y ∈ levelSpace ρ K ↔
      y ∈ levelSpace (offRep hw ρ) K ∧ y ∈ levelSpace (localRep hw ρ) (localIntGL n w) := by
  have h_cut : cutLevel K w (localIntGL n w) = K :=
    inf_eq_left.2 fun k hk ↦ mem_stdLevel_iff.1 (IsLevel.le hk) w
  rw [← mem_levelSpace_cutLevel_iff hw ρ hK le_rfl, h_cut]

/-- The elements of the group algebra that map the space of vectors fixed by the part of `K` off
`w` to itself act on the vectors of the cut level through their parts off `w`. -/
def offAction (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w) :
    levelAlgebra (offRep hw ρ) K →ₐ[ℂ] End ℂ (levelSpace ρ (cutLevel K w J)) :=
  (levelAction ρ (cutLevel K w J)).comp <|
    ((mapDomainAlgHom ℂ ℂ (offPlace hw)).comp (levelAlgebra (offRep hw ρ) K).val).codRestrict _
      fun a y hy ↦ by
        obtain ⟨h_off, h_local⟩ := (mem_levelSpace_cutLevel_iff hw ρ hK hJ).1 hy
        change ρ.asAlgebraHom (mapDomain (offPlace hw) a) y ∈ levelSpace ρ (cutLevel K w J)
        rw [asAlgebraHom_mapDomain, mem_levelSpace_cutLevel_iff hw ρ hK hJ]
        exact ⟨a.property y h_off, map_mem_levelSpace_of_commute h_local
          fun x ↦ commute_localRep_offRep hw ρ x a⟩

/-- The elements of the group algebra at `w` that map the space of vectors fixed by `J` to itself
act on the vectors of the cut level. -/
def localAction (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w) :
    levelAlgebra (localRep hw ρ) J →ₐ[ℂ] End ℂ (levelSpace ρ (cutLevel K w J)) :=
  (levelAction ρ (cutLevel K w J)).comp <|
    ((mapDomainAlgHom ℂ ℂ (ofSplitPlace hw)).comp (levelAlgebra (localRep hw ρ) J).val).codRestrict
      _ fun u y hy ↦ by
        obtain ⟨h_off, h_local⟩ := (mem_levelSpace_cutLevel_iff hw ρ hK hJ).1 hy
        change ρ.asAlgebraHom (mapDomain (ofSplitPlace hw) u) y ∈ levelSpace ρ (cutLevel K w J)
        rw [asAlgebraHom_mapDomain, mem_levelSpace_cutLevel_iff hw ρ hK hJ]
        exact ⟨map_mem_levelSpace_of_commute h_off fun k ↦ commute_offRep_localRep hw ρ k u,
          u.property y h_local⟩

/-- On the vectors of the cut level, `offAction` of `a` is the action of `a` through the parts off
`w`. -/
lemma coe_offAction_apply (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w)
    (a : levelAlgebra (offRep hw ρ) K) (y : levelSpace ρ (cutLevel K w J)) :
    (offAction hw ρ hK hJ a y : M) = (offRep hw ρ).asAlgebraHom a y := by
  change ρ.asAlgebraHom (mapDomain (offPlace hw) (a : ℂ[Gf E n])) y = _
  rw [asAlgebraHom_mapDomain]

/-- On the vectors of the cut level, `localAction` of `u` is the action of `u` at `w`. -/
lemma coe_localAction_apply (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w)
    (u : levelAlgebra (localRep hw ρ) J) (y : levelSpace ρ (cutLevel K w J)) :
    (localAction hw ρ hK hJ u y : M) = (localRep hw ρ).asAlgebraHom u y := by
  change ρ.asAlgebraHom (mapDomain (ofSplitPlace hw) (u : ℂ[GL n (LocField w)])) y = _
  rw [asAlgebraHom_mapDomain]

/-- On the vectors of the cut level, the operators from the parts off `w` commute with those from
the component at `w`. -/
lemma commute_offAction_localAction (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w)
    (a : levelAlgebra (offRep hw ρ) K) (u : levelAlgebra (localRep hw ρ) J) :
    Commute (offAction hw ρ hK hJ a) (localAction hw ρ hK hJ u) := by
  have h_comm : Commute ((offRep hw ρ).asAlgebraHom a) ((localRep hw ρ).asAlgebraHom u) :=
    Representation.commute_asAlgebraHom_of_forall_commute _
        (fun x ↦ (commute_localRep_offRep hw ρ x a).symm) u
  ext y
  simpa [coe_offAction_apply, coe_localAction_apply] using LinearMap.congr_fun h_comm.eq y

/-- Let `a` map the vectors fixed by the part of `K` off `w` to themselves, and `u` those fixed by
`J` at `w`. On the cut level, the operator of `a` times that of `u` is the action of the product of
the images of `u` under `ofSplitPlace` and of `a` under `offPlace`. -/
lemma coe_offAction_mul_localAction_apply (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w)
    (a : levelAlgebra (offRep hw ρ) K) (u : levelAlgebra (localRep hw ρ) J)
    (y : levelSpace ρ (cutLevel K w J)) :
    ((offAction hw ρ hK hJ a * localAction hw ρ hK hJ u) y : M) =
      ρ.asAlgebraHom (mapDomain (ofSplitPlace hw) u * mapDomain (offPlace hw) a) y := by
  calc ((offAction hw ρ hK hJ a * localAction hw ρ hK hJ u) y : M)
    _ = (localRep hw ρ).asAlgebraHom u ((offRep hw ρ).asAlgebraHom a y) := by
      rw [(commute_offAction_localAction hw ρ hK hJ a u).eq, mul_apply_eq_comp,
        coe_localAction_apply, coe_offAction_apply]
    _ = _ := by rw [map_mul, mul_apply_eq_comp, asAlgebraHom_mapDomain, asAlgebraHom_mapDomain]

/-- The operator `T⁺` at `w` on the vectors whose level is the stabiliser of the `i`-th coordinate
line at `w` and `K` elsewhere. -/
def raiseAt (hK : maxCompactAt n w ≤ K) (i : n) :
    End ℂ (levelSpace ρ (cutLevel K w (lineStabilizer w i))) :=
  localAction hw ρ hK (lineStabilizer_le_localIntGL w i) ⟨lineHecke w i, fun y hy ↦ by
    simpa only [asAlgebraHom_lineHecke] using lineRaise_mem hy⟩

/-- The operator `T⁻` at `w` on the vectors whose level is the stabiliser of the `i`-th coordinate
line at `w` and `K` elsewhere. -/
def lowerAt (hK : maxCompactAt n w ≤ K) (i : n) :
    End ℂ (levelSpace ρ (cutLevel K w (lineStabilizer w i))) :=
  localAction hw ρ hK (lineStabilizer_le_localIntGL w i) ⟨lineHeckeLower w i, fun y hy ↦ by
    simpa only [asAlgebraHom_lineHeckeLower] using lineLower_mem hy⟩

/-- The mean over `GL_n(𝒪_w)`, from the level that is cut at `w` to the level `K`. -/
def meanAt (hK : maxCompactAt n w ≤ K) (i : n) :
    levelSpace ρ (cutLevel K w (lineStabilizer w i)) →ₗ[ℂ] levelSpace ρ K :=
  (sphericalMean (localRep hw ρ)).restrict fun y hy ↦ by
    obtain ⟨h_off, h_local⟩ := (mem_levelSpace_cutLevel_iff hw ρ hK
      (lineStabilizer_le_localIntGL w i)).1 hy
    rw [mem_levelSpace_iff_offRep_localRep hw ρ hK]
    refine ⟨map_mem_levelSpace_of_commute h_off fun k ↦ ?_, sphericalMean_mem h_local⟩
    simpa only [asAlgebraHom_sphericalMeanElement] using commute_offRep_localRep hw ρ k
      (sphericalMeanElement n w)

/-- `raiseAt` is the restriction of the operator `T⁺ = lineRaise` of the representation at `w`. -/
lemma coe_raiseAt_apply (hK : maxCompactAt n w ≤ K) (i : n)
    (y : levelSpace ρ (cutLevel K w (lineStabilizer w i))) :
    (raiseAt hw ρ hK i y : M) = lineRaise i (localRep hw ρ) y := by
  rw [raiseAt, coe_localAction_apply, asAlgebraHom_lineHecke]

/-- `lowerAt` is the restriction of the operator `T⁻ = lineLower` of the representation at `w`. -/
lemma coe_lowerAt_apply (hK : maxCompactAt n w ≤ K) (i : n)
    (y : levelSpace ρ (cutLevel K w (lineStabilizer w i))) :
    (lowerAt hw ρ hK i y : M) = lineLower i (localRep hw ρ) y := by
  rw [lowerAt, coe_localAction_apply, asAlgebraHom_lineHeckeLower]

omit [IsLevel K] in
lemma coe_cutInclusion_apply (i : n) (y : levelSpace ρ K) : (cutInclusion w K ρ i y : M) = y := rfl

/-- `meanAt`, followed by the inclusion of the vectors of level `K`, is `sphericalMean`, the mean
over `GL_n(𝒪_w)`. -/
lemma coe_cutInclusion_meanAt_apply (hK : maxCompactAt n w ≤ K) (i : n)
    (y : levelSpace ρ (cutLevel K w (lineStabilizer w i))) :
    ((cutInclusion w K ρ i ∘ₗ meanAt hw ρ hK i) y : M) = sphericalMean (localRep hw ρ) y := rfl

/-- If `K` contains the maximal compact subgroup at the split place `w`, the mean over `GL_n(𝒪_w)`
fixes the vectors of level `K`: `meanAt` is a left inverse of the inclusion `cutInclusion` of these
vectors in those of the level cut by the stabiliser of the `i`-th coordinate line at `w`. -/
lemma meanAt_comp_cutInclusion (hK : maxCompactAt n w ≤ K) (i : n) :
    meanAt hw ρ hK i ∘ₗ cutInclusion w K ρ i = .id := by
  ext ⟨y, hy⟩
  exact sphericalMean_eq_self ((mem_levelSpace_iff_offRep_localRep hw ρ hK).1 hy).right

/-- Let `K` contain the maximal compact subgroup at the split place `w`, and let the vectors of the
level cut by the stabiliser of a line at `w` form a finite-dimensional space. Let `a` map the space
of vectors fixed by the part of `K` off `w` to itself, let `A` and `T` be its actions through the
parts off `w` at the cut level and at level `K`, and let `e` be the mean over `GL_n(𝒪_w)`
(`meanAt` followed by the inclusion `cutInclusion`). Then `A * e` and `T` have the same trace. -/
lemma trace_offAction_mul_mean (hK : maxCompactAt n w ≤ K) (i : n)
    [Module.Finite ℂ (levelSpace ρ (cutLevel K w (lineStabilizer w i)))]
    (a : levelAlgebra (offRep hw ρ) K) {T : End ℂ (levelSpace ρ K)}
    (hT : ∀ y : levelSpace ρ K, (T y : M) = (offRep hw ρ).asAlgebraHom a y) :
    trace ℂ (levelSpace ρ (cutLevel K w (lineStabilizer w i)))
        (offAction hw ρ hK (lineStabilizer_le_localIntGL w i) a *
          (cutInclusion w K ρ i ∘ₗ meanAt hw ρ hK i)) =
      trace ℂ (levelSpace ρ K) T := by
  have : Module.Finite ℂ (levelSpace ρ K) :=
    .of_injective (cutInclusion w K ρ i) (Submodule.inclusion_injective _)
  have h_restrict : offAction hw ρ hK (lineStabilizer_le_localIntGL w i) a ∘ₗ cutInclusion w K ρ i =
      cutInclusion w K ρ i ∘ₗ T := by
    ext y
    simp [coe_offAction_apply, coe_cutInclusion_apply, hT]
  rw [End.mul_eq_comp, ← comp_assoc, h_restrict, trace_comp_comm', ← comp_assoc,
    meanAt_comp_cutInclusion, id_comp]

/-- Let `K` contain the maximal compact subgroup at the split place `w` and let `a` map the space of
vectors fixed by the part of `K` off `w` to itself. On the level cut by the stabiliser of the `i`-th
coordinate line at `w`, the `l`-th power of the operator of `a` times `(T⁺) ^ m` (`T⁺ = raiseAt`)
is the action of the group algebra element obtained from `lineHecke w i ^ m` by `ofSplitPlace`
(placing it at `w`), times the one obtained from `a ^ l` by `offPlace` (taking the part off `w`). -/
lemma coe_offAction_pow_mul_raiseAt_pow_apply (hK : maxCompactAt n w ≤ K) (i : n)
    (a : levelAlgebra (offRep hw ρ) K) (l m : ℕ)
    (y : levelSpace ρ (cutLevel K w (lineStabilizer w i))) :
    ((offAction hw ρ hK (lineStabilizer_le_localIntGL w i) a ^ l * raiseAt hw ρ hK i ^ m) y : M) =
      ρ.asAlgebraHom (mapDomain (ofSplitPlace hw) (lineHecke w i ^ m) *
        mapDomain (offPlace hw) ((a : ℂ[Gf E n]) ^ l)) y := by
  simp only [raiseAt, ← map_pow, coe_offAction_mul_localAction_apply, SubmonoidClass.coe_pow]

end Algebraic

variable {K : Subgroup (Gf E n)} {M M' : Type}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [NormedAddCommGroup M'] [InnerProductSpace ℂ M']
  {ρ : Representation ℂ (Gf E n) M} {ρ' : Representation ℂ (Gf E n) M'} [IsLevel K]

/-- Let `K` contain the maximal compact subgroup at the split place `w`, whose residue field has
`q` elements, and let `a` map the vectors fixed by the part of `K` off `w` to themselves. In a
unitary representation, on the level cut by the stabiliser of a line at `w`, the operator `A` of
`a`, the operators `T⁺`, `T⁻` and the mean `e` over `GL_n(𝒪_w)` satisfy `LineRelation d c` with
`d = q ^ (n - 2)` and `c = q ^ n - 1`: `T⁻` is adjoint to `T⁺`, `T⁺ T⁻ = d (1 + c e)`, `e` is
idempotent, and `A` commutes with `T⁺` and `T⁻`. -/
lemma lineRelation_offAction (hw : w.IsSplit) (hK : maxCompactAt n w ≤ K) (i : n)
    (hρ : ∀ (g : Gf E n) (x y : M), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (a : levelAlgebra (offRep hw ρ) K) :
    LineRelation ((w.q : ℝ) ^ (Fintype.card n - 2 : ℤ)) ((w.q : ℝ) ^ Fintype.card n - 1)
      (offAction hw ρ hK (lineStabilizer_le_localIntGL w i) a) (raiseAt hw ρ hK i)
        (lowerAt hw ρ hK i)
      (cutInclusion w K ρ i ∘ₗ meanAt hw ρ hK i) := by
  have hq : (1 : ℝ) < w.q := Nat.one_lt_cast.2 w.one_lt_q
  have h_local (y : levelSpace ρ (cutLevel K w (lineStabilizer w i))) :
      (y : M) ∈ levelSpace (localRep hw ρ) (lineStabilizer w i) :=
    ((mem_levelSpace_cutLevel_iff hw ρ hK (lineStabilizer_le_localIntGL w i)).1 y.property).right
  exact
    { d_pos := by positivity
      c_pos := sub_pos.2 (one_lt_pow₀ hq (Fintype.card_pos_iff.2 ⟨i⟩).ne')
      idem := by
        rw [IsIdempotentElem, End.mul_eq_comp, comp_assoc, ← comp_assoc (meanAt hw ρ hK i),
          meanAt_comp_cutInclusion, id_comp]
      adjoint x y := by
        simpa only [Submodule.coe_inner, coe_raiseAt_apply, coe_lowerAt_apply] using
          inner_lineRaise (fun g ↦ hρ (ofSplitPlace hw g)) (h_local x) (h_local y)
      mul_eq := by
        ext y
        simp [coe_raiseAt_apply, coe_lowerAt_apply, lineRaise_lineLower (h_local y),
          ← coe_cutInclusion_meanAt_apply hw ρ hK i]
      commute_plus := commute_offAction_localAction hw ρ hK (lineStabilizer_le_localIntGL w i) a _
      commute_minus :=
        commute_offAction_localAction hw ρ hK (lineStabilizer_le_localIntGL w i) a _ }

/-- Let the level `K` contain the maximal compact subgroup at the split place `w`, and let `a` be
in `universalLevelAlgebra K` (it maps the space of `K`-fixed vectors to itself in every
representation) and be a combination of elements that are integral at `w`. Consider two unitary
representations whose spaces of vectors of level `K'`, the level cut by the stabiliser of a line at
`w`, are finite-dimensional. Suppose that for all `l`, `m` the element
`b = (T⁺) ^ (m + 1) * a' ^ (l + 1)` of the group algebra, with `T⁺ = lineHecke w i` placed at `w`
and `a'` the part of `a` off `w`, has the same trace in both at level `K'` (`h_trace`, where `S`,
`S'` are the two operators by which `b` acts there). Then `a` has the same trace at level `K` in
both. -/
theorem trace_eq_of_trace_cutLevel_eq (hw : w.IsSplit) (hK : maxCompactAt n w ≤ K) (i : n)
    (hρ : ∀ (g : Gf E n) (x y : M), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hρ' : ∀ (g : Gf E n) (x y : M'), ⟪ρ' g x, ρ' g y⟫_ℂ = ⟪x, y⟫_ℂ)
    [Module.Finite ℂ (levelSpace ρ (cutLevel K w (lineStabilizer w i)))]
    [Module.Finite ℂ (levelSpace ρ' (cutLevel K w (lineStabilizer w i)))]
    {a : ℂ[Gf E n]} (ha : a ∈ universalLevelAlgebra K)
    (h_int : a ∈ spanOn ℂ {g : Gf E n | g.atPlace w ∈ localIntGL n w})
    (h_trace : ∀ (l m : ℕ) (S : End ℂ (levelSpace ρ (cutLevel K w (lineStabilizer w i))))
      (S' : End ℂ (levelSpace ρ' (cutLevel K w (lineStabilizer w i)))),
      let K' : Subgroup (Gf E n) := cutLevel K w (lineStabilizer w i)
      let b : ℂ[Gf E n] := mapDomain (ofSplitPlace hw) (lineHecke w i ^ (m + 1)) *
        mapDomain (offPlace hw) (a ^ (l + 1))
      (∀ y : levelSpace ρ K', (S y : M) = ρ.asAlgebraHom b y) →
      (∀ y : levelSpace ρ' K', (S' y : M') = ρ'.asAlgebraHom b y) →
        trace ℂ (levelSpace ρ K') S = trace ℂ (levelSpace ρ' K') S')
    {T : End ℂ (levelSpace ρ K)} {T' : End ℂ (levelSpace ρ' K)}
    (hT : ∀ y : levelSpace ρ K, (T y : M) = ρ.asAlgebraHom a y)
    (hT' : ∀ y : levelSpace ρ' K, (T' y : M') = ρ'.asAlgebraHom a y) :
    trace ℂ (levelSpace ρ K) T = trace ℂ (levelSpace ρ' K) T' := by
  let a₁ : levelAlgebra (offRep hw ρ) K := ⟨a, universalLevelAlgebra_le K (offRep hw ρ) ha⟩
  let a₂ : levelAlgebra (offRep hw ρ') K := ⟨a, universalLevelAlgebra_le K (offRep hw ρ') ha⟩
  -- Vectors of level `K` are spherical at `w`, so `a` acts on them through its part off `w`.
  have hT_off (y : levelSpace ρ K) : (T y : M) = (offRep hw ρ).asAlgebraHom a y :=
    (hT y).trans (asAlgebraHom_offRep_apply hw ρ h_int (levelSpace_anti hK y.property)).symm
  have hT_off' (y : levelSpace ρ' K) : (T' y : M') = (offRep hw ρ').asAlgebraHom a y :=
    (hT' y).trans (asAlgebraHom_offRep_apply hw ρ' h_int (levelSpace_anti hK y.property)).symm
  rw [← trace_offAction_mul_mean hw ρ hK i a₁ hT_off,
    ← trace_offAction_mul_mean hw ρ' hK i a₂ hT_off']
  -- By the line relation it suffices to compare the traces of the products of positive powers.
  refine (lineRelation_offAction hw hK i hρ a₁).trace_mul_mean_eq
    (lineRelation_offAction hw hK i hρ' a₂) fun l m ↦ ?_
  exact h_trace l m _ _ (coe_offAction_pow_mul_raiseAt_pow_apply hw ρ hK i a₁ (l + 1) (m + 1))
    (coe_offAction_pow_mul_raiseAt_pow_apply hw ρ' hK i a₂ (l + 1) (m + 1))

end New

end
end
end

/-!
# Comparison of traces for a cuspidal test function

The comparison of traces `trace_comparison` asks for a test function that is cuspidal at a split
place `w` and is supported at a second place on elements whose characteristic polynomial has a
simple zero at `0` modulo that place. The second condition is removed here: at an auxiliary split
place `v` the level is cut down to the stabiliser of a line, where `T⁺ = lineHecke` forces the
simple zero and counts the spherical vectors through its determinant (`trace_eq_of_isCuspidalAt`).

## Relation to the literature

Known; see `Lib.Adelic.TraceFormula.TraceComparison` for sources.
-/

@[expose] public section

noncomputable section

namespace New

open NumberField Module LinearMap MonoidAlgebra Filter Variety Fintype

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]

/-- An element `a` of the group algebra of the finite adelic group is integral at almost all places
`v`: it is a combination of group elements whose component at `v` lies in
`localIntGL n v = GL_n(O_v)`. -/
lemma eventually_mem_spanOn_atPlace_mem_localIntGL (a : ℂ[Gf E n]) :
    ∀ᶠ v : FinPlace E in cofinite, a ∈ spanOn ℂ {g : Gf E n | g.atPlace v ∈ localIntGL n v} := by
  have h_support : ∀ᶠ v : FinPlace E in cofinite,
      ∀ g ∈ a.coeff.support, g.atPlace v ∈ localIntGL n v :=
    a.coeff.support.eventually_all.2 fun g _ ↦ g.eventually_atPlace_mem_localIntGL
  filter_upwards [h_support] with v hv
  exact Submodule.span_mono (Set.image_mono fun g hg ↦ hv g hg) a.mem_span_support_coeff

variable [HasPrimitiveRoot5040 E]

/-- The auxiliary place: let `E` contain the 5040th roots of unity. For an open subgroup `K`, an
element `a` of the group algebra and a place `w`, some split place `v` is neither `w` nor its
conjugate, `K` contains `maxCompactAt n v` (the integral elements that are `1` away from `v` and its
conjugate), and `a` is a combination of elements that are integral at `v`. -/
lemma exists_auxiliary_place {K : Subgroup (Gf E n)} (hK : K.IsOpen) (a : ℂ[Gf E n])
    (w : FinPlace E) :
    ∃ v : FinPlace E, v.IsSplit ∧
      v ∉ Set.conjClosure {w} ∧
      maxCompactAt n v ≤ K ∧
      a ∈ spanOn ℂ {g : Gf E n | g.atPlace v ∈ localIntGL n v} := by
  -- There are infinitely many split places, and the other conditions hold at almost all places.
  have h_split : ∃ᶠ v : FinPlace E in cofinite, v.IsSplit :=
    frequently_prime_q.mono fun _ ↦ isSplit_of_q_prime
  have h_ne : ∀ᶠ v : FinPlace E in cofinite, v ∉ Set.conjClosure {w} :=
    (Set.finite_singleton w).conjClosure.eventually_cofinite_notMem
  exact (h_split.and_eventually (h_ne.and ((eventually_maxCompactAt_le hK).and
    (eventually_mem_spanOn_atPlace_mem_localIntGL a)))).exists

variable [Nonempty n] {s s' : n → ℤˣ}

/-- Comparison of traces without the condition at a second place. Let the CM field `E` contain the
5040th roots of unity and have an even number of infinite places, let `V`, `V'` be hermitian spaces
of rank `N = card n ≥ 2` over `E` with signs `s`, `s'`, and let `l = 2λ` be a doubled Harish-Chandra
parameter whose `toHCParam s (l v)` and `toHCParam s' (l v)` have gap at least `500 N³ + 10 N⁵` at
every infinite place `v` (`HasLargeGap A` means gap `500 N³ + A`). Let `K` be a level (`IsLevel K`,
so `K` is open and compact), let `a` keep the `K`-fixed vectors in every representation
(`universalLevelAlgebra K`), and let the test function `a ⋆ 1_K` (`convIndicator`) be cuspidal at a
split place `w`. Then operators that act as `a` on the forms of parameter `l` and level `K`
(`levelSpace` of `formRep` at `typeKernel l s`, resp. `typeKernel l s'`, which the gap bound makes a
cusp kernel by `isCuspKernel_typeKernel`) on `V` and on `V'` have the same trace. -/
theorem trace_eq_of_isCuspidalAt (hE : Even (Core.numInfPlaces E)) (hn : 2 ≤ card n)
    (V : Space E n s) (V' : Space E n s') {l : InfinitePlace E → n → ℤ}
    (h_gap : ∀ v : InfinitePlace E, (toHCParam s (l v)).HasLargeGap (10 * card n ^ 5))
    (h_gap' : ∀ v : InfinitePlace E, (toHCParam s' (l v)).HasLargeGap (10 * card n ^ 5))
    {K : Subgroup (Gf E n)} [hK : IsLevel K] {a : ℂ[Gf E n]} (ha : a ∈ universalLevelAlgebra K)
    {w : FinPlace E} (hw : w.IsSplit)
    (h_cusp : IsCuspidalAt hw (convIndicator hK.isOpen hK.isCompact a))
    {T : End ℂ (levelSpace (V.formRep (typeKernel l s)) K)}
    (hT : ∀ y : levelSpace (V.formRep (typeKernel l s)) K,
      (T y).val = (V.formRep (typeKernel l s)).asAlgebraHom a y.val)
    {T' : End ℂ (levelSpace (V'.formRep (typeKernel l s')) K)}
    (hT' : ∀ y : levelSpace (V'.formRep (typeKernel l s')) K,
      (T' y).val = (V'.formRep (typeKernel l s')).asAlgebraHom a y.val) :
    trace ℂ (levelSpace (V.formRep (typeKernel l s)) K) T =
      trace ℂ (levelSpace (V'.formRep (typeKernel l s')) K) T' := by
  -- Cut the level at an auxiliary split place `v` down to the stabiliser of a line. There the
  -- positive powers of `T⁺ = lineHecke v i` make `0` a simple root modulo `v` of the
  -- characteristic polynomial on the support, so `trace_comparison` applies.
  obtain ⟨v, hv, hv_ne, h_max, h_int⟩ := exists_auxiliary_place hK.isOpen a w
  obtain ⟨i⟩ : Nonempty n := inferInstance
  let K' : OpenSubgroup (Gf E n) := ⟨cutLevel K v (lineStabilizer v i), IsLevel.isOpen⟩
  have : Module.Finite ℂ (levelSpace (V.formRep (typeKernel l s)) K'.toSubgroup) :=
    V.finite_levelSpace (isCuspKernel_typeKernel h_gap) K'
  have : Module.Finite ℂ (levelSpace (V'.formRep (typeKernel l s')) K'.toSubgroup) :=
    V'.finite_levelSpace (isCuspKernel_typeKernel h_gap') K'
  refine trace_eq_of_trace_cutLevel_eq hv h_max i V.inner_formRep V'.inner_formRep ha h_int
    (fun j m S S' hS hS' ↦ ?_) hT hT'
  refine trace_comparison hE hn V V' h_gap h_gap' (w' := v) hw ?_ (fun g hg ↦ ?_) hS hS'
  · -- Cuspidality at `w` survives the cut at `v` and convolution on the left.
    obtain ⟨h_ne, h_star_ne⟩ : v ≠ w ∧ star v ≠ w := not_or.1 hv_ne
    rw [pow_succ a, mapDomain_mul, ← mul_assoc]
    exact (h_cusp.convIndicator_offPlace hv h_ne h_star_ne h_max h_int).convIndicator_mul _
  · -- At `v` an element of the support is `x * k` with `k` in the stabiliser of a line and `x` in
    -- a set that carries the positive powers of `T⁺` and on which `x * k` has a simple zero.
    obtain ⟨x, hx, k, hk, h_eq⟩ : ∃ x ∈ {x : GL n (LocField v) |
        ∀ k ∈ lineStabilizer v i, HasSimpleZero (x * k)},
        ∃ k ∈ lineStabilizer v i, g.atPlace v = x * k :=
      exists_atPlace_eq_of_convIndicator_ne_zero hv
        (lineHecke_pow_mem_spanOn v i m.succ_pos) (a ^ (j + 1)) hg
    rw [h_eq]
    exact hx k hk

end New

end
