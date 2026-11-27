module

import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.Weil.CompactLift.ThetaKernelDefs
public import Lib.Weil.Lift
import Lib.Adelic.AutomorphicForms.AutomorphicAsAlgebraic
import Lib.Adelic.Reduction.DefiniteClassSums
import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
import Lib.DiscreteSeries.Theta.LocalCorrespondence
import Lib.GLn.SchurModule.GramMatrix
import Lib.Shimura.Uniformisation.HolomorphicFamilies

/-!
# Theta lifts between definite unitary groups and algebraic lifts by jets

This file studies the theta correspondence from the definite space `I_n` to `I_n'` (`New.stdSpace`),
for a weight that goes up from rank `n` to the larger rank `n'` (`New.IsLiftWeight`). There are two
lifts between these groups. The theta lift is an integral of a theta kernel over `[U(n)]`, and the
algebraic lift is a class sum with the matrix of jets `New.thetaKernel`.

## Main definitions and results

* `New.IsHCParam.paramsCorrespond_iff`: the parameter `l` of the weight in rank `n` corresponds to
  `l'` (`New.ParamsCorrespond`) exactly when `l'` is the parameter of the weight `(κ, ea)` in rank
  `n'`, with the same columns `κ`.
* `New.exists_lift_ofAlgForm_eq_smul`: the analytic theta lift `New.Space.lift` with the joint
  harmonic `New.jointHarmonic` as real datum is a constant (possibly zero), divided by the index of
  the level, times the lift `New.Kernel.lift` of algebraic forms by `New.thetaKernel`.
* `New.isThetaLift_thetaKernel`: the lifts of the kernels of jets are theta lifts in the sense of
  `New.Space.IsThetaLift`.

Notions from other files:
* `New.IsLiftWeight`: `n < n'`, no column of `κ` has height strictly between the two ranks, and the
  exponent in rank `n` is `eb` plus the number `κ w (card n)` of columns of height `n`.
* `New.thetaKernel`: the kernel whose matrix at a finite datum is made of the Taylor coefficients
  (jets) of its theta series, paired with Schur polynomials.
* `New.IsHCParam`: `l` lists twice the Harish-Chandra parameter of the weight `(κ, e)`, in some
  order: at each place `w` the numbers `l w i` are distinct, and each of them is
  `hcParameter κ e (card n) w p` for some position `p < card n`.
* `New.stdSpace`: the definite space `I_n`, the sum of `n` norms with its standard lattice.

## Relation to the literature

Known result: Theta lift for a definite unitary pair as a class sum on algebraic modular forms. The
pair is U(n)×U(n′) over a CM field with `New.WeilData`, n < n′, and the kernel is the matrix of
Taylor coefficients of the theta function against Schur polynomials. The constant is left
unspecified. Source: B. Gross, Algebraic modular forms, Israel J. Math. 113 (1999); Kashiwara–Vergne
1978; R. Howe, Transcending classical invariant theory, JAMS 2 (1989).
-/

@[expose] public section

/-! ## The harmonic theta lift of definite spaces as a multiple of the algebraic lift -/

section DefiniteLift

open NumberField Matrix Finset MvPolynomial Fintype New.Space

variable {E n n' : Type} [Field E] [NumberField E] [Fintype n] [Fintype n']
  {κ : InfinitePlace E → ℕ → ℕ} {l : InfinitePlace E → n → ℤ} {l' : InfinitePlace E → n' → ℤ}
  {ea eb ec : InfinitePlace E → ℤ}

/-- The image of `l w` under a map `f`, for `l` twice the Harish-Chandra parameter of `(κ, ec)`
(`New.IsHCParam`), is the image of the first `card n` values of `hcParameter`. -/
lemma New.IsHCParam.image_comp_eq (h : IsHCParam κ ec l) (w : InfinitePlace E) (f : ℤ → ℤ) :
    univ.image (fun i : n ↦ f (l w i)) =
      (range (card n)).image (fun p : ℕ ↦ f (hcParameter κ ec (card n) w p)) := by
  classical
  simpa [image_image, Function.comp_def] using congrArg (image f) (h.image_eq w)

/-- Theta correspondence of definite spaces of ranks `n < n'`. Let `E` be a number field, let
`κ τ h` be the number of columns of height `h` at the infinite place `τ`, and let the weight
`(κ, ec)` go up from rank `n` to rank `n'` along `eb` (`New.IsLiftWeight`): `card n < card n'`, no
column has height strictly between `card n` and `card n'`, and `ec τ = eb τ + κ τ (card n)`. Let `l`
be the parameter of `(κ, ec)`, that is, twice its Harish-Chandra parameter in some order; then `l`
and `l'` correspond (`New.ParamsCorrespond`: the block rule `New.IsBlockRule` (for `n ≤ n'`, among
its conditions: the entries `l' w - 2 ea w + card n` are those of `l w - 2 eb w + card n'` plus
`doubledBlock (card n' - card n)`) holds at every infinite place, for the signs `1` and characters
of U(1) of weights `ea`, `eb`) exactly when `l'` is the parameter of `(κ, ea)`. -/
lemma New.IsHCParam.paramsCorrespond_iff (hl : IsHCParam κ ec l) (hκ : IsLiftWeight n n' κ eb ec) :
    ParamsCorrespond (n := n) (n' := n') ea eb l l' 1 1 ↔ IsHCParam κ ea l' := by
  classical
  obtain ⟨fits, h_lt, rfl⟩ := hκ
  -- No column has height strictly between the two ranks.
  have sum_eq (w : InfinitePlace E) (p : ℕ) :
      ∑ x ∈ Ioo p (card n'), κ w x = ∑ x ∈ Ioc p (card n), κ w x :=
    (sum_subset (Ioc_subset_Ioo_right h_lt) fun x hx hnx ↦
      (fits w).2 x (mem_Ioo.2 ⟨not_le.1 fun hle ↦
        hnx (mem_Ioc.2 ⟨(mem_Ioo.1 hx).1, hle⟩), (mem_Ioo.1 hx).2⟩)).symm
  -- The shifted entries of the parameter of `(κ, ea)` in rank `n'`, in decreasing order.
  let entry (w : InfinitePlace E) (p : ℕ) : ℤ :=
    hcParameter κ ea (card n') w p - 2 * ea w + card n
  -- The first `card n` of them are positive, and they are the shifted entries of `l`.
  have h_low (w : InfinitePlace E) (p : ℕ) (hp : p < card n) :
      hcParameter κ (fun τ ↦ eb τ + κ τ (card n)) (card n) w p - 2 * eb w + card n' = entry w p ∧
        0 < entry w p := by
    have h_split : (Ioo p (card n)).sum (κ w) + κ w (card n) = ∑ x ∈ Ioc p (card n), κ w x :=
      sum_Ioo_add_eq_sum_Ioc hp
    simp only [entry, hcParameter, diagramWeight_apply, sum_eq]
    omega
  -- The others form the block `[n' - n]`.
  have h_high (w : InfinitePlace E) (p : ℕ) (hp : card n ≤ p) :
      entry w p = card n' + card n - 1 - 2 * p := by
    simp only [entry, hcParameter, diagramWeight_apply, sum_eq, Ioc_eq_empty hp.not_gt,
      Finset.sum_empty]
    omega
  have h_entries (w : InfinitePlace E) :
      univ.image (shiftedEntry (eb w) (card n') (l w)) ∪ doubledBlock (card n' - card n) =
        (range (card n')).image (entry w) := by
    have h_small : univ.image (shiftedEntry (eb w) (card n') (l w)) =
        (range (card n)).image (entry w) :=
      (hl.image_comp_eq w fun y : ℤ ↦ y - 2 * eb w + card n').trans
        (image_congr fun p hp ↦ (h_low w p (mem_range.1 hp)).1)
    have h_block : doubledBlock (card n' - card n) = (Ico (card n) (card n')).image (entry w) := by
      ext y
      simp only [doubledBlock, mem_image, mem_range, mem_Ico]
      refine ⟨fun ⟨b, hb, hy⟩ ↦ ⟨card n + b, ⟨Nat.le_add_right .., by omega⟩, ?_⟩,
        fun ⟨p, hp, hy⟩ ↦ ⟨p - card n, by omega, ?_⟩⟩
      · rw [h_high w (card n + b) (Nat.le_add_right ..)]
        omega
      · rw [h_high w p hp.1] at hy
        omega
    rw [h_small, h_block, ← image_union, range_eq_Ico, range_eq_Ico,
      Ico_union_Ico_eq_Ico (Nat.zero_le _) h_lt.le]
  constructor
  · intro h_rule w
    refine ⟨(h_rule w).hasGap_right.injective, fun r ↦ ?_⟩
    obtain ⟨p, hp, h_eq⟩ :
        ∃ p ∈ range (card n'), entry w p = shiftedEntry (ea w) (card n) (l' w) r :=
      mem_image.1 (by
        rw [← h_entries, ← (h_rule w).entries_of_le h_lt.le]
        exact mem_image_of_mem _ (mem_univ r))
    exact ⟨p, mem_range.1 hp, by simp only [entry, shiftedEntry] at h_eq; omega⟩
  · intro hl' w
    refine ⟨hl.hasGap w _, hl'.hasGap w _, fun _ ↦ ?_, fun h_ge ↦ absurd h_lt h_ge.not_gt,
      -- The signs are all `1`; the last condition concerns negative shifted entries of `l`.
      fun _ _ _ _ ↦ rfl, fun c _ _ h_neg ↦ ?_⟩
    · exact (hl'.image_comp_eq w fun y : ℤ ↦ y - 2 * ea w + card n).trans (h_entries w).symm
    · -- A shifted entry of `l` is positive, so it is not negative.
      obtain ⟨p, hp, hc⟩ : ∃ p < card n, l w c = hcParameter κ _ (card n) w p := (hl w).2 c
      have ⟨h_eq, h_pos⟩ := h_low w p hp
      rw [shiftedEntry] at h_neg
      change l w c - 2 * eb w + card n' < 0 at h_neg
      rw [hc, h_eq] at h_neg
      omega

/-- The joint harmonic is a multiple of the Fock polynomial of two highest vectors. Let `E` be a CM
field with Weil data, let the weight `(κ, ec)` of rank `n` go up to rank `n'` along `eb`, and let
`l`, `l'` be parameters of `(κ, ec)` and `(κ, ea)`. Then `jointHarmonic ea eb l l' 1 1` is a
multiple of `schurCoeffPoly` at the highest vectors of `l` and of `l'`, the latter paired by the
Gram matrix `weylGramOver` of the weight. `jointHarmonic ea eb l l' 1 1` is the product over the
infinite places `w` of the chosen polynomials `jointHarmonicAt`, each in the variables of `w` and,
by `isJointHarmonic_jointHarmonicAt`, a joint highest vector for the match of `l' w` with `-l w`.
Here a parameter is twice the Harish-Chandra parameter, and `schurCoeffPoly A ξ` is the polynomial
`z ↦ Aᵀ S_κ(z) ξ` for the Schur matrix `S_κ`. -/
lemma New.exists_smul_schurCoeffPoly_eq_jointHarmonic {E : Type} [Field E] [CMType E]
    {κ : InfinitePlace E → ℕ → ℕ} {l : InfinitePlace E → n → ℤ} {l' : InfinitePlace E → n' → ℤ}
    {ea eb ec : InfinitePlace E → ℤ} [DecidableEq n'] [DecidableEq n]
    (hl : IsHCParam κ ec l) (hl' : IsHCParam κ ea l')
    (hκ : IsLiftWeight n n' κ eb ec) :
    ∃ β : ℂ, β • schurCoeffPoly (highestVector κ l' ᵥ* weylGramOver) (highestVector κ l) =
      jointHarmonic ea eb l l' 1 1 := by
  have h_match : ∀ w : InfinitePlace E, IsMatch (.std 1 1 (ea w) (-eb w)) (l' w) (-l w) :=
    ((hl.paramsCorrespond_iff hκ).2 hl').isMatch
  -- The exponents `κ w i` vanish for `card n < i < card n'`; for the sign `-1` all are zero.
  have h_cols (w : InfinitePlace E) (η : ℤˣ) : ∀ i : ℕ, card {j : n // (1 : n → ℤˣ) j = η} < i →
      i < card n' → (Pi.single 1 (κ w) : ℤˣ → ℕ → ℕ) η i = 0 := by
    intro i h_low h_high
    fin_cases η
    · simpa using (hκ.1 w).2 i (mem_Ioo.2 ⟨by simpa using h_low, h_high⟩)
    · simp
  -- `M w p` is the block of variables on the first `p` rows and columns, ordered by decreasing
  -- `l' w` and `l w`.
  let M (w : InfinitePlace E) (p : ℕ) : Matrix (Fin p) (Fin p) (MvPolynomial (n' × n) ℂ) :=
    of fun i j ↦ ∑ a : n', ∑ c : n,
      if decreasingPosition (l' w) a = i ∧ decreasingPosition (l w) c = j then X (a, c) else 0
  -- The staircase product of the minors is a joint harmonic, so by uniqueness the chosen joint
  -- harmonic at `w` is a multiple of it.
  have h_stair (w : InfinitePlace E) : ∃ u : ℂ, jointHarmonicAt ea eb l l' 1 1 w =
      u • ∏ p : Fin (card n'), (M w p).det ^ κ w p := by
    have h_highest := isJointHighest_prod_det_pow_staircaseWeight (s := 1) (γ := ea w) (γ' := -eb w)
      (ν := HCParam.lowestKType (ε := 1) (l' w)) (o := decreasingPosition (l w))
      (hl w).1 (hl' w).1 (by simp [decreasingPosition]) _ (h_cols w) (by simp)
      (by simp [hl'.lowestKType_eq, diagramWeight_apply, vacuumWeight])
    have h_M (p : Fin (card n')) :
        staircaseBlock (1 : n → ℤˣ) (decreasingPosition (l w)) (l' w) 1 p = M w p := by
      ext i j
      simp only [staircaseBlock, M, of_apply, Units.val_one, one_smul, Pi.one_apply, true_and]
    have h_prod : (∏ η : ℤˣ, ∏ p : Fin (card n'),
        (staircaseBlock (1 : n → ℤˣ) (decreasingPosition (l w)) (l' w) η p).det ^
          (Pi.single 1 (κ w) : ℤˣ → ℕ → ℕ) η p) =
        ∏ p : Fin (card n'), (M w p).det ^ κ w p := by
      rw [Fintype.prod_eq_single (1 : ℤˣ) fun η hη ↦ prod_eq_one fun p _ ↦ by
        rw [Pi.single_eq_of_ne hη, Pi.zero_apply, pow_zero]]
      refine prod_congr rfl fun p _ ↦ ?_
      rw [Pi.single_eq_same, h_M p]
    rw [← h_prod]
    exact (h_match w).unique
      (isJointHarmonic_jointHarmonicAt (h_match w)).isJointHighest.isPreJointHarmonic
      h_highest.isPreJointHarmonic
  choose u hu using h_stair
  -- The Schur matrix of `x`, times the scalar `d`, maps the evaluation vector at the array `y` to
  -- the evaluation vector at the product `x y` (`schur_mulVec_weylEval`).
  let y : ((_ : InfinitePlace E) × n) × ℕ → ℂ := permArray fun w ↦ decreasingPosition (l w)
  let d : ℂ := (detPow ℂ (fun _ ↦ n) (schurDetExp (fun _ ↦ n) (fun _ ↦ n') κ)).eval y
  refine ⟨(∏ w : InfinitePlace E, u w) * d, funext fun x ↦ ?_⟩
  have h_schur : d * eval x (schurCoeffPoly (highestVector κ l' ᵥ* weylGramOver) (weylEval _ κ y)) =
      ∏ w : InfinitePlace E, ∏ p : Fin (card n'),
        eval (fun v : n' × n ↦ x (w, v)) (M w p)ᵀ.det ^ κ w p := by
    rw [eval_schurCoeffPoly hκ, ← smul_eq_mul, ← dotProduct_smul, schur_mulVec_weylEval hκ.1,
      highestVector, ← dotProduct_mulVec, ← GL.eval_toPoly, toPoly_weylEval, weylKernel,
      highestPoly, map_prod, map_prod]
    refine prod_congr rfl fun w _ ↦ ?_
    rw [tableauPoly, map_prod, map_prod]
    refine prod_congr rfl fun p _ ↦ ?_
    rw [prod_const, Finset.card_fin, map_pow, map_pow, minor, AlgHom.map_det, RingHom.map_det,
      RingHom.map_det]
    congr 2
    ext i j
    simp only [M, y, RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.transpose_apply, of_apply, Function.comp_apply, rowSubst, aeval_X, map_sum, eval_X,
      smul_eq_C_mul, map_mul, eval_C, permArray, Fin.val_castLE, sum_mul, mul_ite, mul_one,
      mul_zero, apply_ite (eval _), map_zero, ite_and]
  rw [smul_eval, mul_assoc, highestVector.eq_def κ l, h_schur]
  simp only [jointHarmonic, hu, map_prod, eval_rename, Function.comp_def, smul_eq_C_mul,
    map_mul, eval_C, prod_mul_distrib, map_pow, det_transpose]

/-- The harmonic theta lift is a multiple of the algebraic lift. Let the weight `(κ, ec)` of rank
`n` go up to rank `n'` along `eb`, let `l`, `l'` be the parameters (twice the Harish-Chandra
parameters) of `(κ, ec)` and `(κ, ea)`, and let `c ≠ 0` be the scale of the jets, the Taylor
coefficients of theta series. There is a number `β` (possibly zero) with the following property for
all characters `a`, `b` of weights `ea`, `eb` (with characters `ψ`, `ψ'` of the residue fields at
the finite places, as in `HasWeight`), every level `K`, every finite datum `f` and every algebraic
form `φ`. The theta lift of the function `F_φ = ofAlgForm l 1 φ` with datum (joint harmonic) ⊗ `f`
is `β / [K₀ : K ∩ K₀]` times `F_φ'`. Here `K₀ = stdLevel E n`, and `φ'` is the lift of `φ` at `f` by
the kernel `New.thetaKernel hκ c ha hb K`, for the measure that gives `K` volume `1`. -/
lemma New.exists_lift_ofAlgForm_eq_smul {E : Type} [Field E] [CMType E]
    {κ : InfinitePlace E → ℕ → ℕ} {l : InfinitePlace E → n → ℤ} {l' : InfinitePlace E → n' → ℤ}
    {ea eb ec : InfinitePlace E → ℤ} [DecidableEq n'] [DecidableEq n] [WeilData E]
    (hl : IsHCParam κ ec l) (hl' : IsHCParam κ ea l') (hκ : IsLiftWeight n n' κ eb ec)
    {c : ℂ} (hc : c ≠ 0) :
    ∃ β : ℂ, ∀ {a b : AutChar E} {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ}
        (ha : a.HasWeight ea ψ) (hb : b.HasWeight eb ψ') (K : Subgroup (Gf E n)) [IsLevel K]
        (f : ((stdSpace E n).hom (stdSpace E n')).finitePart) (φ : AlgForm n κ ec),
      lift (pairThetaKer (stdSpace E n) (stdSpace E n') a b)
          (integrated ((stdSpace E n).hom (stdSpace E n')) (jointHarmonic ea eb l l' 1 1) f)
          (ofAlgForm l 1 φ) =
        (β / stdLevelIndex K) • ofAlgForm l' 1 ((thetaKernel hκ c ha hb K).lift f φ) := by
  -- As the joint harmonic is a multiple of the Fock polynomial of the two highest vectors, the
  -- theta function is a matrix coefficient in the real variable, and
  -- `integral_mul_eq_classIntegral` turns the integral into a mean over the finite points.
  obtain ⟨β, hβ⟩ := exists_smul_schurCoeffPoly_eq_jointHarmonic hl hl' hκ
  let d : ℂ := β / c ^ boxes κ (card n')
  -- The factor `(card (WeylIndex n κ))⁻¹` comes from `integral_mul_eq_classIntegral`.
  refine ⟨d / card (WeylIndex n κ), fun {a b ψ ψ'} ha hb K _ f φ ↦ ?_⟩
  set k : Kernel n n' κ ec ea K ((stdSpace E n).hom (stdSpace E n')).finitePart :=
    thetaKernel hκ c ha hb K with hk
  ext ⟨y, z⟩
  -- The theta function `Θ` of the first variable is automorphic, as `f` has a level `J`.
  let Φ := integrated ((stdSpace E n).hom (stdSpace E n')) (jointHarmonic ea eb l l' 1 1) f
  let Θ (g : G E 1) : ℂ := θ _ (pairWeil (stdSpace E n) (stdSpace E n') a b (g, y, z) Φ)
  obtain ⟨J, J', hJ⟩ : ∃ (J : OpenSubgroup (Gf E n)) (J' : OpenSubgroup (Gf E n')),
      ∀ g ∈ J, ∀ g' ∈ J', pairWeil (stdSpace E n) (stdSpace E n') a b ((1, g), 1, g') f = f :=
    exists_level_pairWeil a b f.property
  -- An element of `J` acts on the finite part only, and fixes `f`.
  have Φ_fixed (g : Gf E n) (hg : g ∈ J) :
      pairWeil (stdSpace E n) (stdSpace E n') a b ((1, g), 1, 1) Φ = Φ := by
    rw [pairWeil_integrated_fin, hJ g hg 1 (one_mem J')]
  have Θ_aut : (stdSpace E n).IsAutomorphic Θ :=
    (pairThetaKer (stdSpace E n) (stdSpace E n') a b).isAutomorphic J Φ_fixed (y, z)
  -- In the real variable, `Θ` is a coefficient at the highest vector
  -- (`theta_pairWeil_schurCoeffPoly`); rescaling the jets by `c` gives the power of `c` in `d`.
  let L : (WeylIndex n' κ → ℂ) →ₗ[ℂ] ℂ :=
    d • gramForm (highestVector κ l') ∘ₗ conjWeylRep κ ea y⁻¹
  have Θ_coef (x : GInf E 1) (g : Gf E n) :
      Θ (x, g) = (L ∘ₗ k.jetMap (k.ω (g, z) f)) (conjWeylRep κ ec x (highestVector κ l)) := by
    have h_th := theta_pairWeil_schurCoeffPoly hκ c ha hb x g y z
      (highestVector κ l' ᵥ* weylGramOver) (highestVector κ l) f
    have h_val : Θ (x, g) = β * ((stdSpace E n).hom (stdSpace E n')).θ
        (pairWeil (stdSpace E n) (stdSpace E n') a b ((x, g), y, z)
          (integrated ((stdSpace E n).hom (stdSpace E n'))
            (Fock.polyVector (realSigns E (homSigns 1 1))
              (schurCoeffPoly (highestVector κ l' ᵥ* weylGramOver) (highestVector κ l))) f)) := by
      simp only [Θ, Φ, ← hβ, LinearMap.map_smul, ContinuousLinearMap.map_smul, _root_.smul_apply,
        smul_eq_mul]
    have h_rhs : (L ∘ₗ k.jetMap (k.ω (g, z) f)) (conjWeylRep κ ec x (highestVector κ l)) =
        d * (highestVector κ l' ᵥ* weylGramOver ⬝ᵥ
          conjWeylRep κ ea y⁻¹ (schurJet κ (jetSeries ((stdSpace E n).hom (stdSpace E n')) c
            (pairWeil (stdSpace E n) (stdSpace E n') a b ((1, g), 1, z) f)) *ᵥ
              conjWeylRep κ ec x (highestVector κ l))) := by
      simp only [L, hk, thetaKernel, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul,
        gramForm_apply, star_highestVector, dotProduct_mulVec, pairWeilFinite]
      rfl
    rw [h_val, h_rhs, ← h_th]
    dsimp only [d]
    rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hc)]
  -- `L` commutes with the mean, which is the value of the algebraic lift at `z`.
  refine (integral_mul_eq_classIntegral hl K Θ_aut _ Θ_coef).trans ?_
  rw [classIntegral_map_mul_right L 1 (k.integrand_mem_smoothInvariants f φ z) (by simp)]
  change _ * L _ = _
  simp only [L, algFormCoeff, Kernel.lift, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.pi_apply, LinearMap.domRestrict_apply, LinearMap.proj_apply, Pi.smul_apply,
    smul_eq_mul, LinearMap.mk₂_apply, div_eq_mul_inv, mul_inv]
  ring

end DefiniteLift

/-! ## The algebraic lift by jets as a theta lift -/

namespace New

open MeasureTheory Space ThetaKernel FiniteDimensional

variable {E n n' : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype n']
  {κ : NumberField.InfinitePlace E → ℕ → ℕ} {e ea eb : NumberField.InfinitePlace E → ℤ}
/-- The theta integral over `[U(n)]` (for `quotMeasure`) against the coefficient of an algebraic
form `φ` at a linear form is additive in the linear form. Here `θ` is the theta functional,
`pairWeil` the Weil action of the pair twisted by `a`, `b`, and `v` any test function. -/
lemma integral_theta_mul_algFormCoeff_add [DecidableEq n'] [DecidableEq n] (a b : AutChar E)
    (v : 𝒮 ((stdSpace E n).hom (stdSpace E n'))) (φ : AlgForm n κ e) (h : G E (1 : n' → ℤˣ))
    (s t : (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ) :
    ∫ g : G E 1, θ ((stdSpace E n).hom (stdSpace E n'))
      (pairWeil (stdSpace E n) (stdSpace E n') a b (g, h) v) *
        algFormCoeff 1 (s + t) φ g ∂(stdSpace E n).quotMeasure =
      (∫ g : G E 1, θ ((stdSpace E n).hom (stdSpace E n'))
        (pairWeil (stdSpace E n) (stdSpace E n') a b (g, h) v) *
        algFormCoeff 1 s φ g ∂(stdSpace E n).quotMeasure) +
      ∫ g : G E 1, θ ((stdSpace E n).hom (stdSpace E n'))
        (pairWeil (stdSpace E n) (stdSpace E n') a b (g, h) v) *
        algFormCoeff 1 t φ g ∂(stdSpace E n).quotMeasure := by
  have h_rapid (L : (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ) :
      algFormCoeff 1 L φ ∈ (stdSpace E n).rapidFunctions :=
    (isAutomorphic_algFormCoeff φ).mem_rapidFunctions fun _ _ ↦ rfl
  rw [← integral_add ((pairThetaKer _ _ a b).integrable_theta_mul (h_rapid s) v h)
    ((pairThetaKer _ _ a b).integrable_theta_mul (h_rapid t) v h)]
  refine integral_congr_ae (.of_forall fun g ↦ ?_)
  simp only [algFormCoeff, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.add_apply, mul_add]
 
/-- Let `(κ, e)` go up from rank `n > 0` to rank `n' > 0` along `eb`, let `a o n` and `a o n'` be
characters at the ranks `n` and `n'` of weights `ea` and `eb` (with residue-field characters `ψ o`,
`ψ' o` at the finite places), let `c ≠ 0` and let `K` be a level. Then the lifts of the kernels of
jets `New.thetaKernel` at the scale `c` compute theta lifts (`New.Space.IsThetaLift`): for every
polynomial `P` and linear form `t` there is one linear form `t'` such that, for every index `o`,
finite datum `Φ` and form `φ`, the coefficient at `t'` of the lift of `φ` is the theta integral,
with datum `P ⊗ Φ`, of the coefficient of `φ` at `t`.

The existence of `t'` for every `P` and `t` is the consequence for theta lifts of Howe's (GL n', GL
n)-duality on polynomials on matrices; the multiplicity formula of the duality is not stated
here. -/
lemma isThetaLift_thetaKernel [Nonempty n] [Nonempty n'] [DecidableEq n'] [DecidableEq n]
    {O : Type*} {a : O → (n : Type) → [Fintype n] → AutChar E} {c : ℂ} {K : Subgroup (Gf E n)}
    [IsLevel K] {hκ : IsLiftWeight n n' κ eb e} (hc : c ≠ 0)
    {ψ ψ' : O → (w : FinPlace E) → MulChar (ResField w) ℂ}
    {ha : ∀ o : O, (a o n).HasWeight ea (ψ o)} {hb : ∀ o : O, (a o n').HasWeight eb (ψ' o)} :
    IsThetaLift κ e ea a fun o : O ↦ (thetaKernel hκ c (ha o) (hb o) K).lift := by
  -- The translates of the highest coefficient span all linear forms `t`, and the claim is linear
  -- in `t`. For a translate, the lift with datum `P` is a convolution over the real points of the
  -- lift with the harmonic datum, and that lift is a multiple of the algebraic one.
  intro P t
  let l (w : NumberField.InfinitePlace E) : HCParam (1 : n → ℤˣ) :=
    fun i ↦ hcParameter κ e (Fintype.card n) w (Fintype.equivFin n i)
  let l' (w : NumberField.InfinitePlace E) : HCParam (1 : n' → ℤˣ) :=
    fun i ↦ hcParameter κ ea (Fintype.card n') w (Fintype.equivFin n' i)
  have hl : IsHCParam κ e l := isHCParam_hcParameter n κ e
  have hl' : IsHCParam κ ea l' := isHCParam_hcParameter n' κ ea
  -- By `New.IsEdge`, the lift with any Fock polynomial is a convolution over the real points of
  -- the lift with the joint harmonic.
  have h_edge : IsEdge (realPairWeil ea eb) (typeKernel l 1) (typeKernel l' 1)
      (jointHarmonic ea eb l l' 1 1) :=
    ((hl.paramsCorrespond_iff hκ).2 hl').isEdge_jointHarmonic
  obtain ⟨β, hβ⟩ := exists_lift_ofAlgForm_eq_smul hl hl' hκ hc
  have h_span : t ∈ Submodule.span ℂ
      (.range fun x ↦ gramForm (highestVector κ l) ∘ₗ conjWeylRep κ e (s := 1) x) := by
    simp [span_gramForm_highestVector_comp_eq_top hl.injective e]
  induction h_span using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨x, rfl⟩ := ht
    -- The translate of `P` by the compact group element `x` is a Fock polynomial, so its lift is a
    -- convolution with some `α`. The linear form asked for is the integral of `T`, where `T u` is
    -- the multiple by `α u * (β / stdLevelIndex K)` of the highest coefficient moved by `u⁻¹`.
    obtain ⟨α, hα⟩ := h_edge.exists_lift_eq_realConv
      (realPairWeil ea eb (x, 1) (Fock.polyVector _ P))
      ⟨_, by
        have h_mem {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) :
            M ∈ blockDiagAlg (1 : m → ℤˣ) := by
          simp [blockDiagAlg, Subalgebra.mem_centralizer_iff]
        rw [realPairWeil_polyVector (hx := fun _ ↦ h_mem _) (hy := fun _ ↦ h_mem _),
          ← LinearMap.map_smul]⟩
    let T (u : GInf E (1 : n' → ℤˣ)) : (WeylIndex n' κ → ℂ) →L[ℂ] ℂ :=
      .mk ((α u * (β / stdLevelIndex K)) •
        gramForm (highestVector κ l') ∘ₗ conjWeylRep κ ea (s := 1) u⁻¹)
        (LinearMap.continuous_of_finiteDimensional _)
    refine ⟨(strongIntegral volume T).toLinearMap, fun o Φ φ h ↦ ?_⟩
    have h_realPart : HasRealPart (pairThetaKer (stdSpace E n) (stdSpace E n') (a o n) (a o n'))
        (realPairWeil ea eb) := pairWeil_integrated _ _ (a o n) (a o n')
    -- The lift with the real datum `P` translated by `x` is the convolution `realConv α` of the
    -- lift with the harmonic datum.
    have h_mean : lift (pairThetaKer (stdSpace E n) (stdSpace E n') (a o n) (a o n'))
          (integrated _ (realPairWeil ea eb (x, 1) (Fock.polyVector _ P)) Φ) (ofAlgForm l 1 φ) =
        realConv α (lift (pairThetaKer (stdSpace E n) (stdSpace E n') (a o n) (a o n'))
          (integrated _ (jointHarmonic ea eb l l' 1 1) Φ) (ofAlgForm l 1 φ)) :=
      hα _ h_realPart (isForm_ofAlgForm hl φ)
    -- On the left, move `x` onto the form; on the right, use `hβ`.
    rw [← h_realPart, Prod.mk_one_one, lift_omega_left _ (isAutomorphic_algFormCoeff φ),
      hβ (ha o) (hb o) K] at h_mean
    have T_int (v : WeylIndex n' κ → ℂ) : Integrable fun u : GInf E (1 : n' → ℤˣ) ↦ T u v := by
      refine DiscreteSeries.integrable_of_compactSpace (f := fun u ↦ T u v) ?_
      change Continuous fun u : GInf E (1 : n' → ℤˣ) ↦
        (α u * (β / stdLevelIndex K)) *
          gramForm (highestVector κ l') (conjWeylRep κ ea (s := 1) u⁻¹ v)
      exact (α.continuous.mul continuous_const).mul
        ((LinearMap.continuous_of_finiteDimensional (gramForm (highestVector κ l'))).comp
          ((continuous_conjWeylRep (s := 1) (κ := κ) (e := ea) v).comp continuous_inv))
    have h_fn : (fun g : G E 1 ↦ ofAlgForm l 1 φ (g * (x, 1)⁻¹)) =
        algFormCoeff 1 (gramForm (highestVector κ l) ∘ₗ conjWeylRep κ e x) φ := by
      ext g
      simp only [algFormCoeff, LinearMap.pi_apply, LinearMap.comp_apply,
        LinearMap.domRestrict_apply, LinearMap.proj_apply, Prod.fst_mul, Prod.snd_mul,
        Prod.fst_inv, Prod.snd_inv, inv_one, mul_one, mul_inv_rev, inv_inv, MonoidHom.map_mul,
        mul_apply_eq_comp]
    rw [h_fn] at h_mean
    refine (congrFun h_mean h).trans ?_
    rw [realConv, algFormCoeff, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.domRestrict_apply, LinearMap.proj_apply, ContinuousLinearMap.coe_coe,
      strongIntegral_apply volume T T_int]
    refine integral_congr_ae (.of_forall fun u ↦ ?_)
    simp only [T, algFormCoeff, ContinuousLinearMap.coe_mk', LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.domRestrict_apply, LinearMap.proj_apply,
      Pi.smul_apply, smul_eq_mul, Prod.fst_mul, Prod.snd_mul, mul_one, mul_inv_rev,
      MonoidHom.map_mul, mul_apply_eq_comp, mul_assoc]
  | zero =>
    refine ⟨0, fun o Φ φ h ↦ ?_⟩
    simp only [algFormCoeff, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      mul_zero, integral_zero]
  | add s t _ _ hs ht =>
    obtain ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ := hs, ht
    refine ⟨s' + t', fun o Φ φ h ↦ ?_⟩
    rw [integral_theta_mul_algFormCoeff_add, hs' o Φ φ h, ht' o Φ φ h]
    simp only [algFormCoeff, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.add_apply]
  | smul r t _ ht =>
    obtain ⟨t', ht'⟩ := ht
    -- The integral is linear in `t` and the coefficient of the lift is linear in `t'`.
    refine ⟨r • t', fun o Φ φ h ↦ ?_⟩
    refine (?_ : _ = r * _).trans (congrArg (r * ·) (ht' o Φ φ h))
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun g ↦ ?_)
    simp only [algFormCoeff, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      smul_eq_mul, mul_left_comm _ r]

end New
