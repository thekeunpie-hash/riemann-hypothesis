module

public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
public import Lib.General.Geometry.ProjectiveSpace
public import TauCeti.AlgebraicGeometry.RationalPoint.Image
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.RingTheory.Etale.Weakly
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
public import Lib.Cohomology.Etale.Basic
public import Lib.Shimura.AbelianScheme.Basic

section
/-!
# Dense families of complex points: reduced closures, separation of maps, and arcs

Identities between functions or morphisms on a reduced scheme can be checked on a dense family of
complex points. `New.IsDenseFamily ξ` says that the points `ξ z : Spec ℂ ⟶ X` have dense image, and
`New.IsSeparatingFamily ξ` says that moreover `X` is reduced. Every family of complex points factors
through its reduced closure, on which it is separating.

## Main definitions and results

* `New.exists_reduced_closure`: any family of complex points of `X` factors through a closed
  subscheme in which it is `New.IsSeparatingFamily`, namely the reduced closure.
* `New.IsSeparatingFamily.pointFn_ext`, `New.IsSeparatingFamily.hom_ext`: regular functions, and
  morphisms over `S` to a scheme separated over `S`, that agree at the points are equal.
* `New.IsSeparatingFamily.exists_map_of_coords`: if a linear system on `X` gives the points `e z`
  the same coordinates as a projective embedding of `G` gives points `p z`, then it comes from a
  morphism `X ⟶ G` that sends `e z` to `p z`.
* `New.exists_valuative_arc_of_isDenseFamily` joins any point of a locally noetherian scheme with
  finitely many dense complex points to one of them by an arc `Spec V → S`, with `V` the ring of a
  valuation of `ℂ` in `ℝ≥0`.

Notions from other files:
* `New.PointFn X`: rules that attach an element of `A` to every ring-valued point `Spec A ⟶ X`.
  It is regular on `U` (`IsRegularOn`) if, at points landing in `U`, it commutes with ring maps.
* `New.LineBundle X ι`: an open cover `U_i` of `X` with transition functions `g_ij`.
* `New.LineBundle.IsHomogeneousCoords`: `v` is a vector of homogeneous coordinates of the point `t`,
  that is, `t` lands in `U_j` exactly when `v_j` is a unit, and then `g_jk(t) = v_k / v_j`.
* `New.LineBundle.IsLinearSystem`: the data of a map to projective space, the model being
  `g_ij = s_j / s_i` on `U_i = {s_i ≠ 0}` for sections `s_i` without common zero.
* `New.LineBundle.IsProjEmbedding`: a linear system on a proper `X ⟶ S` for which points in one
  chart with the same affine coordinates and the same image in `S` are equal.
-/

@[expose] public section

/-! ## Reduced closures of families of complex points -/

section ReducedClosure

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData IsLocalRing

/-- Let `i : Y ⟶ Z` be a closed immersion and `f : X ⟶ Z` with `X` reduced. If the preimage under
`f` of the image of `i` is dense in `X`, then `f` factors through `i`. -/
@[stacks 0356 "'if' direction, with the preimage of the closed subscheme only assumed dense"]
lemma New.exists_lift_of_dense_preimage {X Y Z : Scheme} [IsReduced X] (i : Y ⟶ Z)
    [IsClosedImmersion i] (f : X ⟶ Z) (h_dense : Dense (f ⁻¹' Set.range i)) :
    ∃ g : X ⟶ Y, g ≫ i = f := by
  -- The pull-back of the ideal of `i` has closed support containing a dense set, hence full
  -- support, so it is zero as `X` is reduced. Thus `f` kills the ideal of `i`.
  have h_supp : (i.ker.comap f).support = ⊤ := by
    ext x
    simp [i.support_ker, f.continuous.closure_preimage_subset _ (h_dense x)]
  have h_ker : i.ker ≤ f.ker := by simpa using (map_gc f).le_u (support_eq_top_iff.1 h_supp).le
  exact ⟨_, IsClosedImmersion.lift_fac i f h_ker⟩

/-- The images of the complex points `ξ z : Spec ℂ ⟶ X` form a dense subset of `X`. -/
abbrev New.IsDenseFamily {Z : Type} {X : Scheme} (ξ : Z → (Spec (CommRingCat.of ℂ) ⟶ X)) : Prop :=
  DenseRange fun z : Z ↦ ξ z (closedPoint ℂ)

/-- `X` is reduced and the complex points `ξ z` are dense in it, so that regular functions are
determined by their values at these points. -/
def New.IsSeparatingFamily {Z : Type} {X : Scheme} (ξ : Z → (Spec (CommRingCat.of ℂ) ⟶ X)) :
    Prop := AlgebraicGeometry.IsReduced X ∧ IsDenseFamily ξ

/-- Reduced closure: complex points `ξ z : Spec ℂ ⟶ X` factor as `ξ z = i ∘ e z` through a closed
immersion `i : Y ⟶ X`, with `Y` reduced and the points `e z` dense in `Y`
(`IsSeparatingFamily e`). -/
lemma New.exists_reduced_closure {Z : Type} {X : Scheme}
    (ξ : Z → (Spec (CommRingCat.of ℂ) ⟶ X)) :
    ∃ (Y : Scheme) (i : Y ⟶ X) (e : Z → (Spec (CommRingCat.of ℂ) ⟶ Y)),
      IsClosedImmersion i ∧ (∀ z : Z, e z ≫ i = ξ z) ∧ IsSeparatingFamily e := by
  -- Take the reduced closed subscheme on the closure of the points.
  let I : IdealSheafData X := vanishingIdeal (.closure (.range fun z ↦ ξ z (closedPoint ℂ)))
  -- Each point `ξ z` lands in the support, so it factors through the subscheme.
  have h_lift (z : Z) : ∃ g : Spec (CommRingCat.of ℂ) ⟶ I.subscheme, g ≫ I.subschemeι = ξ z :=
    exists_lift_of_dense_preimage I.subschemeι (ξ z)
      (dense_indiscrete ⟨_, ⟨ξ z (closedPoint ℂ), subset_closure ⟨z, rfl⟩⟩, rfl⟩)
  choose e he using h_lift
  -- On each affine chart the ideal is a vanishing ideal, hence radical.
  have (U : I.subschemeCover.cover.I₀) : IsReduced (I.subschemeCover.cover.X U) :=
    (affine_isReduced_iff _).2
      ((Ideal.isRadical_iff_quotient_reduced _).1 (PrimeSpectrum.isRadical_vanishingIdeal _))
  have h_red : IsReduced I.subscheme := IsReduced.of_openCover _ I.subschemeCover.cover
  -- The image of a point of the subscheme lies in the closure of the images of the `e z`.
  have h_dense : IsDenseFamily e := by
    have h_pt (z : Z) (x : Spec (CommRingCat.of ℂ)) : I.subschemeι (e z x) = ξ z x := by
      rw [← he z, Scheme.Hom.comp_apply]
    refine I.subschemeι.isEmbedding.dense_iff.2 fun y ↦ closure_mono ?_ y.property
    exact Set.range_subset_iff.2 fun z ↦ ⟨e z (closedPoint ℂ), ⟨z, rfl⟩, h_pt z _⟩
  exact ⟨I.subscheme, I.subschemeι, e, inferInstance, he, h_red, h_dense⟩

end ReducedClosure

/-! ## Functions and morphisms on reduced schemes determined by dense points -/

namespace New

open CategoryTheory AlgebraicGeometry Limits Set Over LineBundle PointFn

/-- A universally closed morphism `f : Y ⟶ X` is surjective if every point `ξ z` of a dense family
of complex points of `X` lifts to a complex point `y z` of `Y`. -/
lemma IsDenseFamily.surjective {Z : Type} {X Y : Scheme}
    {ξ : Z → (Spec (CommRingCat.of ℂ) ⟶ X)} (hξ : IsDenseFamily ξ) (f : Y ⟶ X) [UniversallyClosed f]
    (y : Z → (Spec (CommRingCat.of ℂ) ⟶ Y)) (h_lift : ∀ z : Z, y z ≫ f = ξ z) :
    Surjective f := by
  -- The range of `f` is closed and contains the dense set of the points `ξ z`.
  have h_mem (z : Z) (x : Spec (CommRingCat.of ℂ)) : ξ z x ∈ range f :=
    ⟨y z x, by rw [← h_lift z, Scheme.Hom.comp_apply]⟩
  exact ⟨fun x ↦ hξ.induction_on x f.isClosedMap.isClosed_range fun z ↦ h_mem z _⟩

namespace IsSeparatingFamily

/-- Let `X` be reduced and the complex points `ξ z` dense. Two functions on ring-valued points that
are regular on an open `U` (compatible with ring maps at points of `U`) and agree at all `ξ z`
landing in `U` agree at every ring-valued point `t` landing in `U`. -/
lemma pointFn_ext {Z : Type} {X : Scheme} {ξ : Z → (Spec (CommRingCat.of ℂ) ⟶ X)}
    (hξ : IsSeparatingFamily ξ) {U : X.Opens} {f g : PointFn X} (hf : IsRegularOn f U)
    (hg : IsRegularOn g U)
    (h_agree : ∀ z : Z, LandsIn (ξ z) U → f (CommRingCat.of ℂ) (ξ z) = g (CommRingCat.of ℂ) (ξ z))
    (A : CommRingCat) (t : Spec A ⟶ X) (ht : LandsIn t U) :
    f A t = g A t := by
  obtain ⟨h_red, h_dense⟩ := hξ
  -- On `U` both `f` and `g` are given by sections of the structure sheaf.
  obtain ⟨s, hs⟩ := hf.exists_ofSection
  obtain ⟨s', hs'⟩ := hg.exists_ofSection
  suffices h_eq : s - s' = 0 by rw [← hs A t ht, ← hs' A t ht, sub_eq_zero.1 h_eq]
  by_contra hs_ne
  -- On a reduced scheme a nonzero section is invertible on a nonempty open set.
  have h_nonempty : (X.basicOpen (s - s') : Set X).Nonempty := by
    simpa [← ne_empty_iff_nonempty] using hs_ne
  -- By density some `ξ z` lies in it: there `s - s'` is a unit, but `f` and `g` agree.
  obtain ⟨z, hz⟩ := h_dense.exists_mem_open (X.basicOpen (s - s')).isOpen h_nonempty
  have hz_U : LandsIn (ξ z) U := (landsIn_iff_mem.2 hz).mono (X.basicOpen_le _)
  exact ((landsIn_basicOpen hz_U _).1 (landsIn_iff_mem.2 hz)).ne_zero
    (by simp [hs _ _ hz_U, hs' _ _ hz_U, h_agree z hz_U])

/-- Let `e z` be complex points of the `S`-scheme `X` over the points `η z` of `S`, with `X` reduced
and the `e z` dense. Two morphisms over `S` from `X` to a separated `G` that agree at every `e z`
are equal. -/
lemma hom_ext {Z : Type} {S : Scheme} {η : Z → (Spec (CommRingCat.of ℂ) ⟶ S)} {X G : Over S}
    {e : ∀ z : Z, Over.mk (η z) ⟶ X} (he : IsSeparatingFamily fun z : Z ↦ (e z).left)
    [IsSeparated G.hom] {f g : X ⟶ G} (h_agree : ∀ z : Z, e z ≫ f = e z ≫ g) :
    f = g := by
  obtain ⟨h_red, h_dense⟩ := he
  -- The equalizer `i` of `f` and `g` is a closed subscheme through which every `e z` factors, so it
  -- is surjective onto `X`; a reduced source and a separated target then give `f = g`.
  let i : (equalizer f g).left ⟶ X.left := (equalizer.ι f g).left
  have : Surjective i := h_dense.surjective i (fun z ↦ (equalizer.lift (e z) (h_agree z)).left)
    fun z ↦ by rw [← Over.comp_left, equalizer.lift_ι]
  exact OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom (by simp) i
    (by rw [← Over.comp_left, ← Over.comp_left, equalizer.condition]))

/-- Let `e z`, `p z` be complex points of the `S`-schemes `X`, `G` over the same point `η z`, with
`X` reduced and the `e z` dense. If a linear system `W` on `X` and a projective embedding `M` of
`G`, both with the finite index set `ι`, give `e z` and `p z` the same homogeneous coordinates
`v z`, then some morphism `d : X ⟶ G` over `S` sends each `e z` to `p z` and pulls the charts and
transition functions of `M` back to those of `W`. -/
lemma exists_map_of_coords {Z ι : Type} {S : Scheme} {η : Z → (Spec (CommRingCat.of ℂ) ⟶ S)}
    [Finite ι] {v : Z → ι → ℂ} {X G : Over S} {e : ∀ z : Z, Over.mk (η z) ⟶ X}
    (he : IsSeparatingFamily fun z : Z ↦ (e z).left) {p : ∀ z : Z, Over.mk (η z) ⟶ G}
    {W : LineBundle X.left ι} {M : LineBundle G.left ι}
    (hW : IsLinearSystem W) (hM : IsProjEmbedding M G.hom)
    (he_coords : ∀ z : Z, W.IsHomogeneousCoords (e z).left (v z))
    (hp_coords : ∀ z : Z, M.IsHomogeneousCoords (p z).left (v z)) :
    ∃ d : X ⟶ G, (∀ z : Z, e z ≫ d = p z) ∧ M.pull d.left = W := by
  -- `W` is the pull-back of the hyperplane bundle `H` along a map `f : X ⟶ ℙ × S` over `S`, and
  -- `M` along a closed immersion `j : G ⟶ ℙ × S` over `S`.
  let H : LineBundle (ProjSpace ι ⨯ S) ι := (ProjSpace.hyperplaneBundle ι).pull prod.fst
  obtain ⟨f, hf_over, rfl⟩ : ∃ f : X.left ⟶ ProjSpace ι ⨯ S,
      f ≫ prod.snd = X.hom ∧ H.pull f = W := hW.exists_hom_projSpace X.hom
  obtain ⟨j, hj_closed, hj_over, rfl⟩ : ∃ j : G.left ⟶ ProjSpace ι ⨯ S,
      IsClosedImmersion j ∧ j ≫ prod.snd = G.hom ∧ H.pull j = M := hM.exists_isClosedImmersion
  obtain ⟨h_red, h_dense⟩ := he
  -- Equal homogeneous coordinates give equal points of projective space.
  have h_pt (z : Z) : (p z).left ≫ j = (e z).left ≫ f :=
    isProjEmbedding_projSpace.eq_of_isHomogeneousCoords (by simp [hf_over, hj_over]) (hp_coords z)
      (he_coords z) (LineBundle.exists_landsIn _ _)
  -- So `f` sends a dense set into the image of `j`, and factors through `j`.
  have h_mem (z : Z) (x : (Over.mk (η z)).left) : f ((e z).left x) ∈ range j :=
    ⟨(p z).left x, by rw [← Scheme.Hom.comp_apply, h_pt z, Scheme.Hom.comp_apply]⟩
  have h_dense_pre : Dense (f ⁻¹' range j) :=
    h_dense.mono (range_subset_iff.2 fun z ↦ h_mem z _)
  obtain ⟨d, rfl⟩ := exists_lift_of_dense_preimage j f h_dense_pre
  exact ⟨homMk d (by rw [← hf_over, ← hj_over, Category.assoc]),
    fun z ↦ OverMorphism.ext (by simp [← cancel_mono j, h_pt z]), by simp [pull_comp]⟩

end IsSeparatingFamily

end New

/-! ## Arcs from dense complex points to arbitrary points -/

section ArcExistence

open CategoryTheory AlgebraicGeometry Spec Scheme Set Ideal IsLocalRing MvPolynomial
  IsLocalization.AtPrime CommRingCat ValuativeRel Valuation IsIntegrallyClosed LocalSubring

/-- The extension of a prime ideal of `A` to a polynomial ring over `A` is prime. -/
lemma New.isPrime_map_C_mvPolynomial {A σ : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    (p.map (C : A →+* MvPolynomial σ A)).IsPrime := by
  -- It is the kernel of the map to the polynomial ring over the domain `A ⧸ p`.
  rw [← p.mk_ker, ← ker_map]
  exact RingHom.ker_isPrime _

/-- A prime of a noetherian ring that is minimal over one element extends to a prime of height at
most one in a polynomial ring in finitely many variables. -/
lemma New.height_map_C_le_one {A σ : Type*} [CommRing A] [IsNoetherianRing A] [Finite σ] {x : A}
    {p : Ideal A} (hp : p ∈ (span {x} : Ideal A).minimalPrimes) :
    (p.map (C : A →+* MvPolynomial σ A)).height ≤ 1 := by
  obtain ⟨⟨hp_prime, hxp⟩, hp_min⟩ := hp
  have : Nontrivial A := (Ideal.Quotient.mk p).domain_nontrivial
  -- The extension is minimal over `x`, so Krull's principal ideal theorem applies.
  have h_min : p.map (C : A →+* MvPolynomial σ A) ∈ ((span {x}).map C).minimalPrimes :=
    ⟨⟨isPrime_map_C_mvPolynomial p, map_mono hxp⟩, fun J ⟨hJ_prime, hxJ⟩ hJp ↦
      map_le_of_le_comap (hp_min ⟨hJ_prime.comap C, le_comap_of_map_le hxJ⟩
        ((comap_mono hJp).trans_eq p.comap_map_eq_self_of_faithfullyFlat))⟩
  exact height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ h_min

/-- Let `p` be a prime of a noetherian domain `A` that is minimal over one element. A nonzero prime
`J` of a polynomial ring over `A` that lies in the extension of `p` equals that extension. -/
lemma New.eq_map_C_of_ne_bot_of_le_map_C {A σ : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {x : A} {p : Ideal A} (hp : p ∈ (span {x} : Ideal A).minimalPrimes)
    {J : Ideal (MvPolynomial σ A)} [J.IsPrime] (hJ_ne : J ≠ ⊥) (hJ_le : J ≤ p.map C) :
    J = p.map C := by
  -- In the finitely many variables of a nonzero `w ∈ J`, the prime `J` cuts out a nonzero prime
  -- `J'` inside the extension of `p`, which has height at most one; so the two are equal.
  obtain ⟨w, hw_mem, hw_ne⟩ := J.ne_bot_iff.1 hJ_ne
  obtain ⟨n, u, hu, w, rfl⟩ := w.exists_fin_rename
  let J' : Ideal (MvPolynomial (Fin n) A) := J.comap (rename u)
  have h_le : J' ≤ p.map C := by
    refine fun a ha ↦ mem_map_C_iff.2 fun m ↦ ?_
    rw [← coeff_rename_mapDomain u hu]
    exact mem_map_C_iff.1 (hJ_le (mem_comap.1 ha)) _
  have h_ne_bot : J' ≠ ⊥ := J'.ne_bot_iff.2 ⟨w, mem_comap.2 hw_mem, ne_zero_of_map hw_ne⟩
  have h_eq : J' = p.map C := J'.eq_of_le_of_height_le h_le
    ((height_map_C_le_one hp).trans (by simpa [Order.one_le_iff_ne_zero] using h_ne_bot))
  refine hJ_le.antisymm (map_le_of_le_comap fun a ha ↦ ?_)
  simpa [J'] using h_eq.ge (mem_map_of_mem C ha)

/-- Let `V` be a valuation subring of a field in which every nonzero prime ideal contains the
maximal ideal. Then the valuation of `V` is archimedean: every value is bounded by a
power of any value above one. -/
lemma New.exists_valuation_le_pow_of_maximalIdeal_le {K : Type*} [Field K] (V : ValuationSubring K)
    (hV : ∀ J : Ideal V, J.IsPrime → J ≠ ⊥ → maximalIdeal V ≤ J) (z : K)
    {y : K} (hy : 1 < V.valuation y) :
    ∃ n : ℕ, V.valuation z ≤ V.valuation y ^ n := by
  -- The element `y⁻¹` lies in the maximal ideal, so a power of it lies in the nonzero ideal `I` of
  -- denominators of `z`.
  let I : Ideal V := (1 : Submodule V K).comap (LinearMap.toSpanSingleton V K z)
  have h_mem_iff (a : V) : a ∈ I ↔ ∃ w : V, (w : K) = a * z := by simp [I, Algebra.smul_def]
  obtain ⟨⟨c, hc⟩, w₀, hw₀⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors V) z
  have hI_ne : I ≠ ⊥ := I.ne_bot_iff.2
    ⟨c, (h_mem_iff c).2 ⟨w₀, by simpa [Algebra.smul_def] using hw₀⟩, nonZeroDivisors.ne_zero hc⟩
  have h_rad : maximalIdeal V ≤ I.radical := by
    rw [radical_eq_sInf]
    exact le_sInf fun J ⟨hIJ, hJ⟩ ↦ hV J hJ (ne_bot_of_le_ne_bot hI_ne hIJ)
  obtain ⟨hy_mem, hy_max⟩ := V.mem_nonunits_iff_exists_mem_maximalIdeal.1
    (show y⁻¹ ∈ V.nonunits by simpa [V.mem_nonunits_iff] using inv_lt_one_of_one_lt₀ hy)
  obtain ⟨n, hn⟩ := mem_radical_iff.1 (h_rad hy_max)
  -- So `w = y⁻¹ ^ n * z` lies in `V`, that is, `y ^ n` divides `z` over `V`.
  obtain ⟨w, hw⟩ : ∃ w : V, (w : K) = y⁻¹ ^ n * z := by simpa using (h_mem_iff _).1 hn
  have hy_ne : y ≠ 0 := V.valuation.pos_iff.1 (zero_lt_one.trans hy)
  have h_dvd : (w : K) * y ^ n = z := by simp [hw, field]
  exact ⟨n, ((V.valuation_le_iff z (y ^ n)).2 ⟨w, h_dvd⟩).trans_eq (map_pow _ y n)⟩

/-- A valuation subring `V` of a field, in which every prime ideal with a nonzero element `c`
contains the maximal ideal, is the ring of a valuation with values in `ℝ≥0`. -/
lemma New.exists_nnreal_valuation {K : Type*} [Field K] (V : ValuationSubring K)
    (hV : ∀ J : Ideal V, J.IsPrime → ∀ c ∈ nonZeroDivisors V, c ∈ J → maximalIdeal V ≤ J) :
    ∃ v : Valuation K NNReal, v.valuationSubring = V := by
  -- The canonical valuation of the valuative relation of `V` is equivalent to that of `V`.
  let : ValuativeRel K := ofValuation V.valuation
  have : V.valuation.Compatible := .ofValuation V.valuation
  have h : (valuation K).IsEquiv V.valuation := isEquiv _ _
  -- The value group is archimedean, hence has rank at most one and embeds into `ℝ≥0` by some `g`.
  obtain ⟨g, hg⟩ : IsRankLeOne K := isRankLeOne_iff_mulArchimedean.2
    ⟨valuation_surjective.forall₂.2 fun z y hy ↦
      (exists_valuation_le_pow_of_maximalIdeal_le V (fun J hJ hne ↦ (J.ne_bot_iff.1 hne).elim
        fun c ⟨hc, hc0⟩ ↦ hV J hJ c (mem_nonZeroDivisors_of_ne_zero hc0) hc) z
        (h.one_lt_iff_one_lt.1 hy)).imp fun n hn ↦ by rwa [← map_pow, h.le_iff_le, map_pow]⟩
  exact ⟨(valuation K).map ⟨g, hg.monotone⟩, V.valuationSubring_valuation ▸
    (isEquiv_iff_valuationSubring _ _).1 ((isEquiv_map_self_of_strictMono _ hg.injective).trans h)⟩

/-- Blowing up inside a valuation ring. Let `O ⟶ W` be a local map from a noetherian local ring to
a valuation ring. Then `W` has a noetherian `O`-subalgebra `A` with a prime `p` that is minimal
over one element and lies over the maximal ideal of `O`. -/
lemma New.exists_subalgebra_minimalPrimes_span_singleton (O W : Type*) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] [CommRing W] [IsDomain W] [ValuationRing W] [Algebra O W]
    [IsLocalHom (algebraMap O W)] :
    ∃ (A : Subalgebra O W) (x : A) (p : Ideal A), IsNoetherianRing A ∧
      p ∈ (span {x} : Ideal A).minimalPrimes ∧ maximalIdeal O ≤ p.comap (algebraMap O A) := by
  obtain ⟨r, hr⟩ := (maximalIdeal O).fg_of_isNoetherianRing
  -- Divisibility in `W` is total, so one element `x` of the maximal ideal divides all its
  -- generators; `A` is generated by the quotients `k y = y / x`, so the maximal ideal becomes
  -- principal in `A`.
  have h_total : Std.Total fun a b : W ↦ b ∣ a := ⟨fun a b ↦ ValuationRing.dvd_total b a⟩
  obtain ⟨⟨x, hx_mem⟩, hx⟩ : ∃ x : (maximalIdeal O : Set O),
      ∀ y : r, ∃ c : W, algebraMap O W y = algebraMap O W x * c :=
    (h_total.directed fun y : (maximalIdeal O : Set O) ↦ algebraMap O W y).finite_le
      (inclusion (subset_span.trans hr.le))
  choose k hk using hx
  let A : Subalgebra O W := (aeval (R := O) k).range
  have hx_nonunit : ¬IsUnit (algebraMap O A x) := fun h_unit ↦
    notMem_maximalIdeal.2 (isUnit_of_map_unit (algebraMap O W) x (h_unit.map A.val)) hx_mem
  obtain ⟨p, hp⟩ := nonempty_minimalPrimes (span_singleton_ne_top hx_nonunit)
  have h_dvd (y : r) : algebraMap O A x ∣ algebraMap O A y :=
    ⟨⟨k y, X y, aeval_X k y⟩, Subtype.ext (hk y)⟩
  -- `A` is noetherian as the image of a polynomial ring in finitely many variables over `O`.
  refine ⟨A, algebraMap O A x, p, inferInstance, hp, ?_⟩
  exact hr.ge.trans <| span_le.2 fun y hy ↦
    Ideal.IsMinimalPrime.le hp (mem_span_singleton.2 (h_dvd ⟨y, hy⟩))

/-- Let `e` identify a ring `R` with a subring of a field `K`. Every prime `P` of `R` is the centre
of a valuation subring `U` of `K` that contains `R`. -/
@[stacks 00IA "for a prime of a subring"]
lemma New.exists_valuationSubring_comap_maximalIdeal_eq {R K : Type*} [CommRing R] [Field K]
    {B : Subring K} (e : R ≃+* B) (P : Ideal R) [P.IsPrime] :
    ∃ (U : ValuationSubring K) (f : R →+* U),
      (∀ a : R, (f a : K) = e a) ∧ (maximalIdeal U).comap f = P := by
  -- `U` dominates the localisation `L` of `B` at the image of `P`.
  let L : LocalSubring K := LocalSubring.ofPrime B (P.map e)
  obtain ⟨U, hU, hU_local⟩ := L.exists_le_valuationSubring
  let f : R →+* U := (Subring.inclusion hU).comp ((algebraMap B L.toSubring).comp e.toRingHom)
  -- The maximal ideal of `U` meets `B` in the image of `P`, as `U` dominates `L`.
  refine ⟨U, f, fun _ ↦ rfl, ext fun a ↦ ?_⟩
  calc f a ∈ maximalIdeal U
      ↔ algebraMap B L.toSubring (e a) ∈ maximalIdeal L.toSubring :=
        map_mem_nonunits_iff (Subring.inclusion hU) _
    _ ↔ e a ∈ P.map e := to_map_mem_maximal_iff _ _ (e a)
    _ ↔ a ∈ P := apply_mem_of_equiv_iff

/-- Let `A` be a noetherian subring of a field `K` and `p` a prime of `A` that is minimal over one
element. Then `A` lies in the ring of a valuation `v` of `K` with values in `ℝ≥0`, in such a way
that `p` lies in the maximal ideal. -/
lemma New.exists_nnreal_valuation_le_comap_maximalIdeal {A : Type*} (K : Type*) [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [FaithfulSMul A K] {x : A}
    {p : Ideal A} (hp : p ∈ (span {x} : Ideal A).minimalPrimes) :
    ∃ (v : Valuation K NNReal) (ψ : A →+* v.valuationSubring),
      (∀ a : A, (ψ a : K) = algebraMap A K a) ∧ p ≤ (maximalIdeal v.valuationSubring).comap ψ := by
  -- Adjoin a transcendence basis `t`, take a valuation ring `U` with centre the extension of `p`,
  -- and localise at a prime `q` minimal over `p`. The result `V` has rank at most one.
  have hp_prime : p.IsPrime := Ideal.IsMinimalPrime.isPrime hp
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis A K
  let P : Ideal (MvPolynomial t A) := p.map C
  have hP_prime : P.IsPrime := isPrime_map_C_mvPolynomial p
  let e : MvPolynomial t A ≃+* (Algebra.adjoin A (range (Subtype.val : t → K))).toSubring :=
    ht.1.aevalEquiv.toRingEquiv
  obtain ⟨U, f, hf, h_centre⟩ := exists_valuationSubring_comap_maximalIdeal_eq e P
  obtain ⟨q, ⟨⟨hq_prime, hPq⟩, hq_min⟩, hq_le⟩ :
      ∃ q ∈ (P.map f).minimalPrimes, q ≤ maximalIdeal U :=
    exists_minimalPrimes_le (map_le_of_le_comap h_centre.ge)
  let V : ValuationSubring K := U.ofPrime q
  let g : MvPolynomial t A →+* V := (algebraMap U V).comp f
  have hg (a : MvPolynomial t A) : (g a : K) = e a := hf a
  let : Algebra (MvPolynomial t A) V := g.toAlgebra
  -- Every prime of `V` with a nonzero element contains the maximal ideal `q V`.
  have h_rank (J : Ideal V) (hJ : J.IsPrime) (c : V) (hc : c ∈ nonZeroDivisors V)
      (hcJ : c ∈ J) : maximalIdeal V ≤ J := by
    rw [← map_eq_maximalIdeal q V, map_le_iff_le_comap]
    -- The ideals of the valuation ring `U` are totally ordered, so we may assume `J ∩ U ≤ q`.
    obtain hqJ | hJq : q ≤ J.comap (algebraMap U V) ∨ J.comap (algebraMap U V) ≤ q :=
      (ValuationRing.le_total_ideal U).total _ _
    · exact hqJ
    -- As `K` is algebraic over the polynomial ring, `c` divides a polynomial `w ≠ 0`.
    have hc_alg : IsAlgebraic (MvPolynomial t A) c :=
      (ht.isAlgebraic.isAlgebraic (c : K)).of_ringHom_of_comp_eq _ _ e.surjective
        V.subtype_injective (RingHom.ext fun a ↦ (hg a).symm)
    obtain ⟨w, hw_ne, hcw⟩ : ∃ w : MvPolynomial t A, w ≠ 0 ∧ c ∣ g w :=
      hc_alg.exists_ne_zero_dvd hc
    have h_comap : J.comap g = (J.comap (algebraMap U V)).comap f := (comap_comap _ _).symm
    have hJP : J.comap g ≤ P :=
      h_comap.trans_le ((comap_mono (hJq.trans hq_le)).trans_eq h_centre)
    have hJ_eq : J.comap g = P := eq_map_C_of_ne_bot_of_le_map_C hp
      ((J.comap g).ne_bot_iff.2 ⟨w, mem_of_dvd J hcw hcJ, hw_ne⟩) hJP
    -- So `J ∩ U` contains the extension of `p`, and `q` is minimal among such primes.
    have hPJ : P.map f ≤ J.comap (algebraMap U V) :=
      map_le_iff_le_comap.2 (hJ_eq.ge.trans_eq h_comap)
    exact hq_min ⟨hJ.comap _, hPJ⟩ hJq
  obtain ⟨v, hv⟩ := exists_nnreal_valuation V h_rank
  refine ⟨v, ?_⟩
  rw [hv]
  refine ⟨g.comp C, fun a ↦ (hg (C a)).trans (aeval_C _ a), fun a ha ↦ ?_⟩
  exact (under_maximalIdeal V q).ge (hPq (mem_map_of_mem f (mem_map_of_mem C ha)))

/-- Let `S` be a locally noetherian scheme with finitely many complex points `η i` whose images are
dense. For every point `s` of `S` there are an index `i`, a valuation `v` of `ℂ` with values in
`ℝ≥0` and a morphism `a` from the spectrum of its valuation ring `V` to `S` that restricts to `η i`
along `Spec ℂ ⟶ Spec V` (the map `specMap` of the inclusion) and sends the closed point to `s`. -/
lemma New.exists_valuative_arc_of_isDenseFamily {S : Scheme} {ι : Type} [IsLocallyNoetherian S]
    [Finite ι] (η : ι → (Spec (of ℂ) ⟶ S)) (hη : IsDenseFamily η) (s : S) :
    ∃ (i : ι) (v : Valuation ℂ NNReal) (a : Spec (of v.valuationSubring) ⟶ S),
      specMap v.valuationSubring.subtype ≫ a = η i ∧
      a (closedPoint (of v.valuationSubring)) = s := by
  -- Some `η i` specialises to `s`, which gives a map `θ` from the local ring `O` at `s` to `ℂ`.
  -- By blowing up at `s`, find a noetherian subring `A` of `ℂ` containing the image of `O`, with a
  -- prime `p` over `s` minimal over one element; take a real valuation `v` centred above `p`.
  obtain ⟨i, h_spec⟩ : ∃ i : ι, η i (closedPoint ℂ) ⤳ s := by
    simpa [← iUnion_singleton_eq_range, ← specializes_iff_mem_closure] using hη s
  let O : CommRingCat := S.presheaf.stalk s
  let θ : O ⟶ of ℂ := S.presheaf.stalkSpecializes h_spec ≫ stalkClosedPointTo (η i)
  obtain ⟨W, hW, hW_local⟩ : ∃ (W : ValuationSubring ℂ) (hW : ∀ a : O, θ.hom a ∈ W.toSubring),
      IsLocalHom (θ.hom.codRestrict W.toSubring hW) := exists_factor_valuationRing θ.hom
  let : Algebra O W := (θ.hom.codRestrict W hW).toAlgebra
  have : IsLocalHom (algebraMap O W) := hW_local
  obtain ⟨A, x, p, hA, hp, h_max_le⟩ : ∃ (A : Subalgebra O W) (x : A) (p : Ideal A),
      IsNoetherianRing A ∧ p ∈ (span {x} : Ideal A).minimalPrimes ∧
        maximalIdeal O ≤ p.comap (algebraMap O A) :=
    exists_subalgebra_minimalPrimes_span_singleton O W
  obtain ⟨v, ψ, hψ, hp_le⟩ : ∃ (v : Valuation ℂ NNReal) (ψ : A →+* v.valuationSubring),
      (∀ a : A, (ψ a : ℂ) = algebraMap A ℂ a) ∧ p ≤ (maximalIdeal v.valuationSubring).comap ψ :=
    exists_nnreal_valuation_le_comap_maximalIdeal ℂ hp
  -- The arc is `Spec V → Spec O → S`, with `V` the ring of `v`.
  let φ : O →+* v.valuationSubring := ψ.comp (algebraMap O A)
  have hφ : ofHom φ ≫ ofHom v.valuationSubring.subtype = θ :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ hψ (algebraMap O A a))
  refine ⟨i, v, Spec.map (ofHom φ) ≫ S.fromSpecStalk s, ?_, ?_⟩
  · simp [← map_comp_assoc, hφ, θ, Spec_stalkClosedPointTo_fromSpecStalk _]
  · -- `φ` is local, so the closed point goes to the closed point.
    have h_local : maximalIdeal O ≤ (maximalIdeal v.valuationSubring).comap φ :=
      fun y hy ↦ hp_le (h_max_le hy)
    have h_closed : Spec.map (ofHom φ) (closedPoint (of v.valuationSubring)) = closedPoint O :=
      PrimeSpectrum.ext ((maximalIdeal.isMaximal O).eq_of_le (IsPrime.ne_top') h_local).symm
    exact (congrArg (S.fromSpecStalk s) h_closed).trans fromSpecStalk_closedPoint

end ArcExistence
end
end

/-!
# Geometric points, specialisation, separating products and integral abelian varieties

Let `k` be an algebraically closed field. For schemes and morphisms locally of finite type, points
with values in `k` detect nonempty locally closed sets and images of morphisms, and this is used to
spread properties over commutative group schemes.
Abelian schemes over `k` are shown to be integral, using that smooth morphisms are geometrically
reduced (`TauCeti.AlgebraicGeometry.Smooth.geometricallyReduced`). The file also records that flat
morphisms are injective on stalks. Finally it gives criteria for families of complex points to be
separating over a stalk of the base and on a product of flat schemes.

## Main definitions and results

* `New.exists_section_mem`, `New.exists_point_mem`: a nonempty locally closed set in a scheme
  locally of finite type over `k` contains a `k`-point.
* `New.IsDenseFamily.of_fibres`: if the complex points `η i` are dense in `S` and `A` is smooth over
  `S`, a family containing every complex point of `A` over the `η i` is dense in `A`.
* `New.AddObj.property_of_isOpenImmersion`: take a commutative group scheme (`New.AddObj`) locally
  of finite type over `k`. A property induced by a property of ring maps spreads from a nonempty
  open part to the whole scheme, by translation.
* `New.AddObj.smoothOfRelativeDimension_of_fibres`: the relative dimension of an abelian scheme can
  be read off the fibres through a dense family of points.
* `New.isSeparatingFamily_stalk`: for `A` and `S` reduced and dense points of `A` with finitely many
  images in `S`, the lifts of those that factor through a stalk of `S` separate the base change of
  `A` to that stalk.
* `New.IsSeparatingFamily.prod`: separating points of `B`, paired with dense points of the fibres of
  `A` over their images in `S`, separate `A ×_S B`, for `A`, `B` flat and locally of finite type,
  `A` reduced, and `S` reduced, locally noetherian, with finitely many dense complex points.

Notions from other files:
* `New.IsDenseFamily`: the images of a family of complex points are dense.
* `New.IsSeparatingFamily`: the family is dense and the scheme is reduced.
* `New.IsAbelianScheme`: a smooth proper commutative group scheme on which multiplication by every
  `m ≠ 0` is surjective.
* `New.translation`: translation x ↦ x + z by a section z of a commutative group scheme.

## Relation to the literature

Known; see `Lib.Shimura.AbelianScheme.IsogenyFlatness` for sources.
-/

@[expose] public section

/-! ## Points over algebraically closed fields -/

section GeometricPoints

open CategoryTheory AlgebraicGeometry MonoidalCategory Scheme Over Limits.pullback Pullback Set

namespace New

/-- A nonempty locally closed subset of a scheme `X` locally of finite type over an algebraically
closed field `k` contains the image of a `k`-point, that is, of a section `x : Spec k ⟶ X` of the
structure morphism `s`. -/
lemma exists_section_mem {k : Type*} {X : Scheme} [Field k] [IsAlgClosed k]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] {S : Set X} (hS : IsLocallyClosed S)
    (hS_ne : S.Nonempty) :
    ∃ x : Spec (.of k) ⟶ X, x ≫ s = 𝟙 (Spec (.of k)) ∧ x (default : Spec (.of k)) ∈ S := by
  -- `X` is a Jacobson space, so `S` contains a closed point; over `k` a closed point is a
  -- `k`-point.
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace s
  obtain ⟨x, hxS, hx : IsClosed {x}⟩ := nonempty_inter_closedPoints hS_ne hS
  exact ⟨pointOfClosedPoint s x hx, pointOfClosedPoint_comp s x hx,
    by simpa [pointOfClosedPoint] using hxS⟩

/-- Let `X` be a scheme over `Spec k`, locally of finite type, with `k` an algebraically closed
field. A nonempty locally closed subset `S` of `X` contains the image of a `k`-point, that is, of a
morphism over `Spec k` from the unit object `𝟙_` (`Spec k` over itself) to `X`. This is
`New.exists_section_mem` in the category of schemes over `Spec k`. -/
lemma exists_point_mem {k : Type*} [Field k] [IsAlgClosed k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] {S : Set X.left} (hS : IsLocallyClosed S) (hS_ne : S.Nonempty) :
    ∃ x : 𝟙_ (Over (Spec (.of k))) ⟶ X, x.left (default : Spec (.of k)) ∈ S := by
  obtain ⟨x, hx_section, hx_mem⟩ := exists_section_mem X.hom hS hS_ne
  exact ⟨homMk x hx_section, hx_mem⟩

/-- Let `f : A ⟶ S` be smooth and `η i` complex points with dense images in `S`
(`New.IsDenseFamily`). If every complex point of `A` over some `η i` is one of the points `ξ z`,
then the `ξ z` have dense images in `A`. -/
lemma IsDenseFamily.of_fibres {A S : Scheme} {κ Z : Type} {η : κ → (Spec (.of ℂ) ⟶ S)}
    (hη : IsDenseFamily η) (f : A ⟶ S) [s : Smooth f] {ξ : Z → (Spec (.of ℂ) ⟶ A)}
    (h_all : ∀ (i : κ) (y : Spec (.of ℂ) ⟶ A), y ≫ f = η i → ∃ z : Z, ξ z = y) :
    IsDenseFamily ξ := by
  -- As `f` is open, the points of `A` over the `η i` are dense; so it suffices to see that each
  -- of them lies in the closure of the `ξ z`.
  refine (hη.preimage f.isOpenMap).induction (fun x ⟨i, hx⟩ ↦ mem_closure_iff.2 fun U hU hxU ↦ ?_)
    isClosed_closure
  -- An open neighbourhood `U` of `x` contains a complex point over `η i`, which is some `ξ z`.
  let V : A.Opens := ⟨U, hU⟩
  obtain ⟨y, hy⟩ : ∃ y : Spec (.of ℂ) ⟶ V, y ≫ V.ι ≫ f = η i :=
    (Scheme.Hom.exists_comp_eq_iff_mem_range (V.ι ≫ f) _).2 ⟨⟨x, hxU⟩, hx.symm⟩
  obtain ⟨z, hz⟩ := h_all i (y ≫ V.ι) hy
  exact ⟨(y ≫ V.ι) (IsLocalRing.closedPoint ℂ), (y _).property, z, by simp only [hz]⟩

/-- Let `X` be a commutative group scheme (`grp`, a `New.AddObj` structure) locally of finite type
over an algebraically closed field `k`, with structure morphism `s`, and let `P` be a property of
morphisms of schemes induced by a property `Q` of ring maps. If a nonempty open subscheme
`i : Y ⟶ X` has `P` over `k`, so does `X`. -/
lemma AddObj.property_of_isOpenImmersion {k : Type} {X : Scheme} [Field k] [IsAlgClosed k]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] {P : MorphismProperty Scheme}
    {Q : {R S : Type} → [CommRing R] → [CommRing S] → (R →+* S) → Prop} [HasRingHomProperty P Q]
    (grp : AddObj (Over.mk s)) {Y : Scheme} (i : Y ⟶ X) [IsOpenImmersion i] (hY : Nonempty Y)
    (hP : P (i ≫ s)) : P s := by
  -- The translates of `i` (for the group structure `grp`) cover `X`, each has `P` over `k`, and
  -- `P` is local on the source.
  let Pt : Type := 𝟙_ (Over (Spec (.of k))) ⟶ Over.mk s
  let c : Spec (.of k) := default
  have : LocallyOfFiniteType (Over.mk s).hom := inferInstanceAs (LocallyOfFiniteType s)
  obtain ⟨y, a, ha⟩ : ∃ y : Pt, y.left c ∈ range i :=
    exists_point_mem (Over.mk s) i.isLocallyClosed_range (range_nonempty i)
  let t (z : Pt) : Y ⟶ X := i ≫ (translation z).left
  let U : X.Opens := ⨆ z : Pt, (t z).opensRange
  have h_cover (x : X) : ∃ (z : Pt) (b : Y), t z b = x := by
    suffices x ∈ U by simpa [U]
    -- Otherwise the closed complement of `U` has a `k`-point `z`; but translation by `z - y`
    -- carries `y`, which lies in the image of `i`, to `z`.
    by_contra hx
    obtain ⟨z, hz⟩ : ∃ z : Pt, z.left c ∈ (U : Set X)ᶜ :=
      exists_point_mem (Over.mk s) U.isOpen.isClosed_compl.isLocallyClosed ⟨x, hx⟩
    refine hz (TopologicalSpace.Opens.mem_iSup.2 ⟨z - y, a, ?_⟩)
    have h_yz : y ≫ translation (z - y) = z := by simp [Pt, comp_add]
    change (translation (z - y)).left (i a) = z.left c
    rw [ha, ← Hom.comp_apply, ← comp_left, h_yz]
  refine IsZariskiLocalAtSource.of_openCover (.mkOfCovers _ _ t h_cover) fun z ↦ ?_
  -- Translations are morphisms over `k`.
  change P ((i ≫ (translation z).left) ≫ (Over.mk s).hom)
  rwa [Category.assoc, (translation z).w]

/-- A standard smooth ring map is standard smooth of some relative dimension. -/
lemma exists_isStandardSmoothOfRelativeDimension {R T : Type} [CommRing R] [CommRing T]
    {φ : R →+* T} (hφ : φ.IsStandardSmooth) : ∃ n : ℕ, φ.IsStandardSmoothOfRelativeDimension n := by
  algebraize [φ]
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hφ
  exact ⟨P.dimension, ι, σ, hσ, hι, P, rfl⟩

/-- Let `f : X ⟶ S` map the affine open `V` into the affine open `U`. If the ring map
`Γ(S, U) ⟶ Γ(X, V)` is standard smooth of relative dimension `n`, then `Spec Γ(X, V) ⟶ S` is smooth
of relative dimension `n`. -/
lemma smoothOfRelativeDimension_fromSpec_comp {X S : Scheme} {f : X ⟶ S} {U : S.Opens}
    {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) {n : ℕ}
    (hn : (f.appLE U V hVU).hom.IsStandardSmoothOfRelativeDimension n) :
    SmoothOfRelativeDimension n (hV.fromSpec ≫ f) := by
  rw [← hU.SpecMap_appLE_fromSpec f hV hVU]
  have : SmoothOfRelativeDimension n (Spec.map (f.appLE U V hVU)) := HasRingHomProperty.Spec_iff.2
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hn)
  -- The open immersion `hU.fromSpec` has relative dimension `0`.
  exact smoothOfRelativeDimension_comp n 0 (Spec.map (f.appLE U V hVU)) hU.fromSpec

/-- Let `A` be an abelian scheme over `S` (`New.IsAbelianScheme`) with complex points `y i` over
`η i` whose images are dense in `A`. If `g` is the only possible relative dimension of each fibre
over `η i`, then `A` is smooth of relative dimension `g` over `S`. -/
lemma AddObj.smoothOfRelativeDimension_of_fibres {S : Scheme} {κ : Type} {g : ℕ} {A : Over S}
    [IsAbelianScheme A] {η : κ → (Spec (.of ℂ) ⟶ S)} {y : ∀ i : κ, Over.mk (η i) ⟶ A}
    (hy : IsDenseFamily fun i : κ ↦ (y i).left)
    (h_dim : ∀ (i : κ) (n : ℕ), SmoothOfRelativeDimension n (snd A.hom (η i)) → n = g) :
    SmoothOfRelativeDimension g A.hom := by
  -- Around each `x` there is an affine chart `V`, standard smooth of some relative dimension `n`.
  -- It contains some `y i`, so it gives a nonempty open part of the fibre over `η i` that has
  -- dimension `n`; by `property_of_isOpenImmersion` the whole fibre has dimension `n`, and `n = g`
  -- by `h_dim`.
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, hU, V, hV, hxV, hVU, h_std⟩ := Smooth.exists_isStandardSmooth A.hom x
  obtain ⟨n, hn⟩ := exists_isStandardSmoothOfRelativeDimension h_std
  let c : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  obtain ⟨i, hi⟩ : ∃ i : κ, (y i).left c ∈ V := hy.exists_mem_open V.isOpen ⟨x, hxV⟩
  suffices h_fibre : SmoothOfRelativeDimension n (snd A.hom (η i)) by
    obtain rfl : n = g := h_dim i n h_fibre
    exact ⟨U, hU, V, hV, hxV, hVU, hn⟩
  -- Let `j` be the inclusion of the open part of the fibre that lies over `V`.
  let π : Limits.pullback A.hom (η i) ⟶ A.left := fst A.hom (η i)
  let j : Limits.pullback hV.fromSpec π ⟶ Limits.pullback A.hom (η i) := snd hV.fromSpec π
  -- It contains the point `p` of the fibre given by `y i`.
  let p : Spec (.of ℂ) ⟶ Limits.pullback A.hom (η i) := lift (y i).left (𝟙 _) (y i).w
  obtain ⟨p', -⟩ : p c ∈ range j := by
    rwa [range_snd, mem_preimage, ← Hom.comp_apply, show p ≫ π = (y i).left from lift_fst _ _ _,
      hV.range_fromSpec]
  -- `pullbackAddObj` is the group structure on the fibre.
  refine (pullbackAddObj (η i)).property_of_isOpenImmersion (snd A.hom (η i)) j ⟨p'⟩ ?_
  -- This open part of the fibre is the base change of the chart along `η i`.
  have h_square : IsPullback _ (j ≫ snd A.hom (η i)) (hV.fromSpec ≫ A.hom) (η i) :=
    (IsPullback.of_hasPullback hV.fromSpec π).paste_vert (IsPullback.of_hasPullback A.hom (η i))
  exact (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback h_square
    (smoothOfRelativeDimension_fromSpec_comp hU hV hVU hn)

end New

end GeometricPoints

/-!
## Geometric reducedness of smooth morphisms and integral abelian varieties

An étale algebra over a domain is reduced (`New.Variety.isReduced_of_etale`), and an
abelian scheme over an algebraically closed field is integral. Here `New.IsAbelianScheme` asks a
commutative group scheme to be smooth, proper and divisible (multiplication by each `m ≠ 0` is
onto); divisibility takes the place of the usual connectedness of the fibres, and the instance
recovers it.
-/

section AbelianIntegral

open CategoryTheory AlgebraicGeometry Algebra MorphismProperty TensorProduct Set LocallyOfFiniteType

namespace New.Variety

/-- An étale algebra over an integral domain is reduced. Étaleness of `B` over the domain `A` is
an explicit hypothesis, from which the algebra structure is inferred. -/
@[stacks 033B "for an étale algebra over a domain"]
lemma isReduced_of_etale {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] {alg : Algebra A B}
    (h_etale : Algebra.Etale A B) : IsReduced B := by
  -- `B` is flat over `A`, so it embeds in `K ⊗[A] B`, which is unramified over the field `K`.
  let K : Type _ := FractionRing A
  have : IsReduced (K ⊗[A] B) := FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective _ (includeRight_injective (IsFractionRing.injective A K))

/-- An abelian scheme (`New.IsAbelianScheme`: smooth, proper and divisible) over an algebraically
closed field is integral. -/
instance {k : Type} [Field k] [IsAlgClosed k] (A : Over (Spec ⟨k⟩)) [hA : IsAbelianScheme A] :
    AlgebraicGeometry.IsIntegral A.left := by
  -- The `k`-points act by translation on the finite set of irreducible components, so `n • x` fixes
  -- every component, where `n = G.index` is the index of the kernel. As multiplication by `n` is
  -- onto, the component of the origin is everything.
  have : IsReduced A.left := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.hom
  have : IsNoetherian A.left :=
    { isLocallyNoetherian A.hom, compactSpace_of_universallyClosed A.hom with }
  have := (finite_irreducibleComponents_of_isNoetherian (X := A.left)).to_subtype
  -- Translation by a `k`-point is a homeomorphism, so it acts on the irreducible components.
  let P : Type := MonoidalCategoryStruct.tensorUnit (Over (Spec ⟨k⟩)) ⟶ A
  let act : AddAction P (irreducibleComponents A.left) :=
    { vadd g C := ⟨(translation g).left ⁻¹' C, preimage_mem_irreducibleComponents C.prop
        (translation g).left.isOpenEmbedding (by simp [C.prop.1.nonempty, Set.inter_univ])⟩
      zero_vadd := by simp [HVAdd.hVAdd, preimage]
      add_vadd := by simp [P, HVAdd.hVAdd, preimage, ← Scheme.Hom.comp_apply, ← Over.comp_left,
        add_assoc, comp_add] }
  let G : AddSubgroup P := (AddAction.toPermHom P (irreducibleComponents A.left)).ker
  let pt : Spec ⟨k⟩ := default
  let C : irreducibleComponents A.left :=
    ⟨irreducibleComponent ((0 : P).left pt), irreducibleComponent_mem_irreducibleComponents _⟩
  have h_univ : C.val = univ := by
    by_contra h_ne
    -- Otherwise some `k`-point `x` has `n • x` outside `C`.
    have h_onto : Surjective (G.index • 𝟙 A).left := hA.nsmul_surjective _ G.index_ne_zero_of_finite
    obtain ⟨x, hx⟩ : ∃ x : P, x.left pt ∈ (G.index • 𝟙 A).left ⁻¹' C.valᶜ := exists_point_mem A
      (isClosed_irreducibleComponent.isOpen_compl.preimage (by fun_prop)).isLocallyClosed
      ((nonempty_compl.mpr h_ne).preimage h_onto.surj)
    -- But `n • x` is the translate of the origin by `n • x`, which preserves `C`.
    have h_ker : AddAction.toPermHom P _ (G.index • x) = 0 := G.nsmul_index_mem x
    have h_fix : (translation (G.index • x)).left ⁻¹' C.val = C.val :=
      congrArg Subtype.val (DFunLike.congr_fun (congrArg Additive.toMul h_ker) C)
    have h_mem : ((0 : P) ≫ translation (G.index • x)).left pt ∈ C.val :=
      h_fix.symm.subset mem_irreducibleComponent
    have h_transl : (0 : P) ≫ translation (G.index • x) = x ≫ (G.index • 𝟙 A) := by
      simp [comp_add, comp_nsmul]
    exact hx (by rwa [h_transl] at h_mem)
  have : IrreducibleSpace A.left :=
    (irreducibleSpace_def _).mpr (h_univ.subst isIrreducible_irreducibleComponent)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end New.Variety

end AbelianIntegral

/-!
## Specialisation to geometric points and flat morphisms on stalks

`New.Variety.AllSpecializeTo S Q` says that every point of `S` specialises to a geometric point with
the property `Q`.
-/

section Specialisation

open AlgebraicGeometry Scheme RingHom.FaithfullyFlat Flat

/-- Every point of `S` specialises to the image of the closed point under some `t : Spec k ⟶ S` with
`k` algebraically closed and `Q t`. -/
def New.Variety.AllSpecializeTo (S : Scheme)
    (Q : ∀ {k : Type} [Field k], (Spec ⟨k⟩ ⟶ S) → Prop) : Prop :=
  ∀ s : S, ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (t : Spec ⟨k⟩ ⟶ S),
    s ⤳ t (IsLocalRing.closedPoint k) ∧ Q t

/-- For a point `s` of a scheme `Z`, the morphism from the spectrum of the stalk at `s` to `Z` is
flat. -/
instance {Z : Scheme} (s : Z) : Flat (fromSpecStalk Z s) := by
  -- The stalk is a localization of the ring of an affine open `U` around `s`, and `U ⊆ Z` is open.
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  let : Algebra Γ(Z, U) (Z.presheaf.stalk s) := Z.presheaf.algebra_section_stalk (⟨s, hs⟩ : U)
  have := hU.isLocalization_stalk ⟨s, hs⟩
  have : Flat (Spec.map (Z.presheaf.germ U s hs)) :=
    SpecMap_iff.mpr (IsLocalization.flat _ (hU.primeIdealOf ⟨s, hs⟩).asIdeal.primeCompl)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hs, IsAffineOpen.fromSpecStalk]
  infer_instance

/-- A flat morphism of schemes is injective on stalks. -/
lemma New.stalkMap_injective_of_flat {X Y : Scheme} (q : X ⟶ Y) [Flat q] (x : X) :
    Function.Injective (q.stalkMap x) := by
  -- The map of stalks is flat and local, hence faithfully flat, hence injective.
  have h_flat : (q.stalkMap x).hom.Flat := Flat.stalkMap q x
  algebraize [(q.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (q x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (q.stalkMap x).hom)
  exact RingHom.FaithfullyFlat.injective Module.FaithfullyFlat.of_flat_of_isLocalHom

end Specialisation

/-!
## Separating families of points over a stalk and on products of flat schemes

A family of complex points of a scheme is separating (`New.IsSeparatingFamily`) if the scheme is
reduced and the points are dense (`New.IsDenseFamily`); regular functions are then determined by
their values there.
-/

namespace New

open CategoryTheory AlgebraicGeometry Limits pullback Set Scheme Spec Pullback Over PointFn Filter

/-- The base change of a reduced scheme along a flat preimmersion is reduced: its stalks are those
of the scheme. -/
lemma Variety.isReduced_pullback_of_flat {X Y T : Scheme} (f : X ⟶ T) (g : Y ⟶ T)
    [IsReduced X] [Flat g] [IsPreimmersion g] : IsReduced (pullback f g) := by
  have (x : ↥(pullback f g)) : IsReduced ((pullback f g).presheaf.stalk x) := ⟨fun a ha ↦ by
    obtain ⟨b, rfl⟩ := (fst f g).stalkMap_surjective x a
    simp [((IsNilpotent.map_iff (stalkMap_injective_of_flat _ _)).1 ha).eq_zero]⟩
  exact isReduced_of_isReduced_stalk _

/-- The points of a finite set `C` that lie near `s` specialise to `s`. -/
lemma eventually_specializes_of_finite {T : Type*} [TopologicalSpace T] {C : Set T}
    (hC : C.Finite) (s : T) : ∀ᶠ t in nhds s, t ∈ C → t ⤳ s := by
  suffices h : ∀ᶠ t in nhds s, ∀ c ∈ C, t = c → c ⤳ s from h.mono fun t ht htC ↦ ht t htC rfl
  refine hC.eventually_all.2 fun c _ ↦ eventually_imp_distrib_right.2 fun h_freq ↦ ?_
  exact specializes_iff_mem_closure.2 h_freq.mem_closure

/-- Let `S` and `A` be reduced, `z : A ⟶ S`, `s` a point of `S`, and `x w` complex points of `A`
with dense images and with finitely many composites `x w ≫ z`. Consider the pairs of an index `w`
and a map `ψ` from the stalk `𝒪_{S,s}` to `ℂ` such that `x w ≫ z` factors through `Spec 𝒪_{S,s}`
via `Spec.map ψ`. The points `(x w, Spec.map ψ)` of `A ×_S Spec 𝒪_{S,s}` form a separating family:
this scheme is reduced and the images of these points are dense. -/
lemma isSeparatingFamily_stalk {S : Scheme} {W : Type} {A : Scheme} {z : A ⟶ S}
    {x : W → (Spec (.of ℂ) ⟶ A)} [IsReduced A] (h_dense : IsDenseFamily x)
    (h_finite : (range fun w : W ↦ x w ≫ z).Finite) (s : S) :
    IsSeparatingFamily
      (Z := Σ' (w : W) (ψ : S.presheaf.stalk s ⟶ .of ℂ), Spec.map ψ ≫ S.fromSpecStalk s = x w ≫ z)
      fun ⟨w, ψ, h_factor⟩ ↦ (pullback.lift (x w) (Spec.map ψ) h_factor.symm :
        Spec (.of ℂ) ⟶ pullback z (S.fromSpecStalk s)) := by
  let P : Scheme := pullback z (S.fromSpecStalk s)
  let π : P ⟶ A := fst z (S.fromSpecStalk s)
  refine ⟨Variety.isReduced_pullback_of_flat z (S.fromSpecStalk s),
    π.isEmbedding.dense_iff.2 fun y ↦ ?_⟩
  -- Of the finitely many images in `S`, only those that specialise to `s` lie near `s`, and so
  -- near `z (π y)`, which specialises to `s`.
  let c : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  let C : Set S := range fun w : W ↦ (x w ≫ z) c
  have hC : C.Finite := (h_finite.image fun p ↦ p c).subset (by simp [C, ← range_comp'])
  have h_spec : z (π y) ⤳ s := by
    simpa [range_fromSpecStalk] using (range_fst z (S.fromSpecStalk s)).subset (mem_range_self y)
  have h_near : ∀ᶠ a in nhds (π y), z a ∈ C → z a ⤳ s := (z.continuous.tendsto (π y)).eventually
    ((eventually_specializes_of_finite hC s).filter_mono (specializes_iff_nhds.1 h_spec))
  -- So the `x w` whose image specialises to `s` accumulate at `π y`, and these lift.
  refine (((mem_closure_iff_frequently.1 (h_dense (π y))).and_eventually h_near).mono
    ?_).mem_closure
  rintro _ ⟨⟨w, rfl⟩, hw⟩
  have hw_spec : (x w ≫ z) c ⤳ s := hw ⟨w, rfl⟩
  let ψ : S.presheaf.stalk s ⟶ .of ℂ :=
    S.presheaf.stalkSpecializes hw_spec ≫ stalkClosedPointTo (x w ≫ z)
  have hψ : Spec.map ψ ≫ S.fromSpecStalk s = x w ≫ z := by
    rw [Spec.map_comp, Category.assoc, SpecMap_stalkSpecializes_fromSpecStalk]
    exact Spec_stalkClosedPointTo_fromSpecStalk _
  exact ⟨pullback.lift (x w) (Spec.map ψ) hψ.symm c, ⟨⟨w, ψ, hψ⟩, rfl⟩,
    by rw [← Hom.comp_apply, pullback.lift_fst]⟩

/-- Let `S` be reduced with finitely many complex points `ξ i` whose images are dense. An element
`a` of the stalk at `x` is zero if `ψ a = 0` for every map `ψ` from the stalk to `ℂ` such that
some `ξ i` factors through the spectrum of the stalk via `Spec.map ψ`. -/
lemma stalk_eq_zero_of_forall_factor {S : Scheme} [IsReduced S] {J : Type} [Finite J]
    {ξ : J → (Spec (.of ℂ) ⟶ S)} (hξ : IsDenseFamily ξ) {x : S} (a : S.presheaf.stalk x)
    (h_vanish : ∀ (i : J) (ψ : S.presheaf.stalk x ⟶ .of ℂ),
      Spec.map ψ ≫ S.fromSpecStalk x = ξ i → ψ a = 0) :
    a = 0 := by
  -- View `a` as a regular function `f` on the ring-valued points (`PointFn`) of
  -- `S ×_S Spec 𝒪_{S,x}`, where the lifts of the `ξ i` separate. It agrees at these lifts with the
  -- function of the zero section, hence also at the tautological point `inv q`, where it is `a`.
  let q : pullback (𝟙 S) (S.fromSpecStalk x) ⟶ Spec (S.presheaf.stalk x) := snd _ _
  let f : PointFn (pullback (𝟙 S) (S.fromSpecStalk x)) := fun _ y ↦ preimage (y ≫ q) a
  have hf : IsRegularOn f ⊤ := by simp [f, IsRegularOn]
  have h_eq : f _ (inv q) = ofSection (U := ⊤) 0 _ (inv q) := by
    refine (isSeparatingFamily_stalk (z := 𝟙 S) hξ (toFinite _) x).pointFn_ext hf
      (isRegularOn_ofSection 0) (fun ⟨i, ψ, hψ⟩ _ ↦ ?_) _ (inv q) landsIn_top
    -- At the lift given by `ψ` the function `f` takes the value `ψ a`.
    simpa [f, q, pullback.lift_snd] using h_vanish i ψ hψ
  simpa [f] using h_eq

/-- The form of `New.stalk_eq_zero_of_forall_factor` in which the index `i`, the map `ψ` from the
stalk to `ℂ` and the factorisation of `ξ i` via `Spec.map ψ` are bundled into one triple `p` (so
that `p.snd.fst` is `ψ`): for `S` reduced with finitely many dense complex points `ξ i`, an element
`a` of the stalk at `x` is zero if `ψ a = 0` for every such triple. -/
lemma stalk_eq_zero_of_dense {S : Scheme} [IsReduced S] {J : Type} [Finite J]
    {ξ : J → (Spec (.of ℂ) ⟶ S)} (hξ : IsDenseFamily ξ) {x : S} (a : S.presheaf.stalk x)
    (h_vanish : ∀ p : Σ' (i : J) (ψ : S.presheaf.stalk x ⟶ .of ℂ),
      Spec.map ψ ≫ S.fromSpecStalk x = ξ i, p.snd.fst a = 0) : a = 0 :=
  stalk_eq_zero_of_forall_factor hξ a fun i ψ hψ ↦ h_vanish ⟨i, ψ, hψ⟩

open MonoidalCategory IsSchemeTheoreticallyDominant LocallyOfFiniteType CartesianMonoidalCategory

/-- Let X be reduced, locally noetherian, flat and locally of finite type over a reduced locally
noetherian scheme S with finitely many complex points whose images are dense. Then the smooth
locus of X over S is dense in X. -/
lemma dense_smoothLocus_of_isDenseFamily {S : Scheme} [IsReduced S] [IsLocallyNoetherian S]
    {J : Type} [Finite J] {ξ : J → (Spec (.of ℂ) ⟶ S)} (hξ : IsDenseFamily ξ) {X : Scheme}
    (f : X ⟶ S) [LocallyOfFiniteType f] [Flat f] [IsReduced X] :
    Dense (f.smoothLocus : Set X) := by
  -- At a generic point `a` of `X` the stalks of `X` and `S` are fields. The second maps to `ℂ`,
  -- so it has characteristic zero and is perfect, and the extension is formally smooth.
  refine (dense_iff_closure_eq.2 genericPoints.closure).mono fun a ha ↦ ?_
  have hX : IsField (X.presheaf.stalk a) :=
    isField_stalk_of_closure_mem_irreducibleComponents _ a ha
  have hS : IsField (S.presheaf.stalk (f a)) :=
    IsLocalHom.isField (stalkMap_injective_of_flat f a) hX
  -- As `1 ≠ 0` in the stalk, some `ξ i` factors through it.
  obtain ⟨ψ⟩ : Nonempty (S.presheaf.stalk (f a) ⟶ .of ℂ) := by_contra fun h_empty ↦
    one_ne_zero (stalk_eq_zero_of_forall_factor hξ 1 fun _ ψ _ ↦ (h_empty ⟨ψ⟩).elim)
  let : Field (X.presheaf.stalk a) := hX.toField
  let : Field (S.presheaf.stalk (f a)) := hS.toField
  have : CharZero (S.presheaf.stalk (f a)) := ψ.hom.charZero
  have h_ft : (f.stalkMap a).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f a
  algebraize [(f.stalkMap a).hom]
  exact Algebra.FormallySmooth.of_perfectField

/-- Let S be reduced and locally noetherian, with a finite family of complex points whose images are
dense. Let A and B be flat and locally of finite type over S, with A reduced. Let η_w be complex
points of S, and let y_w be complex points of B over η_w that separate B, meaning B is reduced and
the images of the y_w are dense. Suppose that for each w the complex points e_w(v) of A over η_w
have dense image in the fibre A ×_S Spec ℂ over η_w. Then the complex points (e_w(v), y_w) separate
A ×_S B: it is reduced and their images are dense (`New.IsSeparatingFamily`). -/
lemma IsSeparatingFamily.prod {S : Scheme} [IsReduced S] {A B : Over S} {V W J : Type} [Finite J]
    {ξ : J → (Spec (.of ℂ) ⟶ S)} {η : W → (Spec (.of ℂ) ⟶ S)} [LocallyOfFiniteType A.hom]
    [LocallyOfFiniteType B.hom] [IsLocallyNoetherian S] [Flat A.hom] [Flat B.hom]
    {y : ∀ w : W, Over.mk (η w) ⟶ B} {e : ∀ w : W, V → (Over.mk (η w) ⟶ A)}
    (hy : IsSeparatingFamily fun w : W ↦ (y w).left) (hξ : IsDenseFamily ξ)
    (h_red : IsReduced A.left)
    (he : ∀ w : W, IsDenseFamily fun v : V ↦
      (pullback.lift (e w v).left (𝟙 (Spec (.of ℂ))) (e w v).w :
        Spec (.of ℂ) ⟶ pullback A.hom (η w))) :
    IsSeparatingFamily fun ((w, v) : W × V) ↦
      ((CartesianMonoidalCategory.lift (e w v) (y w)).left : Spec (.of ℂ) ⟶ (A ⊗ B).left) := by
  obtain ⟨hB_red : IsReduced B.left, hB_dense⟩ := hy
  have : IsLocallyNoetherian A.left := isLocallyNoetherian A.hom
  have : IsLocallyNoetherian B.left := isLocallyNoetherian B.hom
  -- The smooth locus of `A` over `S`, with inclusion `j`, is dense.
  let j : A.hom.smoothLocus.toScheme ⟶ A.left := A.hom.smoothLocus.ι
  have : Smooth (j ≫ A.hom) := by
    simp [j, ← Hom.smoothLocus_eq_top_iff, ← j.preimage_smoothLocus_eq]
  have : IsDominant j := ⟨(dense_smoothLocus_of_isDenseFamily hξ A.hom).denseRange_subtypeVal⟩
  have : IsSchemeTheoreticallyDominant j := of_isDominant j
  -- Hence `A ×_S B` is reduced: the flat base change `j'` of `j` is scheme-theoretically dominant,
  -- and its source is smooth over the reduced `B`.
  let j' : pullback (j ≫ A.hom) B.hom ⟶ pullback A.hom B.hom :=
    (pullbackRightPullbackFstIso A.hom B.hom j).inv ≫ snd j (fst A.hom B.hom)
  refine ⟨isReduced j', .of_closure ?_⟩
  -- The points of `A ⊗ B` over some `y w` are dense, as `A` is universally open over `S`. Such a
  -- point comes from the fibre of `A` at `η w`, where the `e w v` are dense.
  refine (hB_dense.preimage (pullback.snd A.hom B.hom).isOpenMap).mono ?_
  rintro t ⟨w, hw⟩
  have ht : pullback.snd A.hom B.hom t ∈ range (y w).left := ⟨_, hw⟩
  obtain ⟨u, rfl⟩ : t ∈ range (A ◁ y w).left := by simpa [range_map, whiskerLeft_left] using ht
  refine map_mem_closure (by fun_prop) (he w u) (forall_mem_range.2 fun v ↦ ⟨(w, v), ?_⟩)
  -- The map `A ◁ y w` from the fibre sends `(e w v, 𝟙)` to `(e w v, y w)`.
  have h_lift : lift (e w v) (𝟙 _) ≫ A ◁ y w = lift (e w v) (y w) := by simp
  exact congrArg (fun m : Over.mk (η w) ⟶ A ⊗ B ↦ m.left (IsLocalRing.closedPoint ℂ)) h_lift.symm

end New
