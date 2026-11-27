module

import Mathlib.Data.Rat.Cast.OfScientific
import Std.Tactic.BVDecide.Normalize.BitVec
public import New.Determinant.AuxiliaryForms.PathData
public import New.Determinant.Chain.Moduli
import New.Determinant.Exchange.OneSquare
import Lib.Adelic.Unitary.RationalPoints
import Lib.General.Algebra.MultivariatePolynomials
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.PNatToNat
import Std.Tactic.BVDecide.Normalize.Bool
public import New.Determinant.AuxiliaryForms.LastPath
public import New.UpperBound.Kernels.ThetaLiftGauge
public import New.UpperBound.Objects.RowChain
public import New.UpperBound.Size.ShortColumns
import New.Determinant.AuxiliaryForms.FirstPath
import New.OneLift.ComparisonOperator.FirstFactors
import New.UpperBound.Size.Estimates

section
/-!
# Turning path data, and turns off the diagonal

A turn of a path replaces two sides of a square by the two other sides. The `m`-fold twist is `ϑ`,
the characters of the edges are built from `D.untwistedLiftChar j`, of weight `-D.liftWeight j`, and
the vertical edges, whose character carries a power of `ϑ`, go from `Y^i_j` to `Y^i_(j+1)` and from
`Ỹ^i_j` to `Ỹ^i_(j+1)`. The forms that move in the grid of the `Y` are conjugate forms.

## Main definitions and results

* `New.Data.Corner.IsTurn.exists_isPathDatum`: the match of a path datum, after a Fourier transform
  in the column of the line if the turn is on the diagonal, is a path datum.
* `New.Data.exists_squareLaw_grid_hasAbsUpToNormPower`: the exchange
  `New.Exchange.one_square_identity_of_isEdgeFamily` on a square of a grid, with a constant
  `κ / c ϑ` whose denominator has, up to a power of the norm, the absolute value
  `New.Data.turnRatio`.
* `New.Data.TransfersPeriods`: path data pass forwards, and proportionality of periods passes
  backwards.
* `New.Data.exists_transfersPeriods_off_diagonal`: a turn off the diagonal transfers periods.

Notions from other files:
* `New.Data.GridNode`: a triple `(z, a, b)`, the node `Y^a_b` if `z = false` and `Ỹ^b_a` if
  `z = true`. Its index set is `D.NodeIndex`, which is `D.GridIndex z a b`.
* `New.Data.EdgeTuple`: a matrix over the residue ring modulo `gridModulus ϑ` for each pair of
  nodes. The modulus is that of the twist `ϑ` times a power of the product of the chosen places. A
  `New.Data.NodeFamily` is an invertible matrix `g q` for each node `q`; it takes the matrix `S e`
  on an edge `e = (p, q)` to `(g q)⁻¹ * S e * g p`. It is admissible (`New.Data.IsAdmissibleFamily`)
  if at each of the two starting nodes it lies in the level of the node and at each node
  `(true, a, a)` it is `g ⊕ 1` for its element `g` at `(false, a, a)`.
* `New.Data.IsPathDatum N w`: a function of the matrices on the edges `w` that admissible families
  fix up to `edgeCharProd`, that vanishes unless the vertical edges carry split injective matrices,
  and whose values are sums of at most `N` roots of unity.
* `New.AreMatched`: matched functions, `Φ(x_γ) = χ(det γ) Ψ(y_γ)` with both supported on such
  matrices, `y_γ` being the first columns of `γ` and `x_γ` the last rows of `γ⁻¹`. The subring
  argument, here `⊤`, is where the entries of `γ` and `γ⁻¹` lie. `New.Exchange.matchOf` is the match
  of a function.
* `New.Exchange.SquareLaw` with constant `C`, for functions `L` and `L'` on matrices over a finite
  ring: `∑ Ψ L' = C ∑ Φ L` for all matched `Φ`, `Ψ`.
-/

@[expose] public section

noncomputable section

namespace New.Data

/-!
## Turning a path datum

A turn of a path replaces the edges `V' → W₁`, `Ṽ' → W₂` of a square by `W₁ → V`, `W₂ → Ṽ`, where
`Ṽ' = V'` and `Ṽ = V` unless the turn is on the diagonal, at which a line is added to both.

The form that crosses the square goes from `W₁` to `W₂`. For a turn at `V' = (i, j)` in the grid
of the `Y`, and on the diagonal, `W₁` is the corner `(i, j + 1)` and `W₂` the corner `(i + 1, j)`;
in the grid of the `Ỹ` it is the other way round. On the diagonal the line sits on the edges at
`W₂`. The blocks of `y` and `x` at `W₁`, `W₂` are `y₁`, `y₂` and `x₁`, `x₂`.
-/

section GridMove

open Matrix Fintype Function Finset Exchange

variable {P : Parameters}

/-- The nodes at a turn of a path. The old path has the edges `V' → W₁` and `Ṽ' → W₂`, the new one
has `W₁ → V` and `W₂ → Ṽ`. A node (`GridNode`) is a place `(z, a, b)` in one of the two grids, and
`D.NodeIndex` is the index set of its basis. The type `T` indexes what `Ṽ'` has beyond `V'` and
`Ṽ` beyond `V`: in the use off the diagonal it is empty, and on the diagonal it indexes one line. -/
structure Corner (D : Data P) (B T : Type) where
  /-- The node `V'` that the turn removes. -/
  low : GridNode
  /-- The node `Ṽ' = V' ⊕ T`. -/
  lowExt : GridNode
  /-- The node `W₁`, kept by the turn and joined to `V'` and to `V`. -/
  fst : GridNode
  /-- The node `W₂`, kept by the turn and joined to `Ṽ'` and to `Ṽ`. -/
  snd : GridNode
  /-- The node `V` that the turn adds. -/
  high : GridNode
  /-- The node `Ṽ = V ⊕ T`. -/
  highExt : GridNode
  /-- The basis of `W₂` as it is numbered in the square. -/
  sndEquiv : B ≃ D.NodeIndex snd
  /-- The basis of `Ṽ'` is that of `V'` and `T`. -/
  lowEquiv : D.NodeIndex low ⊕ T ≃ D.NodeIndex lowExt
  /-- The basis of `Ṽ` is that of `V` and `T`. -/
  highEquiv : D.NodeIndex high ⊕ T ≃ D.NodeIndex highExt

namespace Corner

section Definitions

variable {D : Data P} {B T : Type} [Fintype B] [DecidableEq B] [Fintype T] [DecidableEq T]
  (c : D.Corner B T) {ϑ : D.MFoldTwist}

/-- The edges of the old path, `w` being those that the turn preserves. -/
abbrev oldEdges (w : Finset (GridNode × GridNode)) : Finset (GridNode × GridNode) :=
  insert (c.lowExt, c.snd) (insert (c.low, c.fst) w)

/-- The edges of the new path. -/
abbrev newEdges (w : Finset (GridNode × GridNode)) : Finset (GridNode × GridNode) :=
  insert (c.snd, c.highExt) (insert (c.fst, c.high) w)

/-- The character `χ` for which the data on the two sides of the square are matched: the inverse of
the product of the characters `edgeChar` of the two old edges. It lives on the residue ring modulo
`gridModulus ϑ`, the modulus of the twist `ϑ` times a power of the chosen places. -/
def char (ϑ : D.MFoldTwist) : MulChar (gridModulus ϑ).ResidueRing ℂ :=
  (edgeChar ϑ (c.low, c.fst) * edgeChar ϑ (c.lowExt, c.snd))⁻¹

/-- The conditions under which the corner is a turn of a path whose other edges are `w`, for the
twist `ϑ`. A family `g` of invertible matrices, one for each node, is admissible
(`IsAdmissibleFamily`) if it lies in the level at the two starting nodes and is `g ⊕ 1` on the
diagonal of the second grid, for its element `g` at the same place of the first. -/
structure IsTurn (ϑ : D.MFoldTwist) (w : Finset (GridNode × GridNode)) : Prop where
  /-- The two kept nodes differ. -/
  fst_ne_snd : c.fst ≠ c.snd
  /-- The removed nodes are not on the new edges. -/
  ne_low_and_ne_lowExt : ∀ q ∈ [c.fst, c.snd, c.high, c.highExt], q ≠ c.low ∧ q ≠ c.lowExt
  /-- The other edges avoid the removed nodes and do not end at the added ones. -/
  endpoints_notMem : ∀ e ∈ w, e.1 ∉ [c.low, c.lowExt] ∧ e.2 ∉ [c.low, c.lowExt, c.high, c.highExt]
  /-- One old edge is vertical, and the new edge at the same kept node is not. -/
  vertical : IsVerticalEdge c.low c.fst ∧ ¬IsVerticalEdge c.fst c.high ∨
    IsVerticalEdge c.lowExt c.snd ∧ ¬IsVerticalEdge c.snd c.highExt
  /-- Opposite edges have the same character. -/
  edgeChar_fst : edgeChar ϑ (c.fst, c.high) = edgeChar ϑ (c.lowExt, c.snd)
  /-- Opposite edges have the same character. -/
  edgeChar_snd : edgeChar ϑ (c.snd, c.highExt) = edgeChar ϑ (c.low, c.fst)
  /-- Only the group of `V` acts at `Ṽ`. -/
  apply_highExt (g : NodeFamily ϑ) (hg : IsAdmissibleFamily g) :
    g c.highExt = blockInlGL c.highEquiv (g c.high)
  /-- The node `V'` is inner: any element `k` may act there, through `k ⊕ 1` at `Ṽ'`. -/
  exists_eq_low (g : NodeFamily ϑ) (hg : IsAdmissibleFamily g)
      (k : GL (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing) :
    ∃ g' : NodeFamily ϑ, IsAdmissibleFamily g' ∧ g' c.low = k ∧
      g' c.lowExt = blockInlGL c.lowEquiv k ∧ ∀ q : GridNode, q ≠ c.low → q ≠ c.lowExt → g' q = g q

variable (S : EdgeTuple ϑ)

/-- The matrix `y : V' → W₁ ⊕ W₂` read on the old edges. -/
def oldMatrix : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing :=
  fromRows (S (c.low, c.fst)) ((S (c.lowExt, c.snd)).submatrix c.sndEquiv c.lowEquiv).toCols₁

/-- The column `v : T → W₂` read on the old edge at `Ṽ'`. -/
def oldColumn : Matrix B T (gridModulus ϑ).ResidueRing :=
  ((S (c.lowExt, c.snd)).submatrix c.sndEquiv c.lowEquiv).toCols₂

/-- The matrix `x : W₁ ⊕ W₂ → V` read on the new edges. -/
def newMatrix : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing :=
  fromCols (S (c.fst, c.high)) ((S (c.snd, c.highExt)).submatrix c.highEquiv c.sndEquiv).toRows₁

/-- The row `v' : W₂ → T` read on the new edge at `Ṽ`. -/
def newRow : Matrix T B (gridModulus ϑ).ResidueRing :=
  ((S (c.snd, c.highExt)).submatrix c.highEquiv c.sndEquiv).toRows₂

/-- The tuple with `y` and `v` on the old edges and the matrices of `S` elsewhere. -/
def oldTuple (y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing)
    (v : Matrix B T (gridModulus ϑ).ResidueRing) : EdgeTuple ϑ :=
  update (update S (c.low, c.fst) y.toRows₁) (c.lowExt, c.snd)
    ((fromCols y.toRows₂ v).submatrix c.sndEquiv.symm c.lowEquiv.symm)

/-- The tuple with `x` and `v'` on the new edges and the matrices of `S` elsewhere. -/
def newTuple (x : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing)
    (v' : Matrix T B (gridModulus ϑ).ResidueRing) : EdgeTuple ϑ :=
  update (update S (c.fst, c.high) x.toCols₁) (c.snd, c.highExt)
    ((fromRows x.toCols₂ v').submatrix c.highEquiv.symm c.sndEquiv.symm)

/-- The column Fourier transform `Ψ̂'(y, v') = ∑ v, ψ(v' v) Ψ'(y, v)` in the column `v` of the line,
where `ψ(v' v)` is the additive character `ψ` at the trace of `v' v` and the matrices on the other
edges are those of `S`. -/
def columnFourier (ψ : AddChar (gridModulus ϑ).ResidueRing ℂ) (Ψ' : EdgeTuple ϑ → ℂ)
    (S : EdgeTuple ϑ) (v' : Matrix T B (gridModulus ϑ).ResidueRing)
    (y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing) : ℂ :=
  ∑ v : Matrix B T (gridModulus ϑ).ResidueRing, ψ (v' * v).trace * Ψ' (c.oldTuple S y v)

/-- The datum on the new path: the match for the character `c.char ϑ` of the column Fourier
transform of `Ψ'`, taken at the row `v'` and the matrix `x` that are read on the new edges of `S`.
The bijection `ε` identifies the indices of `V'` and `V` with those of `W₁ ⊕ W₂`. -/
def turned (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B)
    (ψ : AddChar (gridModulus ϑ).ResidueRing ℂ) (Ψ' : EdgeTuple ϑ → ℂ) (S : EdgeTuple ϑ) : ℂ :=
  matchOf (c.char ϑ) ε (c.columnFourier ψ Ψ' S (c.newRow S)) (c.newMatrix S)

/-- The element of a family at `W₂`, in the basis of the square. -/
abbrev sndGL (g : NodeFamily ϑ) : GL B (gridModulus ϑ).ResidueRing :=
  reindexGL c.sndEquiv.symm (g c.snd)

/-- The element of a family on `W₁ ⊕ W₂`. -/
abbrev sumGL (g : NodeFamily ϑ) : GL (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing :=
  blockGL (g c.fst, c.sndGL g)

end Definitions

variable {D : Data P} {B T : Type} [Fintype T] [DecidableEq T]
  {c : D.Corner B T} {ϑ : D.MFoldTwist} {w : Finset (GridNode × GridNode)} {N : ℕ}
  {Ψ' : EdgeTuple ϑ → ℂ}

section Tuples

variable {S : EdgeTuple ϑ}
  (y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing)
  (v : Matrix B T (gridModulus ϑ).ResidueRing)
  (x : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing)
  (v' : Matrix T B (gridModulus ϑ).ResidueRing)

omit [Fintype T] [DecidableEq T] in
lemma oldColumn_oldTuple : c.oldColumn (c.oldTuple S y v) = v := by simp [oldColumn, oldTuple]

omit [Fintype T] [DecidableEq T] in
lemma newRow_newTuple : c.newRow (c.newTuple S x v') = v' := by simp [newRow, newTuple]

namespace IsTurn

lemma low_notMem (hc : c.IsTurn ϑ w) : (c.low, c.fst) ∉ w := by grind [→ hc.endpoints_notMem]

lemma lowExt_notMem (hc : c.IsTurn ϑ w) : (c.lowExt, c.snd) ∉ w := by grind [→ hc.endpoints_notMem]

lemma high_notMem (hc : c.IsTurn ϑ w) : (c.fst, c.high) ∉ w := by grind [→ hc.endpoints_notMem]

lemma highExt_notMem (hc : c.IsTurn ϑ w) : (c.snd, c.highExt) ∉ w := by
  grind [→ hc.endpoints_notMem]

lemma oldTuple_apply_of_mem (hc : c.IsTurn ϑ w) {e : GridNode × GridNode} (he : e ∈ w) :
    c.oldTuple S y v e = S e := by
  simp [oldTuple, ne_of_mem_of_not_mem he hc.lowExt_notMem, ne_of_mem_of_not_mem he hc.low_notMem]

lemma newTuple_apply_of_mem (hc : c.IsTurn ϑ w) {e : GridNode × GridNode} (he : e ∈ w) :
    c.newTuple S x v' e = S e := by
  simp [newTuple, ne_of_mem_of_not_mem he hc.highExt_notMem, ne_of_mem_of_not_mem he hc.high_notMem]

lemma oldTuple_low (hc : c.IsTurn ϑ w) : c.oldTuple S y v (c.low, c.fst) = y.toRows₁ := by
  simp [oldTuple, hc.fst_ne_snd]

lemma oldMatrix_oldTuple (hc : c.IsTurn ϑ w) : c.oldMatrix (c.oldTuple S y v) = y := by
  simp [oldMatrix, oldTuple, hc.fst_ne_snd]

lemma newMatrix_newTuple (hc : c.IsTurn ϑ w) : c.newMatrix (c.newTuple S x v') = x := by
  simp [newMatrix, newTuple, hc.fst_ne_snd]

end IsTurn

end Tuples

variable [Fintype B] [DecidableEq B]

namespace IsTurn

/-- Let the corner `c` be a turn, for the twist `ϑ`, of a path whose other edges are `w`. A sum over
the tuples on the old edges is a sum over three things, put together by `oldTuple`: a tuple `S` on
the preserved edges `w`, a matrix `y` on the old edges and a matrix `v` of type `Matrix B T`. Here
`tuplesOn ϑ w` is the set of tuples of matrices that are zero off `w`. -/
lemma sum_tuplesOn_oldEdges (hc : c.IsTurn ϑ w) (F : EdgeTuple ϑ → ℂ) :
    ∑ S ∈ tuplesOn ϑ (c.oldEdges w), F S = ∑ S ∈ tuplesOn ϑ w,
      ∑ y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing,
        ∑ v : Matrix B T (gridModulus ϑ).ResidueRing, F (c.oldTuple S y v) := by
  rw [sum_tuplesOn_insert (by simp [hc.lowExt_notMem, hc.fst_ne_snd.symm]),
    sum_tuplesOn_insert hc.low_notMem]
  refine sum_congr rfl fun S _ ↦ ?_
  -- `y` has the rows `y₁` and `y₂`, and the matrix at `Ṽ' → W₂` has the columns `y₂` and `v`.
  rw [sum_eq_sum_fromRows]
  refine sum_congr rfl fun y₁ _ ↦ ?_
  rw [← (reindex c.sndEquiv c.lowEquiv).sum_comp, sum_eq_sum_fromCols, sum_comm]
  simp [oldTuple]

/-- Let the corner `c` be a turn, for the twist `ϑ`, of a path whose other edges are `w`. A sum over
the tuples on the new edges is a sum over three things, put together by `newTuple`: a tuple `S` on
the preserved edges `w`, a matrix `v'` of type `Matrix T B` and a matrix `x` on the new edges. -/
lemma sum_tuplesOn_newEdges (hc : c.IsTurn ϑ w) (F : EdgeTuple ϑ → ℂ) :
    ∑ S ∈ tuplesOn ϑ (c.newEdges w), F S = ∑ S ∈ tuplesOn ϑ w,
      ∑ v' : Matrix T B (gridModulus ϑ).ResidueRing,
        ∑ x : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing,
          F (c.newTuple S x v') := by
  rw [sum_tuplesOn_insert (by simp [hc.highExt_notMem, hc.fst_ne_snd.symm]),
    sum_tuplesOn_insert hc.high_notMem]
  refine sum_congr rfl fun S _ ↦ ?_
  -- `x` has the columns `x₁` and `x₂`, and the matrix at `W₂ → Ṽ` has the rows `x₂` and `v'`.
  rw [sum_comm (γ := Matrix T B (gridModulus ϑ).ResidueRing), sum_eq_sum_fromCols, eq_comm,
    sum_comm]
  refine sum_congr rfl fun x₁ _ ↦ ?_
  rw [← (reindex c.highEquiv c.sndEquiv).sum_comp, sum_eq_sum_fromRows]
  simp [newTuple]

section Turned

variable {ψ : AddChar (gridModulus ϑ).ResidueRing ℂ}

/-- The column Fourier transform of a path datum `Ψ'` on the old path depends on `S` only through
the matrices of the preserved edges `w`. -/
lemma columnFourier_congr {S S' : EdgeTuple ϑ} (hc : c.IsTurn ϑ w)
    (hΨ' : IsPathDatum N (c.oldEdges w) Ψ') (h_eq : ∀ e ∈ w, S e = S' e) :
    c.columnFourier ψ Ψ' S = c.columnFourier ψ Ψ' S' := by
  funext v' y
  refine sum_congr rfl fun v _ ↦ congrArg _ (hΨ'.dependsOn fun e he ↦ ?_)
  -- The tuples of `S, y, v` and of `S', y, v` agree on every old edge.
  obtain rfl | rfl | he : e = (c.lowExt, c.snd) ∨ e = (c.low, c.fst) ∨ e ∈ w := by simpa using he
  · simp [oldTuple]
  · simp [hc.oldTuple_low]
  · simp [hc.oldTuple_apply_of_mem _ _ he, h_eq e he]

/-- Let the corner be a turn and `Ψ'` a path datum on the old path, let `g` be an admissible family
and let `k` be an invertible matrix at the removed node `c.low`. Then moving `S` by `g`, replacing
`v'` by `v' * c.sndGL g` and `y` by `(c.sumGL g)⁻¹ * y * k` changes the column Fourier transform
only by the characters of the edges at the determinants. -/
lemma columnFourier_tupleAction (hc : c.IsTurn ϑ w)
    (y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing)
    (v' : Matrix T B (gridModulus ϑ).ResidueRing) (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    {g : NodeFamily ϑ} (hg : IsAdmissibleFamily g)
    (k : GL (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing) (S : EdgeTuple ϑ) :
    c.char ϑ k.val.det * edgeChar ϑ (c.low, c.fst) (g c.fst).val.det *
      edgeChar ϑ (c.lowExt, c.snd) (g c.snd).val.det * edgeCharProd g w *
      c.columnFourier ψ Ψ' (tupleAction g S) (v' * (c.sndGL g).val)
        ((c.sumGL g)⁻¹.val * y * k.val) =
    c.columnFourier ψ Ψ' S v' y := by
  -- Let `g'` be `k` at `V'`, `k ⊕ 1` at `Ṽ'` and `g` elsewhere. By invariance `Ψ'` at a tuple moved
  -- by `g'` is its value divided by the characters; the sum over `v` is reindexed by `v ↦ g⁻¹ v`.
  obtain ⟨g', hg', h_low, h_ext, h_other⟩ := hc.exists_eq_low g hg k
  obtain ⟨h_fst, h_snd⟩ : g' c.fst = g c.fst ∧ g' c.snd = g c.snd := by
    simp [h_other, hc.ne_low_and_ne_lowExt]
  have h_w : ∀ e ∈ w, g' e.1 = g e.1 ∧ g' e.2 = g e.2 := by grind [→ hc.endpoints_notMem]
  have h_char : edgeCharProd g' (c.oldEdges w) =
      c.char ϑ k.val.det * edgeChar ϑ (c.low, c.fst) (g c.fst).val.det *
        edgeChar ϑ (c.lowExt, c.snd) (g c.snd).val.det * edgeCharProd g w := by
    simp +contextual [edgeCharProd, char, hc.low_notMem, hc.lowExt_notMem, hc.fst_ne_snd.symm,
      h_low, h_ext, h_fst, h_snd, h_w, MulChar.inv_apply_eq_inv', field]
  -- Moving the tuple of `S, y, v` by `g'` moves `S`, `y` and `v` separately.
  have h_tuple (v : Matrix B T (gridModulus ϑ).ResidueRing) :
      Ψ' (tupleAction g' (c.oldTuple S y v)) = Ψ' (c.oldTuple (tupleAction g S)
        ((c.sumGL g)⁻¹.val * y * k.val) ((c.sndGL g)⁻¹.val * v)) := by
    refine hΨ'.dependsOn fun e he ↦ ?_
    obtain rfl | rfl | he : e = (c.lowExt, c.snd) ∨ e = (c.low, c.fst) ∨ e ∈ w := by simpa using he
    · -- On `Ṽ' → W₂` the equation holds entry by entry in the two blocks of columns.
      simp [tupleAction, oldTuple, h_ext, h_snd, ← Matrix.ext_iff, ← map_inv, Matrix.mul_apply,
        reindex_equiv c.sndEquiv, reindex_equiv c.lowEquiv, toRows₂, Matrix.one_apply]
    · -- On `V' → W₁` it is the block `y₁` that moves.
      simp [tupleAction, hc.oldTuple_low, h_low, h_fst, ← Matrix.ext_iff, ← map_inv,
        Matrix.mul_apply, toRows₁]
    · simp [tupleAction, hc.oldTuple_apply_of_mem _ _ he, h_w e he]
  rw [← h_char, columnFourier, columnFourier,
    ← (mul_right_injective_of_invertible (c.sndGL g)⁻¹.val).bijective_of_finite.sum_comp, mul_sum]
  refine sum_congr rfl fun v _ ↦ ?_
  have h_cancel : v' * (c.sndGL g).val * ((c.sndGL g)⁻¹.val * v) = v' * v := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ v, Units.mul_inv, Matrix.one_mul]
  rw [h_cancel, ← h_tuple, mul_left_comm, hΨ'.invariant g' hg']

/-- If the column Fourier transform of a path datum `Ψ'` on the old path is nonzero at `(v', y)`,
then the blocks of rows of `y` that lie on vertical edges, and the matrices of `S` on the vertical
edges in `w`, have left inverses. -/
lemma hasLeftInv_of_columnFourier_ne_zero {S : EdgeTuple ϑ} (hc : c.IsTurn ϑ w)
    (y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing)
    (v' : Matrix T B (gridModulus ϑ).ResidueRing) (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (h_ne : c.columnFourier ψ Ψ' S v' y ≠ 0) :
    (IsVerticalEdge c.low c.fst → HasLeftInv y.toRows₁) ∧
    (IsVerticalEdge c.lowExt c.snd → HasLeftInv y.toRows₂) ∧
    ∀ e ∈ w, IsVerticalEdge e.1 e.2 → HasLeftInv (S e) := by
  obtain ⟨v, -, hv⟩ := exists_ne_zero_of_sum_ne_zero h_ne
  have h_inv : ∀ e ∈ c.oldEdges w, IsVerticalEdge e.1 e.2 → HasLeftInv (c.oldTuple S y v e) :=
    hΨ'.hasLeftInv _ (right_ne_zero_of_mul hv)
  refine ⟨fun h_vert ↦ ?_, fun h_vert ↦ ?_, fun e he h_vert ↦ ?_⟩
  · simpa [hc.oldTuple_low] using h_inv (c.low, c.fst) (by simp) h_vert
  · -- A left inverse of `(y₂ v)` has a left inverse of `y₂` as its upper block.
    obtain ⟨L, hL⟩ : HasLeftInv (c.oldTuple S y v (c.lowExt, c.snd)) := h_inv _ (by simp) h_vert
    refine ⟨L.submatrix (c.lowEquiv ∘ .inl) c.sndEquiv, Matrix.ext fun i j ↦ ?_⟩
    simpa [oldTuple, Matrix.mul_apply, reindex_equiv c.sndEquiv, Matrix.one_apply] using
      congrFun₂ hL (c.lowEquiv (.inl i)) (c.lowEquiv (.inl j))
  · simpa [hc.oldTuple_apply_of_mem _ _ he] using h_inv e (by simp [he]) h_vert

/-- An admissible family `g` moves the row `v'` read on the new edge at `Ṽ` only through its
element at `W₂`. -/
lemma newRow_tupleAction (hc : c.IsTurn ϑ w) {g : NodeFamily ϑ} (hg : IsAdmissibleFamily g)
    (S : EdgeTuple ϑ) : c.newRow (tupleAction g S) = c.newRow S * (c.sndGL g).val := by
  -- Entry by entry, as `g` fixes the line at `Ṽ`.
  ext i j
  simp [newRow, tupleAction, hc.apply_highExt g hg, ← map_inv, Matrix.mul_apply,
    reindex_equiv c.sndEquiv, reindex_equiv c.highEquiv, toRows₂, Matrix.one_apply]

/-- Let the corner `c` be a turn (`hc`). An admissible family `g` acts on tuples by `tupleAction`.
This moves the matrix `c.newMatrix S` read on the new edges on the left by `(g c.high)⁻¹`, the
inverse of its element at the node `V = c.high`. It moves it on the right by `c.sumGL g`, its
element on `W₁ ⊕ W₂`. -/
lemma newMatrix_tupleAction (hc : c.IsTurn ϑ w) {g : NodeFamily ϑ} (hg : IsAdmissibleFamily g)
    (S : EdgeTuple ϑ) :
    c.newMatrix (tupleAction g S) = (g c.high)⁻¹.val * (c.newMatrix S * (c.sumGL g).val) := by
  -- Entry by entry, in the columns of `W₁` and in those of `W₂`.
  rw [← Matrix.mul_assoc]
  ext i (j | j) <;> simp [newMatrix, tupleAction, hc.apply_highExt g hg, ← map_inv, toRows₁,
    Matrix.mul_apply, reindex_equiv c.sndEquiv, reindex_equiv c.highEquiv]

/-- Let the corner `c` be a turn (`hc`), `Ψ'` a path datum on the old edges (`hΨ'`) and `v'` a
matrix. Then the function `matchOf` of the column Fourier transform `c.columnFourier ψ Ψ' S v'` is
matched with this transform for the character `c.char ϑ`. -/
lemma areMatched_columnFourier (hc : c.IsTurn ϑ w) (v' : Matrix T B (gridModulus ϑ).ResidueRing)
    (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B) (S : EdgeTuple ϑ) :
    AreMatched ⊤ ε (c.char ϑ) (matchOf (c.char ϑ) ε (c.columnFourier ψ Ψ' S v'))
      (c.columnFourier ψ Ψ' S v') := by
  refine areMatched_matchOf (fun y hy ↦ ?_) fun y k ↦ ?_
  · -- The support condition: one of the blocks of `y` lies on a vertical edge.
    obtain ⟨h_fst, h_snd, -⟩ := hc.hasLeftInv_of_columnFourier_ne_zero y v' hΨ' hy
    exact exists_eq_firstCols (Modulus.isValuationPair_residueRing _) ε (by grind [hc.vertical])
  · -- The character condition: invariance under the identity family, with `k` at `V'`.
    simpa [tupleAction_one, edgeCharProd, ← Prod.one_eq_mk] using
      hc.columnFourier_tupleAction y v' hΨ' (g := 1)
        (by simp [IsAdmissibleFamily, ← Prod.one_eq_mk]) k S

/-- Let the corner `c` be a turn and `Ψ'` a path datum on the old path. The turned datum
`c.turned ε ψ Ψ'` is the match of the Fourier transform of `Ψ'` in the column of the line, read on
the new edges; `ε` is the bijection between the indices of the removed and added nodes and those of
the two kept nodes. It is fixed by the action of an admissible family `g` up to `edgeCharProd g` of
the edges of the new path: the product over the edges `(p, q)` of their characters at
`det (g q) / det (g p)`. -/
lemma turned_tupleAction (hc : c.IsTurn ϑ w) (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B)
    {g : NodeFamily ϑ} (hg : IsAdmissibleFamily g) (S : EdgeTuple ϑ) :
    edgeCharProd g (c.newEdges w) * c.turned ε ψ Ψ' (tupleAction g S) = c.turned ε ψ Ψ' S := by
  -- The match commutes with the action at `W₁ ⊕ W₂` and transforms by `χ⁻¹` at `V`.
  let H := c.columnFourier ψ Ψ' (tupleAction g S) (c.newRow S * (c.sndGL g).val)
  let a : ℂ := edgeChar ϑ (c.low, c.fst) (g c.fst).val.det *
    edgeChar ϑ (c.lowExt, c.snd) (g c.snd).val.det * edgeCharProd g w
  have h_moved := hc.areMatched_columnFourier (ψ := ψ) (c.newRow S * (c.sndGL g).val) hΨ' ε
    (tupleAction g S)
  have h_fourier :
      c.columnFourier ψ Ψ' S (c.newRow S) = fun y ↦ a * H ((c.sumGL g)⁻¹.val * y) :=
    funext fun y ↦ by
      simpa [a, H] using (hc.columnFourier_tupleAction y (c.newRow S) hΨ' hg 1 S).symm
  rw [turned, turned, hc.newRow_tupleAction hg, hc.newMatrix_tupleAction hg,
    ← h_moved.left_mul (g := g c.high) (by simp [mem_intGL]),
    ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
    (hc.areMatched_columnFourier (c.newRow S) hΨ' ε S).unique
      (by simpa only [h_fourier] using h_moved.translate a (c.sumGL g)),
    ← mul_assoc]
  -- Opposite edges have the same character.
  congr 1
  simp [a, edgeCharProd, char, hc.high_notMem, hc.highExt_notMem, hc.fst_ne_snd.symm,
    hc.edgeChar_fst, hc.edgeChar_snd, hc.apply_highExt g hg, MulChar.inv_apply_eq_inv']
  field [MulChar.apply_eq_zero_iff]

/-! ### The turned datum and the sum over a square -/

/-- Let the corner `c` be a turn (`hc`) and `Ψ'` a path datum on the old edges (`hΨ'`). If
`c.turned ε ψ Ψ' S` is nonzero, then there is an invertible matrix `γ` with
`c.newMatrix S = invLastRows ε γ`, the matrix on the new edges. For this `γ` the value
`c.turned ε ψ Ψ' S` is `χ(det γ)`, for `χ = c.char ϑ`, times `c.columnFourier ψ Ψ' S` taken at the
row `c.newRow S` and at `firstCols ε γ`. -/
lemma exists_turned_eq {S : EdgeTuple ϑ} (hc : c.IsTurn ϑ w)
    (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B)
    (hS : c.turned ε ψ Ψ' S ≠ 0) :
    ∃ γ : GL (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing,
      c.newMatrix S = invLastRows ε γ ∧
      c.turned ε ψ Ψ' S =
        c.char ϑ γ.val.det * c.columnFourier ψ Ψ' S (c.newRow S) (firstCols ε γ) := by
  have h_match := hc.areMatched_columnFourier (ψ := ψ) (c.newRow S) hΨ' ε S
  obtain ⟨γ, hγ, hx⟩ := h_match.supp_left _ hS
  exact ⟨γ, hx, by rw [turned, hx, h_match.apply_eq γ hγ]⟩

/-- Let the corner be a turn, `Ψ'` a path datum on the old path and `ε` the bijection between the
indices of the removed and added nodes and those of the two kept nodes, for which the turned datum
is formed. Where this datum is nonzero at `S`, the matrices of `S` on the vertical edges of the new
path have left inverses, as a path datum on the new path requires. -/
lemma hasLeftInv_of_turned_ne_zero {S : EdgeTuple ϑ} (hc : c.IsTurn ϑ w)
    (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B)
    (hS : c.turned ε ψ Ψ' S ≠ 0) :
    ∀ e ∈ c.newEdges w, IsVerticalEdge e.1 e.2 → HasLeftInv (S e) := by
  obtain ⟨γ, hx, h_value⟩ := hc.exists_turned_eq hΨ' ε hS
  obtain ⟨h_fst, h_snd, h_w⟩ := hc.hasLeftInv_of_columnFourier_ne_zero (firstCols ε γ)
    (c.newRow S) hΨ' (right_ne_zero_of_mul (h_value.symm.trans_ne hS))
  obtain ⟨h_cols₂, h_cols₁⟩ :
      (HasLeftInv (firstCols ε γ).toRows₁ → HasLeftInv (c.newMatrix S).toCols₂) ∧
      (HasLeftInv (firstCols ε γ).toRows₂ → HasLeftInv (c.newMatrix S).toCols₁) := by
    simpa only [hx] using hasLeftInv_toCols_of_hasLeftInv_toRows ε γ
  -- A vertical new edge is opposite to a vertical old edge.
  have h_opp₁ : IsVerticalEdge c.fst c.high → IsVerticalEdge c.lowExt c.snd := by
    grind [hc.vertical]
  have h_opp₂ : IsVerticalEdge c.snd c.highExt → IsVerticalEdge c.low c.fst := by
    grind [hc.vertical]
  simp only [mem_insert, forall_eq_or_imp]
  refine ⟨fun h_vert ↦ ?_, fun h_vert ↦ ?_, h_w⟩
  · -- The matrix `(x₂; v')` is split injective where `x₂` is.
    obtain ⟨L, hL⟩ : HasLeftInv (c.newMatrix S).toCols₂ := h_cols₂ (h_fst (h_opp₂ h_vert))
    refine ⟨(fromCols L 0).submatrix c.sndEquiv.symm c.highEquiv.symm, ?_⟩
    simpa [newMatrix, ← Matrix.ext_iff, Matrix.mul_apply, reindex_equiv c.sndEquiv,
      reindex_equiv c.highEquiv, toRows₁, Matrix.one_apply] using hL
  · simpa [newMatrix] using h_cols₁ (h_snd (h_opp₁ h_vert))

/-- Let the corner `c` be a turn (`hc`) and `Ψ'` a path datum (`IsPathDatum`) on the old edges,
whose values are sums of at most `N` roots of unity. Then each value `c.turned ε ψ Ψ' S` of the
datum on the new path is a sum of roots of unity, at most `N` times the number of matrices in
`Matrix B T` over the residue ring. -/
lemma isSumOfRootsOfUnity_turned (hc : c.IsTurn ϑ w) (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B) (S : EdgeTuple ϑ) :
    IsSumOfRootsOfUnity (card (Matrix B T (gridModulus ϑ).ResidueRing) * N)
      (c.turned ε ψ Ψ' S) := by
  by_cases hS : c.turned ε ψ Ψ' S = 0
  · simpa only [hS] using IsSumOfRootsOfUnity.zero
  obtain ⟨γ, -, h_value⟩ := hc.exists_turned_eq hΨ' ε hS
  have h_char : IsOfFinOrder (c.char ϑ γ.val.det) :=
    (c.char ϑ).isOfFinOrder (isUnits_det_units γ).isOfFinOrder
  have h_psi (r : (gridModulus ϑ).ResidueRing) : IsOfFinOrder (ψ r) :=
    ψ.toMonoidHom.isOfFinOrder (isMulTorsion_of_finite _)
  rw [h_value]
  exact .mul_left (.sum fun v ↦ (hΨ'.isSumOfRootsOfUnity _).mul_left (h_psi _)) h_char

end Turned

/-- Turning a path datum: let the corner be a turn and let `Ψ'` be a path datum on the old path,
with at most `N` roots of unity in a value. Hold fixed the matrices of the preserved edges and take
the Fourier transform of `Ψ'` in the column of the line (`columnFourier`). For each row `v'` the
match of the transform is `Ψ(·, v')` for a path datum `Ψ` on the new path, and the bound for the
number of roots of unity in a value is multiplied by the number of column matrices `v`. -/
theorem exists_isPathDatum (hc : c.IsTurn ϑ w) (hΨ' : IsPathDatum N (c.oldEdges w) Ψ')
    (ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B)
    (ψ : AddChar (gridModulus ϑ).ResidueRing ℂ) :
    ∃ Ψ : EdgeTuple ϑ → ℂ,
      IsPathDatum (card (Matrix B T (gridModulus ϑ).ResidueRing) * N) (c.newEdges w) Ψ ∧
      ∀ (S : EdgeTuple ϑ) (v' : Matrix T B (gridModulus ϑ).ResidueRing),
        AreMatched ⊤ ε (c.char ϑ)
          (fun x : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing ↦
            Ψ (c.newTuple S x v'))
          (c.columnFourier ψ Ψ' S v') := by
  -- The datum is the turned one; it depends only on the matrices of the new edges.
  have h_dep : DependsOn (c.turned ε ψ Ψ') (c.newEdges w : Set (GridNode × GridNode)) := by
    intro S S' h_agree
    have h_fourier : c.columnFourier ψ Ψ' S = c.columnFourier ψ Ψ' S' :=
      hc.columnFourier_congr hΨ' fun e he ↦ h_agree e (by simp [he])
    simp only [turned, newRow, newMatrix, h_agree (c.snd, c.highExt) (by simp),
      h_agree (c.fst, c.high) (by simp), h_fourier]
  refine ⟨c.turned ε ψ Ψ', ⟨h_dep, fun g hg ↦ hc.turned_tupleAction hΨ' ε hg,
    fun S ↦ hc.hasLeftInv_of_turned_ne_zero hΨ' ε, hc.isSumOfRootsOfUnity_turned hΨ' ε⟩,
    fun S v' ↦ ?_⟩
  have h_turned : (fun x ↦ c.turned ε ψ Ψ' (c.newTuple S x v')) =
      matchOf (c.char ϑ) ε (c.columnFourier ψ Ψ' S v') := by
    funext x
    rw [turned, newRow_newTuple, hc.newMatrix_newTuple,
      hc.columnFourier_congr hΨ' fun e he ↦ hc.newTuple_apply_of_mem x v' he]
  simpa only [h_turned] using hc.areMatched_columnFourier v' hΨ' ε S

/-- The exchange on a square at which the path turns. The sum over the tuples on the old path
(`tuplesOn`) against `Ψ'` equals `C` times the sum over the tuples on the new path against a datum
`Ψ` that matches the column Fourier transform of `Ψ'`. The square law with constant `C` is given for
a family of pairs `L i, L' i`. The index `f S v'` may depend on the matrices of the preserved edges
`w` and on the row `v'`. -/
lemma sum_eq_of_squareLaw (hc : c.IsTurn ϑ w) {Ψ : EdgeTuple ϑ → ℂ}
    {ψ : AddChar (gridModulus ϑ).ResidueRing ℂ}
    {ε : D.NodeIndex c.low ⊕ D.NodeIndex c.high ≃ D.NodeIndex c.fst ⊕ B}
    (h_match : ∀ (S : EdgeTuple ϑ) (v' : Matrix T B (gridModulus ϑ).ResidueRing),
      AreMatched ⊤ ε (c.char ϑ)
        (fun x : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing ↦
          Ψ (c.newTuple S x v'))
        (c.columnFourier ψ Ψ' S v'))
    {J : Type} {C : ℂ}
    {L : J → Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing → ℂ}
    {L' : J → Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing → ℂ}
    (h_law : ∀ i : J, SquareLaw (c.char ϑ) ε C (L i) (L' i))
    {f : EdgeTuple ϑ → Matrix T B (gridModulus ϑ).ResidueRing → J} (hf : DependsOn f w) :
    ∑ S ∈ tuplesOn ϑ (c.oldEdges w), Ψ' S *
        ∑ v' : Matrix T B (gridModulus ϑ).ResidueRing,
          ψ (v' * c.oldColumn S).trace * L' (f S v') (c.oldMatrix S) =
      C * ∑ S ∈ tuplesOn ϑ (c.newEdges w), Ψ S * L (f S (c.newRow S)) (c.newMatrix S) := by
  rw [hc.sum_tuplesOn_oldEdges, hc.sum_tuplesOn_newEdges, mul_sum]
  refine sum_congr rfl fun S _ ↦ ?_
  -- The index does not see the matrices on the sides of the square.
  have h_old (y : Matrix (D.NodeIndex c.fst ⊕ B) (D.NodeIndex c.low) (gridModulus ϑ).ResidueRing)
      (v : Matrix B T (gridModulus ϑ).ResidueRing) : f (c.oldTuple S y v) = f S :=
    hf fun _ ↦ hc.oldTuple_apply_of_mem y v
  have h_new (x : Matrix (D.NodeIndex c.high) (D.NodeIndex c.fst ⊕ B) (gridModulus ϑ).ResidueRing)
      (v' : Matrix T B (gridModulus ϑ).ResidueRing) : f (c.newTuple S x v') = f S :=
    hf fun _ ↦ hc.newTuple_apply_of_mem x v'
  calc _
    _ = ∑ v', ∑ y, c.columnFourier ψ Ψ' S v' y * L' (f S v') y := by
      simp only [h_old, hc.oldMatrix_oldTuple, oldColumn_oldTuple, columnFourier, mul_sum, sum_mul]
      rw [sum_comm_cycle]
      simp only [mul_assoc, mul_left_comm (Ψ' _)]
    _ = ∑ v', C * ∑ x, Ψ (c.newTuple S x v') * L (f S v') x :=
      sum_congr rfl fun v' _ ↦ (h_law (f S v')).sum_eq_of_areMatched _ _ (h_match S v')
    _ = _ := by simp only [h_new, newRow_newTuple, hc.newMatrix_newTuple, mul_sum]

end IsTurn

end Corner

end GridMove

/-! ## The exchange on a square of the grids -/

section GridSquare

open Fintype Exchange

variable {P : Parameters} {D : Data P} {a b : ℕ}

variable (D) in
/-- The ratio of the turn at `(i, j)`: the product over `1 ≤ s ≤ D.t` of the ratios of Hecke values
at `s` of the character `untwistedLiftChar (i + 1) * untwistedLiftChar (j + 1)` at the twist
`ϑ ^ (j + 1)`. -/
noncomputable def turnRatio (i j : ℕ) (ϑ : D.MFoldTwist) : ℝ :=
  D.lRatioProd (D.untwistedLiftChar (i + 1) * D.untwistedLiftChar (j + 1)) D.t (ϑ.pow (j + 1))

/-- The critical pair of a square: the character `ν = untwistedLiftChar (a + 1) * untwistedLiftChar
(b + 1)`, of weight `-(D.liftWeight (a + 1) + D.liftWeight (b + 1))`, with its tame part `tamePart`
and the integer `z = D.t`. In a critical pair (`D.CriticalPair`) minus the weight is at least `z`
and at most `4 * D.b` at every infinite place. -/
noncomputable def squarePair (ha : a < D.m) (hb : b < D.m) : D.CriticalPair where
  character := D.untwistedLiftChar (a + 1) * D.untwistedLiftChar (b + 1)
  negWeight := D.liftWeight (b + 1) + D.liftWeight (a + 1)
  tamePart := D.chiMLocal ^ (a + 1 + (b + 1) : ℤ)
  z := D.t
  hasWeight := by
    -- the weights add, and the tame parts multiply
    simpa [← zpow_add] using! (D.untwistedLiftChar_hasWeight a.succ).mul
      (D.untwistedLiftChar_hasWeight b.succ)
  tamePart_eq_one := by simp_all
  z_mem := by grind
  le_negWeight := by grind [Pi.add_apply]
  negWeight_le v := by
    simp only [Pi.add_apply]
    grind [liftWeight_le_two_mul_b]

/-- The pair `squarePair ha hb` of the square `(a, b)` is ramified: its tame part is nontrivial
exactly at the chosen places. -/
lemma isRamified_squarePair (ha : a < D.m) (hb : b < D.m) : (squarePair ha hb).IsRamified :=
  D.chiMLocal_zpow_ne_one_iff_isChosen (a + 1 + (b + 1)) (by omega) (by omega)

/-- For `i, j < D.m` the ratio `turnRatio i j` of a turn is the product of the ratios of Hecke
values of a ramified critical pair at the powers `ϑ ^ (j + 1)` of the twists. -/
lemma isRamifiedRatio_turnRatio {i j : ℕ} (hi : i < D.m) (hj : j < D.m) :
    D.IsRamifiedRatio (D.turnRatio i j) :=
  ⟨squarePair hi hj, ⟨j + 1, by omega, by omega⟩, isRamified_squarePair hi hj, fun _ ↦ rfl⟩

lemma isRamifiedRatio_turnRatio_of_mem (s : ℕ × ℕ)
    (hs : s ∈ Finset.range D.m ×ˢ Finset.range D.m) : D.IsRamifiedRatio (D.turnRatio s.1 s.2) :=
  isRamifiedRatio_turnRatio (by grind) (by grind)

/-- The two pairs of opposite corners of a square of the grid `z` have the same sum of ranks. -/
lemma card_gridIndex_square (z : Bool) (a b : ℕ) :
    card (D.GridIndex z a b ⊕ D.GridIndex z (a + 1) (b + 1)) =
      card (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) := by
  cases z <;> simp [card_gridIndex] <;> grind

/-- The character of the residue ring with given tame parts is multiplicative in the tame parts. -/
lemma charOfTamePart_gridModulus_mul {ϑ : D.MFoldTwist}
    (ψ ψ' : ∀ w : FinPlace D.E, MulChar (ResField w) ℂ) :
    (gridModulus ϑ).charOfTamePart (ψ * ψ') =
      (gridModulus ϑ).charOfTamePart ψ * (gridModulus ϑ).charOfTamePart ψ' := by
  ext
  apply finprod_mul_distrib <;> toFinite_tac

/-- The characters of the two edges at the node `(a, b)` of the grid `z` multiply to the character
with components `(squarePair ha hb).tamePart * ϑ.tamePart ^ n`, for `n = a + 1` if `z` and
`n = b + 1` otherwise. -/
lemma edgeChar_columnEdge_mul_rowEdge (z : Bool) (ha : a < D.m) (hb : b < D.m) (ϑ : D.MFoldTwist) :
    edgeChar ϑ (columnEdge z a b) * edgeChar ϑ (rowEdge z a b) =
      (gridModulus ϑ).charOfTamePart ((squarePair ha hb).tamePart * ϑ.tamePart ^
        ((if z then a else b) + 1)) := by
  rw [edgeChar, edgeChar, ← charOfTamePart_gridModulus_mul]
  congr 1
  -- One of the two tame parts carries a power of the twist, the other the trivial twist.
  have h_one : (1 : D.Twist).tamePart = 1 := rfl
  cases z <;> simp [squarePair, liftTamePart, TameChar.pow, h_one, zpow_add, mul_assoc, mul_comm,
    mul_left_comm]

/-- Let `a, b < D.m`, let `r` be the sum of the ranks of the corners `(a, b + 1)` and `(a + 1, b)`
of the grid `z`, and let `p`, `q` be index types with `card p + card q = r`. The character
`gridChar ϑ z a p` of the edges of the lifts times `gridChar ϑ (!z) b q`, that of the edges of the
transposed lifts, is `rankTwist` of the product `ν * ϑ.toAutChar ^ n` in the rank `r`. Here
`ν = (squarePair ha hb).character = D.untwistedLiftChar (a + 1) * D.untwistedLiftChar (b + 1)`, with
`D.untwistedLiftChar j` the untwisted character of the `j`-th lift, `ϑ.toAutChar` is the character
of the twist `ϑ`, and `n = a + 1` if `z`, `n = b + 1` otherwise. -/
lemma gridChar_mul_gridChar_eq_rankTwist (z : Bool) (ha : a < D.m) (hb : b < D.m) (ϑ : D.MFoldTwist)
    {p q : Type} [Fintype p] [Fintype q]
    (hpq : card p + card q = card (D.GridIndex z a (b + 1)) + card (D.GridIndex z (a + 1) b)) :
    gridChar ϑ z a p * gridChar ϑ (!z) b q =
      rankTwist ((squarePair ha hb).character * ϑ.toAutChar ^ ((if z then a else b) + 1))
        (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) := by
  -- The sum of the two ranks is even, so the rounded halves of `card p` and `card q` add up.
  have h_half : (card p + (!z).toNat) / 2 + (card q + z.toNat) / 2 =
      card (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) / 2 := by
    cases z <;> simp_all [card_gridIndex] <;> grind
  rw [rankTwist, ← h_half]
  cases z <;> simp only [squarePair, gridChar, liftChar, TameChar.pow, TameChar.one, Bool.cond_true,
    Bool.cond_false, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false, ite_true,
    ite_false, Bool.false_eq_true, pow_add] <;> ac_rfl

/-- For the sum `W` of the corners `(a, b + 1)` and `(a + 1, b)` of the square, half the rank of
`W` minus its number of negative signs is at most `(squarePair ha hb).negWeight τ`, minus the
weight of the pair of the square at the infinite place `τ`. The signs are `D.gridSigns z 0`, those
of the nodes of the grid `z` (offset `0`). -/
lemma card_gridIndex_square_le (z : Bool) (ha : a < D.m) (hb : b < D.m)
    (τ : NumberField.InfinitePlace D.E) :
    (card (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) : ℤ) ≤
      2 * ((squarePair ha hb).negWeight τ : ℤ) +
        2 * (negCount (Sum.elim (D.gridSigns z 0 a (b + 1)) (D.gridSigns z 0 (a + 1) b)) : ℤ) := by
  -- both ranks are at most `2 * D.n D.m ≤ 2 * D.halfGap`, and both weights are at least `D.halfGap`
  have h_n : D.n D.m ≤ D.halfGap := D.nat_le_of_hasLogBound
  simp only [squarePair, Fintype.card_sum, Pi.add_apply, negCount_sumElim, Nat.cast_add]
  grw [card_gridIndex_le, card_gridIndex_le, h_n] <;> grind

/-- Crossing the square `(a, b)` of the grid `z`, for `a, b < m`: there are a constant `κ`, a
bijection `σ` between the indices of the two pairs of opposite corners and numbers `c ϑ ≠ 0` with
the following property. Let `f` be a form at the node `(a, b + 1)` and `l` a functional on the forms
at the node `(a + 1, b)`. Then the values of `l` at the images of `f` through `(a + 1, b + 1)`, by a
lift and a transposed lift, each by a matrix modulo `gridModulus ϑ`, and through `(a, b)`, by a
transposed lift and a lift, satisfy the square law with constant `κ / c ϑ`; the constant `κ` may be
`0`. The character of the law is the inverse of the product of the characters `edgeChar` of the
edges from `(a, b)` to `(a, b + 1)` (`columnEdge`) and to `(a + 1, b)` (`rowEdge`). The numbers
`c ϑ` have absolute value `turnRatio` up to a constant and a power of the norm of the modulus of
`ϑ`. -/
lemma exists_squareLaw_grid_hasAbsUpToNormPower (z : Bool) (ha : a < D.m) (hb : b < D.m) :
    ∃ (κ : ℂ) (σ : D.GridIndex z a b ⊕ D.GridIndex z (a + 1) (b + 1) ≃
        D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) (c : D.MFoldTwist → ℂˣ),
      D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
        (if z then D.turnRatio b a else D.turnRatio a b) ∧
      ∀ (ϑ : D.MFoldTwist) (f : D.GridForm z a (b + 1)) (l : D.GridForm z (a + 1) b →ₗ[ℂ] ℂ),
        SquareLaw (edgeChar ϑ (columnEdge z a b) * edgeChar ϑ (rowEdge z a b))⁻¹ σ (κ / c ϑ)
          -- the lift of `f`, then the transposed lift
          (fun x : Matrix (D.GridIndex z (a + 1) (b + 1))
              (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) (gridModulus ϑ).ResidueRing ↦
            l (transposedMove x.toCols₂ (liftMove x.toCols₁ f)))
          -- the transposed lift of `f`, then the lift
          (fun y : Matrix (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b)
              (D.GridIndex z a b) (gridModulus ϑ).ResidueRing ↦
            l (liftMove y.toRows₂ (transposedMove y.toRows₁ f))) := by
  -- The character of the square is `(ν * ϑ.toAutChar ^ n)⁻¹` for `ν = pair.character`, with
  -- `n = a + 1` if `z` and `n = b + 1` otherwise. It is tame, and a function `c` of `ϑ` with
  -- `‖c ϑ‖ ^ 2` a constant times `lValueProd` of this character has the absolute value
  -- `turnRatio` up to a constant and a power of the norm.
  let pair : D.CriticalPair := squarePair ha hb
  let n : D.LiftIndex := ⟨(if z then a else b) + 1, by grind⟩
  have h_signs : negCount (Sum.elim (D.gridSigns z 0 a (b + 1)) (D.gridSigns z 0 (a + 1) b)) =
      negCount (D.gridSigns z 0 (a + 1) (b + 1)) + negCount (D.gridSigns z 0 a b) := by
    simp [negCount_gridSigns]
  have h_rank : card (D.GridIndex z (a + 1) (b + 1)) = card (D.GridIndex z a b) + 2 * D.t := by
    cases z <;> simp [card_gridIndex] <;> grind
  have h_ratio : (fun ϑ : D.MFoldTwist ↦ D.lRatioProd pair.character pair.z (ϑ.pow n)) =
      if z then D.turnRatio b a else D.turnRatio a b := by
    funext ϑ
    cases z <;> simp [pair, n, squarePair, turnRatio, mul_comm (D.untwistedLiftChar (b + 1))]
  have h_card := card_gridIndex_square (D := D) z a b
  -- On the two kept corners together at least two more signs are positive than negative.
  have h_few_neg :
      2 * negCount (Sum.elim (D.gridSigns z 0 a (b + 1)) (D.gridSigns z 0 (a + 1) b)) + 2 ≤
        card (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) := by
    cases z <;> simp [card_gridIndex, negCount_gridSigns] <;> grind
  have h_chars (ϑ : D.MFoldTwist) {p q : Type} [Fintype p] [Fintype q]
      (hpq : card p + card q = card (D.GridIndex z a (b + 1)) + card (D.GridIndex z (a + 1) b)) :
      gridChar ϑ z a p * gridChar ϑ (!z) b q =
        rankTwist (pair.character * ϑ.toAutChar ^ n.val)⁻¹⁻¹
          (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) := by
    simpa only [inv_inv] using gridChar_mul_gridChar_eq_rankTwist z ha hb ϑ hpq
  have h_square : ∃ (C : ℝ) (κ : ℂ), ∀ ϑ : D.MFoldTwist, ∃ c ≠ (0 : ℂ),
      ‖c‖ ^ 2 = C * lValueProd (D.twistModulus ϑ D.natB).places
        (pair.character * ϑ.toAutChar ^ n.val)⁻¹ D.t ∧
      ∀ (f : D.GridForm z a (b + 1)) (l : D.GridForm z (a + 1) b →ₗ[ℂ] ℂ),
        SquareLaw ((gridModulus ϑ).charOfTamePart (pair.tamePart * ϑ.tamePart ^ n.val))⁻¹
          (equivOfCardEq h_card)
          (κ / c) (fun x ↦ l (transposedMove x.toCols₂ (liftMove x.toCols₁ f)))
          (fun y ↦ l (liftMove y.toRows₂ (transposedMove y.toRows₁ f))) :=
    one_square_identity_of_isEdgeFamily (D.gridSpace 0 z a b) (D.gridSpace 0 z (a + 1) (b + 1))
      (D.gridSpace 0 z a (b + 1))
      (D.gridSpace 0 z (a + 1) b) (isEdgeFamily_grid_succ_right id ha hb)
      (isEdgeFamily_grid_succ_left id ha hb) (isEdgeFamily_grid_succ_left id ha hb.le)
      (isEdgeFamily_grid_succ_right id ha.le hb) (equivOfCardEq h_card) h_signs D.t h_rank h_few_neg
      (card_gridIndex_square_le z ha hb)
      (pair.isTameFor_inv_mul_pow (isRamified_squarePair ha hb) D.natB n) h_chars
  choose C κ c hc_ne hc_norm h_law using h_square
  refine ⟨κ, equivOfCardEq h_card, fun ϑ ↦ Units.mk0 (c ϑ) (hc_ne ϑ), ?_, fun ϑ f l ↦ ?_⟩
  · simpa only [h_ratio, Units.val_mk0] using
      pair.hasAbsUpToNormPower_of_norm_sq_eq_lValueProd D.natB n hc_norm
  · rw [edgeChar_columnEdge_mul_rowEdge z ha hb ϑ]
    exact h_law ϑ f l

end GridSquare

/-!
## Transfers of periods, and turns off the diagonal

The property that one turn provides, `New.Data.TransfersPeriods`, passes to composites of turns.
-/

section RowLadder

open Fintype Finset Matrix Function Exchange

variable {P : Parameters} {D : Data P} {a b : ℕ}

/-- The property of turns and their composites, for any two paths `Γ'`, `Γ`: path data `Ψ'` on `Γ'`
give path data `Ψ` on `Γ` with the bound for the number of roots of unity in a value multiplied by
`k`, and if `Ψ` is proportional to `Ξ`, then `Ψ'` is proportional to `Ξ / c`. A triple
(`D.PeriodTriple`) is a twist and two forms, one at the start of each half of a path; `Ψ` is
proportional to `Ξ` (`IsProportional`) if at each real point its period, a function of the
triples, is a multiple of `Ξ` by a number independent of the triple. -/
def TransfersPeriods (Γ' Γ : TwoGridPath D.m) (k : D.MFoldTwist → ℕ) (c : D.MFoldTwist → ℂˣ) :
    Prop :=
  ∀ (N : D.MFoldTwist → ℕ) (Ψ' : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ),
    (∀ ϑ : D.MFoldTwist, IsPathDatum (N ϑ) Γ'.edges (Ψ' ϑ)) →
    ∃ Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ,
      (∀ ϑ : D.MFoldTwist, IsPathDatum (k ϑ * N ϑ) Γ.edges (Ψ ϑ)) ∧
      ∀ Ξ : D.PeriodTriple → ℂ, IsProportional Γ Ψ Ξ →
        IsProportional Γ' Ψ' fun x : D.PeriodTriple ↦ Ξ x / c x.1

lemma TransfersPeriods.refl (Γ : TwoGridPath D.m) : TransfersPeriods Γ Γ 1 1 :=
  fun N Ψ hΨ ↦ ⟨Ψ, by simpa using hΨ, by simp⟩

/-- A pair of paths that transfers periods with bound `k` also transfers them with every larger
bound `k'`. -/
lemma TransfersPeriods.mono {Γ' Γ : TwoGridPath D.m} {k k' : D.MFoldTwist → ℕ}
    {c : D.MFoldTwist → ℂˣ} (h_transfer : TransfersPeriods Γ' Γ k c) (hk : k ≤ k') :
    TransfersPeriods Γ' Γ k' c := by
  refine fun N Ψ' hΨ' ↦ (h_transfer N Ψ' hΨ').imp fun Ψ ⟨hΨ, h_prop⟩ ↦ ⟨fun ϑ ↦ ?_, h_prop⟩
  exact (hΨ ϑ).mono (Nat.mul_le_mul_right (N ϑ) (hk ϑ))

/-- Period transfers compose: the bounds and the constants multiply. -/
lemma TransfersPeriods.trans {Γ₁ Γ₂ Γ₃ : TwoGridPath D.m} {k k' : D.MFoldTwist → ℕ}
    {c c' : D.MFoldTwist → ℂˣ} (h₁₂ : TransfersPeriods Γ₁ Γ₂ k c)
    (h₂₃ : TransfersPeriods Γ₂ Γ₃ k' c') :
    TransfersPeriods Γ₁ Γ₃ (k * k') (c * c') := by
  intro N Ψ₁ hΨ₁
  obtain ⟨Ψ₂, hΨ₂, h_prop₁₂⟩ := h₁₂ N Ψ₁ hΨ₁
  obtain ⟨Ψ₃, hΨ₃, h_prop₂₃⟩ := h₂₃ (fun ϑ : D.MFoldTwist ↦ k ϑ * N ϑ) Ψ₂ hΨ₂
  refine ⟨Ψ₃, by simpa only [Pi.mul_apply, mul_assoc, mul_left_comm] using hΨ₃, fun Ξ hΞ ↦ ?_⟩
  simpa only [Pi.mul_apply, Units.val_mul, div_div, mul_comm] using h_prop₁₂ _ (h_prop₂₃ Ξ hΞ)

variable (D) in
/-- The corner at the node `(a, b)` of the grid `z`, for a turn off the diagonal. -/
abbrev innerCorner (z : Bool) (a b : ℕ) : D.Corner (D.GridIndex z (a + 1) b) Empty where
  low := (z, a, b)
  lowExt := (z, a, b)
  fst := (z, a, b + 1)
  snd := (z, a + 1, b)
  high := (z, a + 1, b + 1)
  highExt := (z, a + 1, b + 1)
  sndEquiv := .refl _
  lowEquiv := .sumEmpty _ Empty
  highEquiv := .sumEmpty _ Empty

/-- Let `a < b < m`, let `z` select one of the two grids and let `ϑ` be any `m`-fold twist. If the
edges `w` avoid the node `(z, a, b)` and do not end at `(z, a + 1, b + 1)`, then the corner at
`(z, a, b)` is a turn of a path whose other edges are `w`: it meets the conditions
(`Corner.IsTurn`) for replacing the two sides of the square at `(z, a, b)` by the two sides at
`(z, a + 1, b + 1)`. -/
lemma isTurn_innerCorner {z : Bool} (hab : a < b) (hb : b < D.m) (ϑ : D.MFoldTwist)
    {w : Finset (GridNode × GridNode)}
    (hw : ∀ e ∈ w, e.1 ≠ (z, a, b) ∧ e.2 ≠ (z, a, b) ∧ e.2 ≠ (z, a + 1, b + 1)) :
    (D.innerCorner z a b).IsTurn ϑ w where
  fst_ne_snd := by simp
  ne_low_and_ne_lowExt := by simp
  endpoints_notMem e he := by simpa using hw e he
  vertical := by cases z <;> simp [IsVerticalEdge]
  edgeChar_fst := by simp [edgeChar, IsVerticalEdge]
  edgeChar_snd := by simp [edgeChar, IsVerticalEdge]
  apply_highExt g _ := (blockInlGL_sumEmpty _).symm
  exists_eq_low g hg k := by
    -- An admissible family is free at `(z, a, b)`, which is neither an end nor on the diagonal.
    refine ⟨update g (z, a, b) k, ⟨fun z' ↦ ?_, fun j ↦ ?_⟩, update_self ..,
      (update_self ..).trans (blockInlGL_sumEmpty k).symm, fun q hq _ ↦ update_of_ne hq ..⟩
    · rw [update_of_ne (by grind)]
      exact hg.1 z'
    · rw [update_of_ne (by grind), update_of_ne (by grind), hg.2 j]

private lemma edges_eq_union_halves (Γ : TwoGridPath D.m) (z : Bool) :
    Γ.edges = (Γ.half z).edges z ∪ (Γ.half !z).edges !z := by
  cases z <;> simp [TwoGridPath.edges, union_comm]

/-- If the half in the grid `z` of `Γ'` is `q`, the two sides through `(a, b)`, then `r`, the edges
of `Γ'` are these two sides and the edges of `q`, `r` and the other half. -/
lemma edges_eq_oldEdges_innerCorner {z : Bool} (Γ' : TwoGridPath D.m)
    (q : GridPath 0 D.m a (b + 1)) (r : GridPath (a + 1) b Γ'.diagonalIndex Γ'.diagonalIndex)
    (hΓ' : Γ'.half z = q.down.right.append r) :
    Γ'.edges = (D.innerCorner z a b).oldEdges (q.edges z ∪ r.edges z ∪ (Γ'.half !z).edges !z) := by
  rw [edges_eq_union_halves Γ' z, hΓ']
  simp [GridPath.edges_append, GridPath.edges]

/-- If the half in the grid `z` is replaced by `q`, the two sides through `(a + 1, b + 1)`, then
`r`, the edges are these two sides and the edges of `q`, `r` and the other half. -/
lemma edges_update_eq_newEdges_innerCorner (z : Bool) (Γ' : TwoGridPath D.m)
    (q : GridPath 0 D.m a (b + 1)) (r : GridPath (a + 1) b Γ'.diagonalIndex Γ'.diagonalIndex) :
    (⟨Γ'.diagonalIndex, update Γ'.half z (q.right.down.append r)⟩ : TwoGridPath D.m).edges =
      (D.innerCorner z a b).newEdges (q.edges z ∪ r.edges z ∪ (Γ'.half !z).edges !z) := by
  rw [edges_eq_union_halves _ z]
  simp [GridPath.edges_append, GridPath.edges]

/-- The exchange at the corner `(a, b)` of the grid `z`, for one twist `ϑ`. Let `q` be a grid path
from `(0, D.m)` to `(a, b + 1)` and `r` one from `(a + 1, b)` to a diagonal node `(k, k)`. Let the
corner be a turn of a path whose other edges `w` contain those of `q` and `r`, let `Ψ` match the
column Fourier transform of `Ψ'`, and let the square law hold with constant `C`. Carry a form `F`
at `(0, D.m)` along `q`, two sides of the square and `r`, and read it at `(k, k)` by functionals
`l S` that depend on the tuple `S` only through its matrices on `w`. Then the sum against `Ψ'`
through `(a, b)` is `C` times the sum against `Ψ` through `(a + 1, b + 1)`. -/
lemma sum_formMap_eq_of_squareLaw {z : Bool} {ϑ : D.MFoldTwist} {w : Finset (GridNode × GridNode)}
    (h_turn : (D.innerCorner z a b).IsTurn ϑ w) {k : ℕ} {q : GridPath 0 D.m a (b + 1)}
    {r : GridPath (a + 1) b k k} (hq : q.edges z ⊆ w) (hr : r.edges z ⊆ w)
    {σ : D.GridIndex z a b ⊕ D.GridIndex z (a + 1) (b + 1) ≃
      D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b} {Ψ Ψ' : EdgeTuple ϑ → ℂ} {C : ℂ}
    (h_match : ∀ (S : EdgeTuple ϑ)
      (v' : Matrix Empty (D.GridIndex z (a + 1) b) (gridModulus ϑ).ResidueRing),
      AreMatched ⊤ σ ((D.innerCorner z a b).char ϑ)
        (fun x : Matrix (D.GridIndex z (a + 1) (b + 1))
            (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) (gridModulus ϑ).ResidueRing ↦
          Ψ ((D.innerCorner z a b).newTuple S x v'))
        ((D.innerCorner z a b).columnFourier 1 Ψ' S v'))
    (h_law : ∀ (f : D.GridForm z a (b + 1)) (l : D.GridForm z (a + 1) b →ₗ[ℂ] ℂ),
      SquareLaw ((D.innerCorner z a b).char ϑ) σ C
        (fun x : Matrix (D.GridIndex z (a + 1) (b + 1))
            (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) (gridModulus ϑ).ResidueRing ↦
          l (transposedMove x.toCols₂ (liftMove x.toCols₁ f)))
        (fun y : Matrix (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b)
            (D.GridIndex z a b) (gridModulus ϑ).ResidueRing ↦
          l (liftMove y.toRows₂ (transposedMove y.toRows₁ f))))
    (F : D.GridForm z 0 D.m) {l : EdgeTuple ϑ → D.GridForm z k k →ₗ[ℂ] ℂ} (hl : DependsOn l w) :
    ∑ S ∈ tuplesOn ϑ ((D.innerCorner z a b).oldEdges w),
        Ψ' S * l S ((q.down.right.append r).formMap S z F) =
      C * ∑ S ∈ tuplesOn ϑ ((D.innerCorner z a b).newEdges w),
        Ψ S * l S ((q.right.down.append r).formMap S z F) := by
  let K : D.Corner (D.GridIndex z (a + 1) b) Empty := D.innerCorner z a b
  -- The form at `(a, b + 1)` and the functional at `(a + 1, b)` depend on the preserved edges.
  have h_dep : DependsOn
      (fun (S : EdgeTuple ϑ) (_ : Matrix Empty (D.GridIndex z (a + 1) b)
        (gridModulus ϑ).ResidueRing) ↦
        (q.formMap S z F, l S ∘ₗ r.formMap S z)) (w : Set (GridNode × GridNode)) := fun S S' h ↦ by
    simp only [q.formMap_congr (z := z) fun e he ↦ h e (hq he),
      r.formMap_congr (z := z) fun e he ↦ h e (hr he), hl h]
  -- The line is empty, so the sum over the rows has one term.
  have h_square : ∑ S ∈ tuplesOn ϑ (K.oldEdges w), Ψ' S * l S (r.formMap S z (liftMove
        (K.oldMatrix S).toRows₂ (transposedMove (K.oldMatrix S).toRows₁ (q.formMap S z F)))) =
      C * ∑ S ∈ tuplesOn ϑ (K.newEdges w), Ψ S * l S (r.formMap S z (transposedMove
        (K.newMatrix S).toCols₂ (liftMove (K.newMatrix S).toCols₁ (q.formMap S z F)))) := by
    simpa [card_congr of.symm] using h_turn.sum_eq_of_squareLaw h_match
      (fun i : D.GridForm z a (b + 1) × (D.GridForm z (a + 1) b →ₗ[ℂ] ℂ) ↦ h_law i.1 i.2) h_dep
  -- The blocks of the matrices of the square are, by definition, the matrices on its sides.
  simp only [GridPath.formMap_append, GridPath.formMap, LinearMap.comp_apply]
  exact h_square

/-- Fix an off-diagonal corner `a < b < D.m` in half `z`. Every turn there transfers periods
with bound `1` and the same nonzero factor `c ϑ` for each twist `ϑ`. Up to a constant and a power
of the norm of its modulus, the absolute value of this factor is the Hecke ratio `turnRatio` at
`(a, b)` for the ordinary half and at `(b, a)` for the reflected half. -/
lemma exists_transfersPeriods_off_diagonal (z : Bool) (hab : a < b) (hb : b < D.m) :
    ∃ c : D.MFoldTwist → ℂˣ,
      D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
        (if z then D.turnRatio b a else D.turnRatio a b) ∧
      ∀ Γ' Γ : TwoGridPath D.m, Γ'.Turn (bif z then (b, a) else (a, b)) Γ →
        TransfersPeriods Γ' Γ 1 c := by
  -- The exchange on the square, applied to the form that arrives at it along `q`, shows that the
  -- period of `Ψ'` is `κ / c` times that of the turned datum `Ψ`, with a constant `κ`.
  obtain ⟨κ, σ, c, hc, h_law⟩ := exists_squareLaw_grid_hasAbsUpToNormPower z (hab.trans hb) hb
  refine ⟨c, hc, fun Γ' Γ h_step ↦ ?_⟩
  obtain ⟨q, r, hΓ', rfl⟩ := h_step.exists_corner (z := z) hab
  intro N Ψ' hΨ'
  let Γ : TwoGridPath D.m := ⟨Γ'.diagonalIndex, update Γ'.half z (q.right.down.append r)⟩
  let w : Finset (GridNode × GridNode) := q.edges z ∪ r.edges z ∪ (Γ'.half !z).edges !z
  let K : D.Corner (D.GridIndex z (a + 1) b) Empty := D.innerCorner z a b
  have h_old : Γ'.edges = K.oldEdges w := edges_eq_oldEdges_innerCorner Γ' q r hΓ'
  have h_new : Γ.edges = K.newEdges w := edges_update_eq_newEdges_innerCorner z Γ' q r
  have h_apart : ∀ e ∈ w, e.1 ≠ (z, a, b) ∧ e.2 ≠ (z, a, b) ∧ e.2 ≠ (z, a + 1, b + 1) := by
    rintro ⟨u, v⟩ he
    grind [→ GridPath.eq_and_le_of_mem_edges, Prod.le_def]
  have h_turn (ϑ : D.MFoldTwist) : K.IsTurn ϑ w := isTurn_innerCorner hab hb ϑ h_apart
  have h_datum (ϑ : D.MFoldTwist) : ∃ Ψ : EdgeTuple ϑ → ℂ, IsPathDatum (1 * N ϑ) Γ.edges Ψ ∧
      ∀ (S : EdgeTuple ϑ) (v' : Matrix Empty (D.GridIndex z (a + 1) b) (gridModulus ϑ).ResidueRing),
        AreMatched ⊤ σ (K.char ϑ) (fun x ↦ Ψ (K.newTuple S x v'))
          (K.columnFourier 1 (Ψ' ϑ) S v') := by
    rw [h_old] at hΨ'
    -- The line is empty, so there is only one column matrix and the bound is unchanged.
    simpa [h_new, card_congr of.symm] using (h_turn ϑ).exists_isPathDatum (hΨ' ϑ) σ 1
  choose Ψ hΨ h_match using h_datum
  refine ⟨Ψ, hΨ, fun Ξ hΞ g ↦ ?_⟩
  -- The exchange for a form `F` that starts in the grid `z`, read by functionals `l S` that depend
  -- on the other half of the path only.
  have h_cross (ϑ : D.MFoldTwist) (F : D.GridForm z 0 D.m)
      (l : EdgeTuple ϑ → D.GridForm z Γ'.diagonalIndex Γ'.diagonalIndex →ₗ[ℂ] ℂ)
      (hl : DependsOn l ((Γ'.half !z).edges !z)) :
      ∑ S ∈ tuplesOn ϑ Γ'.edges, Ψ' ϑ S * l S ((q.down.right.append r).formMap S z F) =
      κ / c ϑ * ∑ S ∈ tuplesOn ϑ Γ.edges, Ψ ϑ S * l S ((q.right.down.append r).formMap S z F) := by
    rw [h_old, h_new]
    exact sum_formMap_eq_of_squareLaw (h_turn ϑ) (by grind) (by grind) (h_match ϑ) (h_law ϑ) F
      (hl.mono (by grind))
  have h_period : ∀ x : D.PeriodTriple, gridPeriod Γ' Ψ' g x = κ / c x.1 * gridPeriod Γ Ψ g x := by
    rintro ⟨ϑ, F₀, F₁⟩
    -- The form that starts in the grid `z` crosses the square, the other half gives the functional.
    cases z
    · simpa [gridPeriod, hΓ', Γ] using h_cross ϑ F₀
        (fun S ↦ (diagonalPeriodForm ϑ Γ'.diagonalIndex_le g).flip
          ((Γ'.half true).formMap S true F₁))
        fun S S' h ↦ by simp only [(Γ'.half true).formMap_congr (z := true) h]
    · simpa [gridPeriod, hΓ', Γ] using h_cross ϑ F₁
        (fun S ↦ diagonalPeriodForm ϑ Γ'.diagonalIndex_le g ((Γ'.half false).formMap S false F₀))
        fun S S' h ↦ by simp only [(Γ'.half false).formMap_congr (z := false) h]
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, ∀ x : D.PeriodTriple, gridPeriod Γ Ψ g x = β * Ξ x := hΞ g
  exact ⟨κ * β, fun x ↦ by simp [h_period, hβ, field]⟩

end RowLadder

end New.Data

end
end
end

section
/-!
# Turns on the diagonal, and the transfer of periods from the first path to the last

A turn on the diagonal replaces the node `(j, j)` of a path through the two grids by
`(j + 1, j + 1)`. A seesaw moves the period to the space `S = Ỹ^(j+1)_j = Y^(j+1)_j` common to both
paths, where the line contributes a theta kernel. There the line is reversed and the two maps are
exchanged, and a second seesaw moves the period on. Together with the turns off the diagonal this
transfers the periods from the first path to the last.

## Main definitions and results

* `New.Data.columnPeriod`, `New.Data.rowPeriod`: the integrals over the group of `S`.
* `New.Data.isProportional_of_columnPeriod`, `New.Data.IsProportional.exists_rowPeriod_eq_mul`: the
  seesaws.
* `New.Data.exists_columnLineKernel_eq`: reversing the line.
* `New.Data.exists_transfersPeriods_of_turn`: one turn, with the absolute value of its constant.
* `New.Data.exists_transfersPeriods_first_last`: the `m ^ 2` turns composed.

Notions from other files:
* `D.gridSpace 0 false a b` is the space `Y^a_b` and `D.gridSpace 0 true a b` is `Ỹ^b_a`; their
  bases are indexed by `D.GridIndex`.
* `modKernel S T a b 𝔪 Ψ p` is the theta kernel of the pair `(S, T)` with characters `a`, `b` of
  `[U(1)]`, for a function `Ψ` on matrices modulo `𝔪` and a polynomial `p`. On a space of rank `k`
  the character `a` gives the splitting character `New.AutChar.spaceChar`, the base change of `a`
  times `υ ^ (-k)`.
* `D.GridForm false a b` holds the conjugate forms on `Y^a_b`, and `D.GridForm true a b` the forms
  on `Ỹ^b_a`. In sums over tuples of matrices, one for each edge, the letter `S` names the tuple.
* `IsProportional Γ Ψ Ξ`, written `Ψ ∝ Ξ`: the periods of `Ψ` on the path `Γ` are multiples of `Ξ`
  by numbers that depend neither on the twist nor on the forms.
* `TransfersPeriods Γ' Γ k c`: path data `Ψ'` on `Γ'` give path data `Ψ` on `Γ`, with the bound for
  the number of roots of unity in a value multiplied by `k`, and `Ψ ∝ Ξ` implies `Ψ' ∝ Ξ / c`.
* `D.HasAbsUpToNormPower c f`: `‖c ϑ‖² = C (Nm Q)ᵏ (f ϑ)²`, with `Q` the modulus of the twist `ϑ`
  and with `C`, `k` independent of `ϑ`.
-/

@[expose] public section

noncomputable section

namespace New.Data

open MeasureTheory Fintype Function Exchange Finset Space Matrix Submodule

section Subdiagonal

variable {P : Parameters} (D : Data P) (j : ℕ)

/-- The renumbering of the bases that identifies `Ỹ^(j+1)_j` with `Y^(j+1)_j`. -/
def subdiagEquiv : D.GridIndex true j (j + 1) ≃ D.GridIndex false (j + 1) j :=
  (gridSpace_subdiag (D := D) j).choose

/-- The renumbering `subdiagEquiv` carries the signs of `Ỹ^(j+1)_j` to those of `Y^(j+1)_j`. -/
lemma gridSigns_subdiagEquiv :
    D.gridSigns false 0 (j + 1) j ∘ (D.subdiagEquiv j).symm.symm = D.gridSigns true 0 j (j + 1) :=
  (gridSpace_subdiag (D := D) j).choose_spec.choose

/-- The space `Ỹ^(j+1)_j` is the space `Y^(j+1)_j` with its basis renumbered by `subdiagEquiv`. -/
lemma gridSpace_subdiagEquiv : D.gridSpace 0 true j (j + 1) =
    (D.gridSpace 0 false (j + 1) j).reindex (D.subdiagEquiv j).symm (D.gridSigns_subdiagEquiv j) :=
  (gridSpace_subdiag (D := D) j).choose_spec.choose_spec

/-- The identification of the group of `Ỹ^(j+1)_j` with that of `Y^(j+1)_j`. -/
def subdiagMap :
    C(New.G D.E (D.gridSigns true 0 j (j + 1)), New.G D.E (D.gridSigns false 0 (j + 1) j)) where
  toFun := (G.reindex (D.subdiagEquiv j).symm (D.gridSigns_subdiagEquiv j)).symm
  continuous_toFun := G.continuous_reindex _ (by simp [← D.gridSigns_subdiagEquiv j, comp_def])

/-- The map `subdiagMap` is a right inverse of the renumbering of the group of `Y^(j+1)_j`. -/
lemma reindex_subdiagMap (g : New.G D.E (D.gridSigns true 0 j (j + 1))) :
    G.reindex (D.subdiagEquiv j).symm (D.gridSigns_subdiagEquiv j) (D.subdiagMap j g) = g :=
  (G.reindex (D.subdiagEquiv j).symm (D.gridSigns_subdiagEquiv j)).apply_symm_apply g

/-- The identification of the groups of `Ỹ^(j+1)_j` and `Y^(j+1)_j` preserves heights. -/
lemma height_subdiagMap (g : New.G D.E (D.gridSigns true 0 j (j + 1))) :
    (D.gridSpace 0 false (j + 1) j).height (D.subdiagMap j g) =
      (D.gridSpace 0 true j (j + 1)).height g := by
  rw [D.gridSpace_subdiagEquiv j, ← Space.height_reindex _ (D.gridSigns_subdiagEquiv j),
    reindex_subdiagMap]

/-- A function of moderate growth on the group of `S = Y^(j+1)_j`, as a weight for periods of a
form on `Ỹ^(j+1)_j` against a form on `Y^(j+1)_j`. -/
def subdiagWeight (θ : C(New.G D.E (D.gridSigns false 0 (j + 1) j), ℂ))
    (hθ : (D.gridSpace 0 false (j + 1) j).IsModerate θ) :
    ModerateWeight (D.gridSpace 0 true j (j + 1)) (D.gridSpace 0 false (j + 1) j) where
  weightFn := θ.comp (D.subdiagMap j)
  comparisonMap := D.subdiagMap j
  isModerate := by
    obtain ⟨C, N, h_bound⟩ := hθ
    exact ⟨C, N, fun g ↦ by simpa [height_subdiagMap] using h_bound (D.subdiagMap j g)⟩
  height_le := ⟨1, by simp [height_subdiagMap]⟩

end Subdiagonal

variable {P : Parameters} {D : Data P} {j : ℕ}

/-- The kernel `θ^j_(v,p)` of the pair from the line `E ẽ_j`, the summand that `Ỹ^j_j` has beyond
`Y^j_j`, to `S = Y^(j+1)_j`, for the point mass at the column `v` modulo `𝔪 = gridModulus ϑ` and
the polynomial `p`, at `u ^ j` on the line. Here `u` is the scalar `flipScalar` of `U(1)` of the
modulus `𝔪`, used to reverse a line. The character `gridChar ϑ false j` of `S` is that of a
horizontal edge at the index `j`, here the edge from `Y^j_j`. The line has the splitting character
`υ⁻¹`, given by the trivial character of `[U(1)]`; it completes the character of `Y^j_j` to that
of `Ỹ^j_j`. -/
def columnLineKernel (j : ℕ) (ϑ : D.MFoldTwist)
    (v : Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus ϑ).ResidueRing)
    (p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ) :
    ModerateWeight (D.gridSpace 0 true j (j + 1)) (D.gridSpace 0 false (j + 1) j) :=
  D.subdiagWeight j
    ⟨modKernel (signedSpace D.E fun _ : Unit ↦ (-1) ^ j) (D.gridSpace 0 false (j + 1) j) 1
      (gridChar ϑ false j (D.GridIndex false (j + 1) j)) (gridModulus ϑ) (Pi.single v 1) p
      (1, (gridModulus ϑ).flipScalar ^ j), by fun_prop [modKernel]⟩
    -- a theta kernel has moderate growth in each variable
    ((pairThetaKer ..).swap.isModerate ..)

/-- The weight function of `columnLineKernel` at a point `g` of the group of `Ỹ^(j+1)_j` is the
theta kernel from the line `E ẽ_j` to `S = Y^(j+1)_j`, for the point mass at the column `v` and the
polynomial `p`, taken at `flipScalar ^ j` on the line and at the image `subdiagMap g` of `g` in the
group of `S`. -/
lemma columnLineKernel_weightFn (j : ℕ) (ϑ : D.MFoldTwist)
    (v : Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus ϑ).ResidueRing)
    (p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ)
    (g : New.G D.E (D.gridSigns true 0 j (j + 1))) :
    (columnLineKernel j ϑ v p).weightFn g =
      modKernel (signedSpace D.E fun _ : Unit ↦ (-1) ^ j) (D.gridSpace 0 false (j + 1) j) 1
        (gridChar ϑ false j (D.GridIndex false (j + 1) j)) (gridModulus ϑ) (Pi.single v 1) p
        (1, (gridModulus ϑ).flipScalar ^ j) (D.subdiagMap j g) :=
  rfl

/-- The kernel `θ^(j+1)_(v',p)` of the pair from `S = Y^(j+1)_j` to the line `E ẽ_(j+1)`, the
summand that `Ỹ^(j+1)_(j+1)` has beyond `Y^(j+1)_(j+1)`, for the point mass at the row `v'` modulo
`𝔪 = gridModulus ϑ` and the polynomial `p`, at `u ^ (j + 1)` on the line, with `u = flipScalar`. The
character `gridChar ϑ true j` of `S` is that of a vertical edge at the index `j`, here the edge to
`Ỹ^(j+1)_(j+1)`. The line has the splitting character `υ`, given by `upsilonU1`; it completes the
character of `Y^(j+1)_(j+1)` to that of `Ỹ^(j+1)_(j+1)`. -/
def rowLineKernel (j : ℕ) (ϑ : D.MFoldTwist)
    (v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus ϑ).ResidueRing)
    (p : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ) :
    ModerateWeight (D.gridSpace 0 true j (j + 1)) (D.gridSpace 0 false (j + 1) j) :=
  D.subdiagWeight j
    ⟨fun x : New.G D.E (D.gridSigns false 0 (j + 1) j) ↦ modKernel (D.gridSpace 0 false (j + 1) j)
      (signedSpace D.E fun _ : Unit ↦ (-1) ^ (j + 1))
      (gridChar ϑ true j (D.GridIndex false (j + 1) j)) WeilData.upsilonU1 (gridModulus ϑ)
      (Pi.single v' 1) p x (1, (gridModulus ϑ).flipScalar ^ (j + 1)), by fun_prop [modKernel]⟩
    -- a theta kernel has moderate growth in each variable
    ((pairThetaKer ..).isModerate ..)

/-- The weight function of `rowLineKernel` at a point `g` of the group of `Ỹ^(j+1)_j` is the theta
kernel from `S = Y^(j+1)_j` to the line `E ẽ_(j+1)`, for the point mass at the row `v'` and the
polynomial `p`, taken at the image `subdiagMap g` of `g` in the group of `S` and at
`flipScalar ^ (j + 1)` on the line. -/
lemma rowLineKernel_weightFn (j : ℕ) (ϑ : D.MFoldTwist)
    (v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus ϑ).ResidueRing)
    (p : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ)
    (g : New.G D.E (D.gridSigns true 0 j (j + 1))) :
    (rowLineKernel j ϑ v' p).weightFn g =
      modKernel (D.gridSpace 0 false (j + 1) j) (signedSpace D.E fun _ : Unit ↦ (-1) ^ (j + 1))
        (gridChar ϑ true j (D.GridIndex false (j + 1) j)) WeilData.upsilonU1 (gridModulus ϑ)
        (Pi.single v' 1) p (D.subdiagMap j g) (1, (gridModulus ϑ).flipScalar ^ (j + 1)) :=
  rfl

/-- The corner for a turn at `(j, j)`, that is the six nodes at which such a turn changes a path. A
node `(z, a, b)` is `Y^a_b` for `z = false` and `Ỹ^b_a` for `z = true`. The turn removes the nodes
`low = Y^j_j` and `lowExt = Ỹ^j_j`, keeps `fst = Y^j_(j+1)` and `snd = Ỹ^(j+1)_j`, and adds
`high = Y^(j+1)_(j+1)` and `highExt = Ỹ^(j+1)_(j+1)`. The type `Unit` indexes the line by which
`lowExt` exceeds `low` and `highExt` exceeds `high`; the basis of `snd` is numbered as that of
`Y^(j+1)_j`. -/
abbrev diagonalCorner (D : Data P) (j : ℕ) : D.Corner (D.GridIndex false (j + 1) j) Unit where
  low := (false, j, j)
  lowExt := (true, j, j)
  fst := (false, j, j + 1)
  snd := (true, j, j + 1)
  high := (false, j + 1, j + 1)
  highExt := (true, j + 1, j + 1)
  sndEquiv := (D.subdiagEquiv j).symm
  lowEquiv := D.gridDiagEquiv j
  highEquiv := D.gridDiagEquiv (j + 1)

/-- The path that continues both halves `q` down to `(j, j)`. -/
abbrev downPath (q : Bool → GridPath 0 D.m j (j + 1)) : TwoGridPath D.m :=
  ⟨j, fun b : Bool ↦ (q b).down⟩

/-- The path that continues both halves `q` to `(j + 1, j + 1)`. -/
abbrev rightPath (q : Bool → GridPath 0 D.m j (j + 1)) : TwoGridPath D.m :=
  ⟨j + 1, fun b : Bool ↦ (q b).right⟩

/-- The path through `(j, j)` has the edges of the halves `q b` in the grids `b` (`false` for that
of the `Y`) and the old edges of the corner, from `Y^j_j` and `Ỹ^j_j` to the nodes that it keeps. -/
lemma edges_downPath (q : Bool → GridPath 0 D.m j (j + 1)) : (downPath q).edges =
    (D.diagonalCorner j).oldEdges ((q false).edges false ∪ (q true).edges true) := by
  simp [TwoGridPath.edges, GridPath.edges]

/-- The path through `(j + 1, j + 1)` has the edges of the halves `q b` in the grids `b` and the new
edges of the corner, from the nodes that it keeps to `Y^(j+1)_(j+1)` and `Ỹ^(j+1)_(j+1)`. -/
lemma edges_rightPath (q : Bool → GridPath 0 D.m j (j + 1)) : (rightPath q).edges =
    (D.diagonalCorner j).newEdges ((q false).edges false ∪ (q true).edges true) := by
  simp [TwoGridPath.edges, GridPath.edges]

/-- The integral `I^S(Ψ; z, p)` over the group of `S = Y^(j+1)_j`, on the path through `(j, j)`. The
halves `q b` are monotone paths from `(0, m)` to `(j, j + 1)`, and `formMap` carries a form along
one of them by the matrices of the edges, by a `liftMove` (lift) where the first index grows and a
`transposedMove` (transposed lift) where the second drops. The `periodPairing` integrates the kernel
of the line times the form that reaches `S` in the grid of the `Ỹ` times the conjugate form that
reaches it through `Y^j_j`, translated by the point `z` of the archimedean group `GInf`. This is
summed against `Ψ` over the tuples `S` in `tuplesOn`, one matrix for each edge. The triple `x` holds
the twist and the two initial forms, and `D.Φ` indexes the infinite places. -/
def columnPeriod (hj : j < D.m) (q : Bool → GridPath 0 D.m j (j + 1))
    (Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ) (z : GInf D.E (D.gridSigns false 0 (j + 1) j))
    (p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ) (x : D.PeriodTriple) : ℂ :=
  ∑ S ∈ tuplesOn x.1 (downPath q).edges, Ψ x.1 S *
    periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩)
      (columnLineKernel j x.1 ((D.diagonalCorner j).oldColumn S) p) z
        ((q true).formMap S true x.2.2)
      (liftMove ((D.diagonalCorner j).oldMatrix S).toRows₂
        (transposedMove ((D.diagonalCorner j).oldMatrix S).toRows₁
          ((q false).formMap S false x.2.1)))

/-- The integral `I^S(Ψ; z, p)` over the group of `S = Y^(j+1)_j`, on the path through
`(j + 1, j + 1)` that continues the halves `q b`, which are monotone paths from `(0, m)` to
`(j, j + 1)`: as `columnPeriod`, with the kernel to the line `E ẽ_(j+1)`, and with the conjugate
form reaching `S` by a lift to `Y^(j+1)_(j+1)` (`liftMove`) and a transposed lift
(`transposedMove`). -/
def rowPeriod (hj : j < D.m) (q : Bool → GridPath 0 D.m j (j + 1))
    (Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ) (z : GInf D.E (D.gridSigns false 0 (j + 1) j))
    (p : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ) (x : D.PeriodTriple) : ℂ :=
  ∑ S ∈ tuplesOn x.1 (rightPath q).edges, Ψ x.1 S *
    periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩)
      (rowLineKernel j x.1 ((D.diagonalCorner j).newRow S) p) z ((q true).formMap S true x.2.2)
      (transposedMove ((D.diagonalCorner j).newMatrix S).toCols₂
        (liftMove ((D.diagonalCorner j).newMatrix S).toCols₁
          ((q false).formMap S false x.2.1)))

/-- The characters `gridChar ϑ c l` of an edge of index `l`, vertical for `c = true` and horizontal
for `c = false`, agree at `Ỹ^(j+1)_j` and at `Y^(j+1)_j`, as the ranks are equal. -/
lemma gridChar_subdiag (ϑ : D.MFoldTwist) (c : Bool) (l : ℕ) :
    gridChar ϑ c l (D.GridIndex true j (j + 1)) = gridChar ϑ c l (D.GridIndex false (j + 1) j) := by
  simp only [gridChar, card_congr (D.subdiagEquiv j)]

/-- The kernel of the edge from `Ỹ^j_j = Y^j_j ⊕ E ẽ_j` to `Ỹ^(j+1)_j`, at the points `h ⊕ u ^ j`
(with `u = flipScalar`) and `g`, is the product of the kernel `columnLineKernel` of the line at `g`
and the kernel of the edge from `Y^j_j` to `S = Y^(j+1)_j` at `h` and `subdiagMap g`. The matrix `X`
of the edge is cut into columns, and the polynomial is a product of `A` in the variables of `Y^j_j`
and `B` in those of the line. -/
lemma modKernel_eq_columnLineKernel_mul (ϑ : D.MFoldTwist) (hj : j < D.m)
    (X : Matrix (D.GridIndex true j (j + 1)) (D.GridIndex true j j) (gridModulus ϑ).ResidueRing)
    (A : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × D.GridIndex false j j) ℂ)
    (B : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ)
    (h : New.G D.E (D.gridSigns false 0 j j)) (g : New.G D.E (D.gridSigns true 0 j (j + 1))) :
    modKernel (D.gridSpace 0 true j j) (D.gridSpace 0 true j (j + 1))
        (gridChar ϑ false j (D.GridIndex true j j))
        (gridChar ϑ false j (D.GridIndex true j (j + 1))) (gridModulus ϑ) (Pi.single X 1)
        (renameRowsCols (D.subdiagEquiv j).symm (D.gridDiagEquiv j ∘ .inl) A *
          renameRowsCols (D.subdiagEquiv j).symm (D.gridDiagEquiv j ∘ .inr) B)
        (.reindex (D.gridDiagEquiv j) (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj.le)
          (.sum (h, 1, (gridModulus ϑ).flipScalar ^ j))) g =
      (columnLineKernel j ϑ (X.submatrix (D.subdiagEquiv j).symm (D.gridDiagEquiv j)).toCols₂
          B).weightFn g *
        modKernel (D.gridSpace 0 false j j) (D.gridSpace 0 false (j + 1) j)
          (gridChar ϑ false j (D.GridIndex false j j))
          (gridChar ϑ false j (D.GridIndex false (j + 1) j)) (gridModulus ϑ)
          (Pi.single (X.submatrix (D.subdiagEquiv j).symm (D.gridDiagEquiv j)).toCols₁ 1) A h
          (D.subdiagMap j g) := by
  let ι : D.GridIndex false (j + 1) j ≃ D.GridIndex true j (j + 1) := (D.subdiagEquiv j).symm
  let e : D.GridIndex false j j ⊕ Unit ≃ D.GridIndex true j j := D.gridDiagEquiv j
  -- The characters agree by the parities of the ranks, as `D.t` is odd.
  have h_char : gridChar ϑ false j (D.GridIndex true j j) =
      gridChar ϑ false j (D.GridIndex false j j) * 1 := by
    obtain ⟨t, ht⟩ := D.t_odd
    have h_rank : (card (D.GridIndex true j j) + 1) / 2 =
        (card (D.GridIndex false j j) + 1) / 2 := by
      simp only [card_gridIndex, ht, Bool.toNat_true, Bool.toNat_false]
      grind
    simp [gridChar, h_rank]
  -- The point mass at `X` is the product of the point masses at its two blocks of columns.
  have h_datum := single_one_eq_mul_of_coordinates X (fun Y ↦ (Y.submatrix ι e).toCols₁)
    (fun Y ↦ (Y.submatrix ι e).toCols₂) (fun Y ↦ by
      simp only [← fromCols_ext_iff, fromCols_toCols]
      exact (Matrix.reindex ι.symm e.symm).injective.eq_iff (a := Y) (b := X))
  have h_poly : renameRowsCols ι (e ∘ .inl) A * renameRowsCols ι (e ∘ .inr) B =
      renameRowsCols ι e (renameRowsCols id .inl A * renameRowsCols id .inr B) := by
    simp [Prod.map_comp_map]
  rw [columnLineKernel_weightFn, eq_comm, mul_comm, ← modKernel_sum_left,
    ← modKernel_reindex e (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj.le) ι
      (D.gridSigns_subdiagEquiv j),
    reindex_subdiagMap, h_char, gridChar_subdiag, h_datum, h_poly, gridSpace_diag hj.le,
    D.gridSpace_subdiagEquiv j]

/-- The product of the kernel `rowLineKernel` of the line at `g` and the kernel of the edge from
`S = Y^(j+1)_j` to `Y^(j+1)_(j+1)` at `subdiagMap g` and `h` is the kernel of the edge from
`Ỹ^(j+1)_j` to `Ỹ^(j+1)_(j+1) = Y^(j+1)_(j+1) ⊕ E ẽ_(j+1)` at the points `g` and `h ⊕ u ^ (j + 1)`,
with `u = flipScalar`. -/
lemma rowLineKernel_mul_modKernel (ϑ : D.MFoldTwist) (hj : j < D.m)
    (X : Matrix (D.GridIndex true (j + 1) (j + 1)) (D.GridIndex true j (j + 1))
      (gridModulus ϑ).ResidueRing)
    (A : MvPolynomial (D.Φ × D.GridIndex false (j + 1) (j + 1) × D.GridIndex false (j + 1) j) ℂ)
    (B : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ)
    (g : New.G D.E (D.gridSigns true 0 j (j + 1)))
    (h : New.G D.E (D.gridSigns false 0 (j + 1) (j + 1))) :
    (rowLineKernel j ϑ (X.submatrix (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm).toRows₂
          B).weightFn g *
        modKernel (D.gridSpace 0 false (j + 1) j) (D.gridSpace 0 false (j + 1) (j + 1))
          (gridChar ϑ true j (D.GridIndex false (j + 1) j))
          (gridChar ϑ true j (D.GridIndex false (j + 1) (j + 1))) (gridModulus ϑ)
          (Pi.single (X.submatrix (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm).toRows₁ 1) A
          (D.subdiagMap j g) h =
      modKernel (D.gridSpace 0 true j (j + 1)) (D.gridSpace 0 true (j + 1) (j + 1))
        (gridChar ϑ true j (D.GridIndex true j (j + 1)))
        (gridChar ϑ true j (D.GridIndex true (j + 1) (j + 1))) (gridModulus ϑ) (Pi.single X 1)
        (renameRowsCols (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm
          (renameRowsCols .inl id A * renameRowsCols .inr id B)) g
        (.reindex (D.gridDiagEquiv (j + 1)) (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj)
          (.sum (h, 1, (gridModulus ϑ).flipScalar ^ (j + 1)))) := by
  let ι : D.GridIndex false (j + 1) j ≃ D.GridIndex true j (j + 1) := (D.subdiagEquiv j).symm
  let e : D.GridIndex false (j + 1) (j + 1) ⊕ Unit ≃ D.GridIndex true (j + 1) (j + 1) :=
    D.gridDiagEquiv (j + 1)
  -- The characters differ by `υ` by the parities of the ranks, as `D.t` is odd.
  have h_char : gridChar ϑ true j (D.GridIndex true (j + 1) (j + 1)) =
      gridChar ϑ true j (D.GridIndex false (j + 1) (j + 1)) * WeilData.upsilonU1 := by
    obtain ⟨t, ht⟩ := D.t_odd
    have h_rank : card (D.GridIndex true (j + 1) (j + 1)) / 2 =
        card (D.GridIndex false (j + 1) (j + 1)) / 2 + 1 := by
      simp only [card_gridIndex, ht, Bool.toNat_true, Bool.toNat_false]
      grind
    simp [gridChar, h_rank, mul_assoc, pow_succ]
  -- The point mass at `X` is the product of the point masses at its two blocks of rows.
  have h_datum := single_one_eq_mul_of_coordinates X (fun Y ↦ (Y.submatrix e ι).toRows₁)
    (fun Y ↦ (Y.submatrix e ι).toRows₂) (fun Y ↦ by
      simp only [← fromRows_ext_iff, fromRows_toRows]
      exact (Matrix.reindex e.symm ι.symm).injective.eq_iff (a := Y) (b := X))
  rw [rowLineKernel_weightFn, mul_comm, ← modKernel_sum_right,
    ← modKernel_reindex ι (D.gridSigns_subdiagEquiv j) e
      (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj),
    reindex_subdiagMap, h_char, gridChar_subdiag, h_datum, gridSpace_diag hj,
    D.gridSpace_subdiagEquiv j]

/-- Seesaw on the path through `(j, j)`: if all integrals `columnPeriod hj q Ψ z p` are multiples of
`Ξ` by constants that do not depend on the twist and the forms, then so are the periods of `Ψ` on
the path. -/
lemma isProportional_of_columnPeriod (hj : j < D.m) {q : Bool → GridPath 0 D.m j (j + 1)}
    {Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ} {Ξ : D.PeriodTriple → ℂ}
    (h_column : ∀ (z : GInf D.E (D.gridSigns false 0 (j + 1) j))
      (p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ),
      ∃ β : ℂ, ∀ x : D.PeriodTriple, columnPeriod hj q Ψ z p x = β * Ξ x) :
    IsProportional (downPath q) Ψ Ξ := by
  intro g
  -- By `seesaw_periods` it suffices that the polynomials whose kernel splits into a weight with
  -- proportional periods and a kernel on the edge from `Y^j_j` span all polynomials. The variables
  -- split into two blocks of columns, and the products `A * B` span.
  have h_cover : ∀ i : D.Φ × D.GridIndex true j (j + 1) × D.GridIndex true j j,
      i ∈ Set.range (Prod.map id (Prod.map (D.subdiagEquiv j).symm (D.gridDiagEquiv j ∘ .inl))) ∪
        Set.range (Prod.map id (Prod.map (D.subdiagEquiv j).symm (D.gridDiagEquiv j ∘ .inr))) := by
    simp [reindex_equiv (D.gridDiagEquiv j)]
  -- The edge from `Y^j_j` to `S` is a lift, the edge from `Ỹ^j_j` to `S` a transposed lift.
  refine (seesaw_periods D.PeriodTriple (W := fun x ↦ tuplesOn x.1 (downPath q).edges)
    (u := fun x ↦ Ψ x.1) (T := D.gridSpace 0 false (j + 1) j) (S' := D.gridSpace 0 true j (j + 1))
    (isEdgeFamily_grid_succ_left Prod.fst hj hj.le) (isEdgeFamily_grid_succ_right Prod.fst hj.le hj)
    fun p _ ↦ ?_).imp fun β hβ x ↦ hβ x
  refine mul_le.2 ?_ (mem_rename_range_mul _ _ h_cover p)
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  -- A product `A * B` qualifies, with `A` on the edge from `Y^j_j` and `B` in the weight on `S`.
  refine subset_span ⟨A, fun x S ↦ Pi.single ((D.diagonalCorner j).oldMatrix S).toRows₂ 1,
    fun x S ↦ columnLineKernel j x.1 ((D.diagonalCorner j).oldColumn S) B, fun z ↦ h_column z B,
    fun x S g₁ g₂ ↦ ?_⟩
  -- The weight of the period on the path is the constant `1`.
  exact (one_mul _).trans (modKernel_eq_columnLineKernel_mul x.1 hj (S (columnEdge true j j)) A B g₁
    g₂)

/-- Seesaw on `rightPath q`, the path through `(j + 1, j + 1)` that continues the halves `q`: if
`IsProportional (rightPath q) Ψ Ξ` holds, i.e. the periods of `Ψ` on that path are multiples of `Ξ`
by constants independent of the twist and the forms, then there is `β` with
`rowPeriod hj q Ψ z p x = β * Ξ x` for every `x : D.PeriodTriple`. -/
lemma IsProportional.exists_rowPeriod_eq_mul (hj : j < D.m) {q : Bool → GridPath 0 D.m j (j + 1)}
    {Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ} (z : GInf D.E (D.gridSigns false 0 (j + 1) j))
    {Ξ : D.PeriodTriple → ℂ} (h_path : IsProportional (rightPath q) Ψ Ξ)
    (p : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ) :
    ∃ β : ℂ, ∀ x : D.PeriodTriple, rowPeriod hj q Ψ z p x = β * Ξ x := by
  refine (seesaw_periods D.PeriodTriple (W := fun x ↦ tuplesOn x.1 (rightPath q).edges)
    (u := fun x ↦ Ψ x.1) (T := D.gridSpace 0 true (j + 1) (j + 1))
    (S' := D.gridSpace 0 false (j + 1) (j + 1)) (isEdgeFamily_grid_succ_left Prod.fst hj hj)
    (isEdgeFamily_grid_succ_right Prod.fst hj hj) fun A _ ↦ subset_span ?_).imp fun β hβ x ↦ hβ x
  -- With `p` fixed, every polynomial `A` on the edge to `Y^(j+1)_(j+1)` qualifies, with `A * p` on
  -- the edge to `Ỹ^(j+1)_(j+1)`, as the periods on the path are proportional by hypothesis.
  refine ⟨renameRowsCols (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm
      (renameRowsCols .inl id A * renameRowsCols .inr id p),
    fun x S ↦ Pi.single (S (rowEdge true j (j + 1))) 1, _, h_path, fun x S g g' ↦ ?_⟩
  -- The weight of the period on the path is the constant `1`.
  exact (rowLineKernel_mul_modKernel x.1 hj (S (rowEdge true j (j + 1))) A p g g').trans
    (one_mul _).symm

/-- The theta kernel is linear in the function `Ψ` on matrices modulo `𝔪`: it is the sum of the
kernels of the point masses, weighted by `Ψ`. -/
lemma modKernel_eq_sum_single {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ} (S : Space D.E n s) (T : Space D.E n' s')
    (a b : AutChar D.E) (𝔪 : Modulus D.E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (p : MvPolynomial (D.Φ × n' × n) ℂ) (g : New.G D.E s) (h : New.G D.E s') :
    modKernel S T a b 𝔪 Ψ p g h =
      ∑ v : Matrix n' n 𝔪.ResidueRing, Ψ v * modKernel S T a b 𝔪 (Pi.single v 1) p g h := by
  simp [modKernel, pairTheta, modDatum_eq_sum _ _ Ψ]

/-- Reversing the line: the kernel from the line `E ẽ_j = Ỹ^j_j ⊖ Y^j_j` with column `v` is, up to a
factor `c` with `‖c‖² = (Nm 𝔪) ^ (-rk S)`, the Fourier transform of the kernels to the line
`E ẽ_(j+1)` with rows `v'`, with respect to an additive character `ψ`. Here `𝔪 = gridModulus ϑ` and
`S = Y^(j+1)_j`. The map `τ` of polynomials does not depend on the twist. -/
lemma exists_columnLineKernel_eq (D : Data P) (j : ℕ) :
    ∃ (τ : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ →
        MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ)
      (ψ : ∀ ϑ : D.MFoldTwist, AddChar (gridModulus ϑ).ResidueRing ℂ) (c : D.MFoldTwist → ℂˣ),
      (∀ ϑ : D.MFoldTwist,
        ‖(c ϑ : ℂ)‖ ^ 2 * card (D.GridIndex false (j + 1) j → (gridModulus ϑ).ResidueRing) = 1) ∧
      ∀ (ϑ : D.MFoldTwist)
        (v : Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus ϑ).ResidueRing)
        (p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ)
        (g : New.G D.E (D.gridSigns true 0 j (j + 1))),
        (columnLineKernel j ϑ v p).weightFn g =
          c ϑ * ∑ v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus ϑ).ResidueRing,
            ψ ϑ (v' * v).trace * (rowLineKernel j ϑ v' (τ p)).weightFn g := by
  let τ := flipPoly (E := D.E) (fun _ : Unit ↦ (-1) ^ (j + 1)) (D.gridSigns false 0 (j + 1) j)
  have h_flip (ϑ : D.MFoldTwist) : ∃ (ψ : AddChar (gridModulus ϑ).ResidueRing ℂ) (c : ℂˣ),
      ‖(c : ℂ)‖ ^ 2 * card (D.GridIndex false (j + 1) j → (gridModulus ϑ).ResidueRing) = 1 ∧
      ∀ (p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ)
        (f : Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus ϑ).ResidueRing → ℂ)
        (h : New.G D.E (D.gridSigns false 0 (j + 1) j)),
        modKernel (signedSpace D.E fun _ : Unit ↦ (-1) ^ j) (D.gridSpace 0 false (j + 1) j) 1
            (gridChar ϑ false j (D.GridIndex false (j + 1) j)) (gridModulus ϑ) f p
            (1, (gridModulus ϑ).flipScalar ^ j) h =
          c * modKernel (D.gridSpace 0 false (j + 1) j)
            (signedSpace D.E fun _ : Unit ↦ (-1) ^ (j + 1))
            (gridChar ϑ true j (D.GridIndex false (j + 1) j)) WeilData.upsilonU1 (gridModulus ϑ)
            (matrixFourier ψ f) (τ p) h (1, (gridModulus ϑ).flipScalar ^ (j + 1)) := by
    rw [show (-1 : ℤˣ) ^ j = -(-1) ^ (j + 1) by simp [pow_succ],
      pow_succ ((gridModulus ϑ).flipScalar Unit)]
    apply exists_modKernel_flip_line
  choose ψ c h_norm h_kernel using h_flip
  refine ⟨τ, ψ, c, h_norm, fun ϑ v p g ↦ ?_⟩
  rw [columnLineKernel_weightFn, h_kernel, modKernel_eq_sum_single]
  -- The Fourier transform of the point mass at `v` takes the value `ψ (v' * v).trace` at `v'`.
  simp [rowLineKernel_weightFn, matrixFourier, Pi.single_apply]

/-- The corner on the diagonal, which removes the nodes `Y^j_j`, `Ỹ^j_j` and adds `Y^(j+1)_(j+1)`,
`Ỹ^(j+1)_(j+1)`, is a turn of a path whose other edges are those of two halves `q` from `(0, m)` to
`(j, j + 1)`. These edges avoid the removed nodes and do not end at the added ones; at one kept node
the old edge is vertical and the new one is not; opposite edges of the corner have equal characters.
An admissible family has at `Ỹ^(j+1)_(j+1)` its element at `Y^(j+1)_(j+1)` extended by `1` on the
line, and it stays admissible if any `k` is put at `Y^j_j` and `k ⊕ 1` at `Ỹ^j_j`. -/
lemma isTurn_diagonalCorner (hj : j < D.m) (q : Bool → GridPath 0 D.m j (j + 1))
    (ϑ : D.MFoldTwist) :
    (D.diagonalCorner j).IsTurn ϑ ((q false).edges false ∪ (q true).edges true) where
  fst_ne_snd := by simp
  ne_low_and_ne_lowExt := by simp
  -- The edges of the halves lie in the rectangle spanned by `(0, m)` and `(j, j + 1)`.
  endpoints_notMem := by
    rintro ⟨u, v⟩ he
    grind [→ GridPath.eq_and_le_of_mem_edges, Prod.le_def]
  vertical := by simp [IsVerticalEdge]
  edgeChar_fst := by simp [edgeChar, IsVerticalEdge]
  edgeChar_snd := by simp [edgeChar, IsVerticalEdge]
  apply_highExt _ := fun ⟨_, h_diag⟩ ↦ h_diag (j + 1)
  exists_eq_low g hg k := by
    obtain ⟨h_end, h_diag⟩ := hg
    refine ⟨update (update g (false, j, j) k) (true, j, j) (blockInlGL (D.gridDiagEquiv j) k),
      ⟨fun z ↦ ?_, fun a ↦ ?_⟩, ?_, by simp, fun p hp hp' ↦ ?_⟩
    · have h_ne (b : Bool) : (z, 0, D.m) ≠ (b, j, j) := by grind
      rw [update_of_ne (h_ne true), update_of_ne (h_ne false)]
      exact h_end z
    · obtain rfl | ha := eq_or_ne a j
      · simp
      · simpa [ha] using h_diag a
    · simp
    · rw [update_of_ne hp', update_of_ne hp]

/-- The character of the corner on the diagonal is the inverse product of the characters `edgeChar`
modulo `𝔪` of the edges `Y^j_j → Y^j_(j+1)` (`columnEdge`) and `Y^j_j → Y^(j+1)_j` (`rowEdge`),
since the edge from `Ỹ^j_j` to `Ỹ^(j+1)_j` has the character of the latter. -/
lemma char_diagonalCorner (ϑ : D.MFoldTwist) : (D.diagonalCorner j).char ϑ =
    (edgeChar ϑ (columnEdge false j j) * edgeChar ϑ (rowEdge false j j))⁻¹ := by
  simp [Corner.char, edgeChar, IsVerticalEdge]

/-- For `S = Y^(j+1)_j` the number of columns modulo `𝔪`, the modulus `gridModulus ϑ`, is at most
`vectorCountBound ϑ`. -/
lemma card_column_le_vectorCountBound (hj : j < D.m) (ϑ : D.MFoldTwist) :
    card (Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus ϑ).ResidueRing) ≤ vectorCountBound
      ϑ :=
  (card_congr Matrix.of.symm).trans_le <| by
    simpa [vectorCountBound] using Nat.pow_le_pow_right Fintype.card_pos
      (D.card_gridIndex_le hj hj.le)

/-- If the kernel from the line with column `v` is `c` times the Fourier transform of the kernels to
the line with rows `v'`, the same holds for their `periodPairing`, the integral of such a kernel
against a form `φ` on `Ỹ^(j+1)_j` and a form `y` on `Y^(j+1)_j` translated by the point `z` of the
archimedean group `GInf`. -/
lemma periodPairing_columnLineKernel_eq (hj : j < D.m) {ϑ : D.MFoldTwist}
    {v : Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus ϑ).ResidueRing}
    {p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ}
    {p' : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ}
    {ψ : AddChar (gridModulus ϑ).ResidueRing ℂ} {c : ℂ}
    (h_line : ∀ g : New.G D.E (D.gridSigns true 0 j (j + 1)),
      (columnLineKernel j ϑ v p).weightFn g =
      c * ∑ v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus ϑ).ResidueRing,
        ψ (v' * v).trace * (rowLineKernel j ϑ v' p').weightFn g)
    (z : GInf D.E (D.gridSigns false 0 (j + 1) j)) (φ : D.GridForm true j (j + 1))
    (y : D.GridForm false (j + 1) j) :
    periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩) (columnLineKernel j ϑ v p) z φ y =
      c * ∑ v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus ϑ).ResidueRing,
        ψ (v' * v).trace *
          periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩) (rowLineKernel j ϑ v' p') z φ
            y := by
  let F v' (g : New.G D.E (D.gridSigns true 0 j (j + 1))) : ℂ :=
    (rowLineKernel j ϑ v' p').weightFn g *
      (φ g * y ((rowLineKernel j ϑ v' p').comparisonMap g * (z, 1)))
  have h_int v' : Integrable (F v') (D.gridSpace 0 true j (j + 1)).quotMeasure := by
    simpa only [mul_assoc] using integrable_moderate_mul_forms
      (isConjKernelPair_gridKernel ⟨hj.le, hj⟩) (rowLineKernel j ϑ v' p') φ y
  have h_swap : ∫ g, ∑ v', ψ (v' * v).trace * F v' g ∂(D.gridSpace 0 true j (j + 1)).quotMeasure =
      ∑ v', ψ (v' * v).trace * ∫ g, F v' g ∂(D.gridSpace 0 true j (j + 1)).quotMeasure := by
    simp [integral_finsetSum _ fun v' _ ↦ (h_int v').const_mul _, integral_const_mul]
  simp only [periodPairing, LinearMap.mk₂_apply, h_line, sum_mul, mul_assoc, integral_const_mul]
  -- Both weights have the comparison map `D.subdiagMap j`.
  exact congrArg (c * ·) h_swap

/-- Reversing the line and crossing the square `(j, j)`, for one triple `x` of a twist and two
forms. Suppose the kernels from the line for the polynomial `p` (`columnLineKernel`) are `c` times
the Fourier transforms of the kernels to the line for the polynomial `p'` (`rowLineKernel`), the
exchange on the square with identification `σ` of its sides holds with factor `C`, and `Ψ`, with `X`
and `v'` put on the new edges by `newTuple`, corresponds under `σ` to the Fourier transform of `Ψ'`
in the column of the line. Then `columnPeriod` of `Ψ'` for `p` is `c * C` times `rowPeriod` of `Ψ`
for `p'`. -/
lemma columnPeriod_eq_mul_rowPeriod (hj : j < D.m) (q : Bool → GridPath 0 D.m j (j + 1))
    {Ψ Ψ' : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ} {x : D.PeriodTriple}
    {p : MvPolynomial (D.Φ × D.GridIndex false (j + 1) j × Unit) ℂ}
    {p' : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ}
    {ψ : AddChar (gridModulus x.1).ResidueRing ℂ} {c C : ℂ}
    {σ : D.GridIndex false j j ⊕ D.GridIndex false (j + 1) (j + 1) ≃
      D.GridIndex false j (j + 1) ⊕ D.GridIndex false (j + 1) j}
    (h_line : ∀ (v : Matrix (D.GridIndex false (j + 1) j) Unit (gridModulus x.1).ResidueRing)
      (g : New.G D.E (D.gridSigns true 0 j (j + 1))), (columnLineKernel j x.1 v p).weightFn g =
        c * ∑ v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus x.1).ResidueRing,
          ψ (v' * v).trace * (rowLineKernel j x.1 v' p').weightFn g)
    (h_law : ∀ (f : D.GridForm false j (j + 1)) (l : D.GridForm false (j + 1) j →ₗ[ℂ] ℂ),
      SquareLaw ((D.diagonalCorner j).char x.1) σ C
        (fun X : Matrix (D.GridIndex false (j + 1) (j + 1))
            (D.GridIndex false j (j + 1) ⊕ D.GridIndex false (j + 1) j)
              (gridModulus x.1).ResidueRing ↦
          l (transposedMove X.toCols₂ (liftMove X.toCols₁ f)))
        (fun Y : Matrix (D.GridIndex false j (j + 1) ⊕ D.GridIndex false (j + 1) j)
            (D.GridIndex false j j) (gridModulus x.1).ResidueRing ↦
          l (liftMove Y.toRows₂ (transposedMove Y.toRows₁ f))))
    (h_match : ∀ (S : EdgeTuple x.1)
      (v' : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus x.1).ResidueRing),
      AreMatched ⊤ σ ((D.diagonalCorner j).char x.1)
        (fun X : Matrix (D.GridIndex false (j + 1) (j + 1))
            (D.GridIndex false j (j + 1) ⊕ D.GridIndex false (j + 1) j)
              (gridModulus x.1).ResidueRing ↦
          Ψ x.1 ((D.diagonalCorner j).newTuple S X v'))
        ((D.diagonalCorner j).columnFourier ψ (Ψ' x.1) S v'))
    (z : GInf D.E (D.gridSigns false 0 (j + 1) j)) :
    columnPeriod hj q Ψ' z p x = c * (C * rowPeriod hj q Ψ z p' x) := by
  obtain ⟨ϑ, y, φ⟩ := x
  -- The form that arrives at the square, and the pairing with the form that arrives at `S`.
  let f (S : EdgeTuple ϑ) (v' : Matrix Unit (D.GridIndex false (j + 1) j)
    (gridModulus ϑ).ResidueRing) :
      D.GridForm false j (j + 1) × (D.GridForm false (j + 1) j →ₗ[ℂ] ℂ) :=
    ((q false).formMap S false y, periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩)
      (rowLineKernel j ϑ v' p') z ((q true).formMap S true φ))
  have h_dep : DependsOn f ↑((q false).edges false ∪ (q true).edges true) := fun S S' h ↦ by
    have h_map (b : Bool) : (q b).formMap S b = (q b).formMap S' b :=
      (q b).formMap_congr fun e he ↦ h e (by cases b <;> simp [he])
    simp only [f, h_map]
  have h_square : ∑ S ∈ tuplesOn ϑ (downPath q).edges, Ψ' ϑ S *
      ∑ v', ψ (v' * (D.diagonalCorner j).oldColumn S).trace *
        (f S v').2 (liftMove ((D.diagonalCorner j).oldMatrix S).toRows₂
          (transposedMove ((D.diagonalCorner j).oldMatrix S).toRows₁ (f S v').1)) =
      C * rowPeriod hj q Ψ z p' (ϑ, y, φ) := by
    rw [rowPeriod, edges_rightPath, edges_downPath]
    exact (isTurn_diagonalCorner hj q ϑ).sum_eq_of_squareLaw h_match
      (fun i : D.GridForm false j (j + 1) × (D.GridForm false (j + 1) j →ₗ[ℂ] ℂ) ↦ h_law i.1 i.2)
      h_dep
  rw [columnPeriod, ← h_square, mul_sum]
  simp only [f, periodPairing_columnLineKernel_eq hj (h_line _)]
  exact sum_congr rfl fun _ _ ↦ mul_left_comm ..

/-- One turn on the diagonal, at `j < m`. There are numbers `c ϑ ≠ 0` of absolute value
`turnRatio j j ϑ` up to a constant and a power of `Nm Q`, with `Q` the modulus of the twist `ϑ`,
such that the following holds for all pairs `q` of monotone paths from `(0, m)` to `(j, j + 1)`, one
in each grid. Path data `Ψ'` on `downPath q` give path data `Ψ` on `rightPath q`, with the bound for
the number of roots of unity in a value multiplied by `vectorCountBound = (Nm 𝔪) ^ (2 * n_m)`, where
`𝔪 = gridModulus ϑ` and `n_m = D.n D.m`, and `Ψ ∝ Ξ` implies `Ψ' ∝ Ξ / c`. -/
lemma exists_transfersPeriods_diagonal (hj : j < D.m) :
    ∃ c : D.MFoldTwist → ℂˣ, D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ) (D.turnRatio j j) ∧
      ∀ q : Bool → GridPath 0 D.m j (j + 1),
        TransfersPeriods (downPath q) (rightPath q) vectorCountBound c := by
  -- Reverse the line and exchange on the square, between two seesaws.
  obtain ⟨κ, σ, c, hc, h_law⟩ := exists_squareLaw_grid_hasAbsUpToNormPower false hj hj
  obtain ⟨τ, ψ, c_line, h_norm, h_line⟩ := D.exists_columnLineKernel_eq j
  refine ⟨c / c_line, ?_, fun q N Ψ' hΨ' ↦ ?_⟩
  · have h_inv : D.HasAbsUpToNormPower (fun ϑ ↦ (c_line ϑ : ℂ)⁻¹) 1 :=
      .of_norm_sq_eq_mul_card_zpow _ 1 (card (D.GridIndex false (j + 1) j))
        (by simpa [field, eq_comm] using h_norm)
    simpa [div_eq_mul_inv, Pi.mul_def] using hc.mul h_inv
  have h_exists_matched (ϑ : D.MFoldTwist) : ∃ Ψ : EdgeTuple ϑ → ℂ,
      IsPathDatum (vectorCountBound ϑ * N ϑ) (rightPath q).edges Ψ ∧
      ∀ S v', AreMatched ⊤ σ ((D.diagonalCorner j).char ϑ)
        (fun X ↦ Ψ ((D.diagonalCorner j).newTuple S X v'))
        ((D.diagonalCorner j).columnFourier (ψ ϑ) (Ψ' ϑ) S v') := by
    simp only [edges_downPath, edges_rightPath] at hΨ' ⊢
    obtain ⟨Ψ, hΨ, h_match⟩ := (isTurn_diagonalCorner hj q ϑ).exists_isPathDatum (hΨ' ϑ) σ (ψ ϑ)
    exact ⟨Ψ, hΨ.mono (Nat.mul_le_mul_right _ (card_column_le_vectorCountBound hj ϑ)), h_match⟩
  choose Ψ hΨ h_match using h_exists_matched
  refine ⟨Ψ, hΨ, fun Ξ hΞ ↦ isProportional_of_columnPeriod hj fun z p ↦ ?_⟩
  obtain ⟨β, hβ⟩ := hΞ.exists_rowPeriod_eq_mul hj z (τ p)
  simp only [← char_diagonalCorner] at h_law
  refine ⟨κ * β, fun x ↦ ?_⟩
  calc columnPeriod hj q Ψ' z p x
    _ = c_line x.1 * (κ / c x.1 * rowPeriod hj q Ψ z (τ p) x) :=
      columnPeriod_eq_mul_rowPeriod hj q (fun v ↦ h_line x.1 v p) (h_law x.1) (h_match x.1) z
    _ = κ * β * (Ξ x / (c / c_line) x.1) := by simp [hβ, Units.val_div_eq_div_val, field]

/-- One turn. For `i, j < m` there are numbers `c ϑ ≠ 0`, of absolute value `turnRatio i j` up to a
constant and a power of `Nm Q`, with `Q` the modulus of `ϑ`, such that for every turn at `(i, j)`
path data `Ψ'` on the old path give path data `Ψ` on the new one, with the bound for the number of
roots of unity in a value multiplied by `vectorCountBound = (Nm 𝔪) ^ (2 * n_m)`, where
`𝔪 = gridModulus ϑ` and `n_m = D.n D.m`, and `Ψ ∝ Ξ` implies `Ψ' ∝ Ξ / c`. -/
theorem exists_transfersPeriods_of_turn {j i : ℕ} (hi : i < D.m) (hj : j < D.m) :
    ∃ c : D.MFoldTwist → ℂˣ, D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ) (D.turnRatio i j) ∧
      ∀ Γ' Γ : TwoGridPath D.m, Γ'.Turn (i, j) Γ → TransfersPeriods Γ' Γ vectorCountBound c := by
  have h_one_le : (1 : D.MFoldTwist → ℕ) ≤ vectorCountBound := fun _ ↦ pow_pos Fintype.card_pos _
  obtain hij | rfl | hij := lt_trichotomy i j
  · obtain ⟨c, hc, h_transfer⟩ := exists_transfersPeriods_off_diagonal false hij hj
    exact ⟨c, hc, fun Γ' Γ h_turn ↦ (h_transfer Γ' Γ h_turn).mono h_one_le⟩
  · obtain ⟨c, hc, h_transfer⟩ := exists_transfersPeriods_diagonal hj
    refine ⟨c, hc, fun Γ' Γ h_turn ↦ ?_⟩
    obtain ⟨q, rfl, rfl⟩ := h_turn.exists_eq_down_and_eq_right
    exact h_transfer q
  · obtain ⟨c, hc, h_transfer⟩ := exists_transfersPeriods_off_diagonal true hij hi
    exact ⟨c, hc, fun Γ' Γ h_turn ↦ (h_transfer Γ' Γ h_turn).mono h_one_le⟩

/-- There are numbers `c ϑ ≠ 0` whose absolute value is the product over `i, j < m` of
`turnRatio i j ϑ`, up to a constant and a power of `Nm Q`, with `Q` the modulus of the twist `ϑ`,
such that path data `Ψ'` on the first path give path data `Ψ` on the last, with the bound for the
number of roots of unity in a value multiplied by `vectorCountBound ^ m ^ 2`, and `Ψ ∝ Ξ` implies
`Ψ' ∝ Ξ / c`. -/
theorem exists_transfersPeriods_first_last (D : Data P) : ∃ c : D.MFoldTwist → ℂˣ,
    D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
      (∏ s ∈ range D.m ×ˢ range D.m, D.turnRatio s.1 s.2) ∧
    TransfersPeriods (.first D.m) (.last D.m) (vectorCountBound ^ D.m ^ 2) c := by
  have h_turn (s : ℕ × ℕ) (hs : s ∈ range D.m ×ˢ range D.m) : ∃ c : D.MFoldTwist → ℂˣ,
      D.HasAbsUpToNormPower (fun ϑ ↦ c ϑ) (D.turnRatio s.1 s.2) ∧
      ∀ Γ' Γ : TwoGridPath D.m, Γ'.Turn s Γ → TransfersPeriods Γ' Γ vectorCountBound c :=
    exists_transfersPeriods_of_turn (mem_range.1 (mem_product.1 hs).1)
      (mem_range.1 (mem_product.1 hs).2)
  choose! c hc h_transfer using h_turn
  refine ⟨∏ s ∈ range D.m ×ˢ range D.m, c s, ?_, ?_⟩
  · simpa only [Finset.prod_fn, Finset.prod_apply, Units.coe_prod] using HasAbsUpToNormPower.prod hc
  rw [show D.m ^ 2 = #(range D.m ×ˢ range D.m) by simp [sq]]
  apply TwoGridPath.turn_induction
    (motive := fun Γ T ↦ TransfersPeriods Γ (.last D.m) (vectorCountBound ^ #T) (∏ s ∈ T, c s))
  · simpa using TransfersPeriods.refl (.last D.m)
  · intro Γ' s Γ T hΓ hs ih
    rw [card_insert_of_notMem hs, prod_insert hs, pow_succ']
    exact (h_transfer s hΓ.mem_product Γ' Γ hΓ).trans ih

end New.Data

end
end
end

/-!
# Denominators and sizes on the last path, and the auxiliary forms

Let `Ξ = New.Data.lastPathPeriod Ψ y` be the sum attached to the last path. Its denominators are
small at the primes that do not divide `Nm Q` and, for the trivial twist, its conjugates are small.
Going back through the turns to the first path, and reading the values of a form from its pairings
with delta forms, we get integrality and size for the chain of lifts from `Y₀` to `Y_m` on the
restrictions of short forms. Throughout, `ϑ` is an `m`-fold twist, `Q` is its finite set of places,
`ϑ.normQ` is `Nm Q`, and sizes are measured by the parameters `x = D.x` and `b = D.b`. The
modulus `𝔪 = gridModulus ϑ` of the twist is the product of the chosen places to the power
`D.natB` (the number `b` as a natural number), times `Q`. The other numbers of the data that occur
are the level `D.M`, the order `D.q₁` of the root of unity that generates `E` over
`K = ℚ(√-P.d)`, the prime `P.d`, the ranks `D.n j` and the parameter `D.r`; at most
`D.natB * D.r ^ 4` boxes occur in each diagram of a weight on the last path.

## Main definitions and results

* `New.Data.exists_mul_lastPathPeriod_mem_embValRing`, `New.Data.norm_lastPathPeriod_le`:
  denominators and conjugates of `Ξ`.
* `New.Data.exists_integral_lowerChainUpTo_eq_lastPathPeriod`: the index of the level times the
  pairing with the chain of lifts of a restriction is a constant multiple of `Ξ` divided by the
  constants of the turns.
* `New.Data.exists_dualPairing_eq_mul_lastPathPeriod`: the values of the chain of lifts, read by
  delta forms, with one constant for all twists, points and forms.
* `New.Data.exists_span_short_lifts_eq_top`: the space of forms on `Y₀` is spanned by forms with two
  properties: for every twist their scaled lifts are integral at the primes not dividing `Nm Q`, and
  for the trivial twist the conjugates of their lifts are small. The passage to target forms is
  `New.Data.exists_span_isAuxiliaryForm_eq_top`, in `New.Determinant.Twist.LongForms`.

Notions from other files:
* `New.Data.lastPathPeriod Ψ y`: the sum over the tuples of matrices `S` of `Ψ S` times the pairing
  of the lifts of the two forms `y` along the halves of the last path, integrated over the finite
  points of `Y^m_m`.
* `New.Data.gridLevelForms m`: the forms of level `J(𝔟)` on `Ỹ^m_0`, where the half `true` of the
  last path starts; `𝔟` is generated by `New.Data.gridLevelGen`.
* `New.Data.levelY ϑ m`: the level `J(𝔪₀)` on `Y_m`, where `𝔪₀` is the product of the chosen places
  and `Q`.
* `New.weylGauge κ e g v`: the largest `p`-adic absolute value of a coordinate of `g⁻¹ v`.
* `New.weylNormSq v`: the squared norm of `v` for the integral Gram matrix of the Weyl module.
* `New.Data.lowerChain ϑ`: the chain of lifts, that is the composite of the `m` theta lifts from
  `Y₀` to `Y_m`, with values in algebraic forms. `New.Data.lowerChainAtLevel ϑ` is the same map with
  values in the forms of the last level and its character; `levelY ϑ m` fixes these forms.
-/

@[expose] public section

noncomputable section

namespace New.Data

open Real Matrix Fintype Submodule LevelPlaces.LevelForm Space Rows Finset Function

variable {P : Parameters} (D : Data P)

variable {D} in
/-- The bound for the number of roots of unity in a value of the data on the last path: that for
the first path, times one factor for each of the `m ^ 2` turns. Here `vectorCountBound ϑ` bounds the
number of column vectors modulo `𝔪` at a node of the grids and `edgeMatrixCountBound ϑ` the number
of matrices modulo `𝔪` at an edge. -/
abbrev lastPathBound (ϑ : D.MFoldTwist) : ℕ :=
  vectorCountBound ϑ ^ D.m ^ 2 * edgeMatrixCountBound ϑ ^ (2 * D.m)

/-! ### Denominators on the last path -/

/-- A product of powers of `M` and `P.d` that, at the primes not dividing `Nm Q`, clears the
denominators of each kernel on the last path. The first factor takes the datum of an edge to
standard data, and the second pays for the boxes of the diagram: `2 * D.n D.m` bounds the ranks on
that path and `D.natB * D.r ^ 4` the numbers of boxes. -/
def liftDenominator : ℕ :=
  (D.M ^ D.natB) ^ (2 * Core.numInfPlaces D.E * (2 * D.n D.m * (2 * D.n D.m))) *
    (D.M ^ D.natB * P.d) ^ (D.natB * D.r ^ 4)

section Denominators

variable {D}

/-- Let `p` be a prime that does not divide the product `ϑ.normQ` of the norms of the set `Q` of
places of the `m`-fold twist `ϑ`, and fix an embedding of `ℂ` into `ℂ_[p]` (`PadicPlace p`). The
half `z` of the last path is a sequence of `m + 1` spaces, and the theta kernel
`lastPathKernel ϑ z j` lifts forms from the `j`-th to the next. For a tuple `S` of matrices on the
edges, the finite datum `lastPathEdgeDatum S z j` of this lift, multiplied by the number
`liftDenominator`, lies in `raises 1 1 1` of the kernel. The first two `1`s are translations of the
source point and of the target point, here trivial, and the third is a factor: for all finite points
`g` of the source and `h` of the target, the lift from `g` to `h` does not increase `p`-adic
gauges. -/
lemma liftDenominator_smul_lastPathEdgeDatum_mem_raises {ϑ : D.MFoldTwist} {p : ℕ} [Fact p.Prime]
    [PadicPlace p] (hp : p.Coprime ϑ.normQ) (S : EdgeTuple ϑ) (z : Bool) {j : ℕ} (hj : j < D.m) :
    (D.liftDenominator : ℂ) • lastPathEdgeDatum S z j ∈ (lastPathKernel ϑ z j).raises 1 1 1 := by
  have h_dvd : (D.M ^ D.natB) ^
        (2 * Core.numInfPlaces D.E * card (D.LastPathIndex z (j + 1) × D.LastPathIndex z j)) *
      (D.M ^ D.natB * P.d) ^ boxes (D.lastPathColumns z) (card (D.LastPathIndex z (j + 1))) ∣
      D.liftDenominator := by
    grw [card_prod, boxes_lastPathColumns_le_natB_mul z hj, card_lastPathIndex_le z hj,
      card_lastPathIndex_le z hj.le, liftDenominator]
  unfold lastPathKernel
  exact P.smul_mem_raises_of_dvd (lastPathEdgeDatum S z j)
    (P.smul_vacuumDatum_mem_standardData normQ_mul_M_pow_mem_modulus
      (by simp [ite_mem, Pi.single_apply]) hp)
    embValRing.one_mem h_dvd

/-- Let `t` be the idele that generates the modulus `𝔪 = gridModulus ϑ` of the `m`-fold twist `ϑ`
and `α = P.α D.towerExp` the fixed idele of the CM field `D.E`, for which `q₁ * α` and `α⁻¹` are
integral, with `q₁ = P.q₁ D.towerExp`. Write `star` for complex conjugation on the finite adeles of
`D.E`, `normQ` for the product of the norms of the places in the set `Q` of `ϑ`, `M = D.M` for the
level and `natB = D.natB` for the exponent of the chosen places in `𝔪`. The flip scalar
`u = star (t * α) / (t * α)` becomes an integral adele after multiplication by
`normQ * M ^ natB * q₁`. -/
lemma generator_inv_mul_normQ_mul_star_mem (ϑ : D.MFoldTwist) :
    (gridModulus ϑ).generator⁻¹.val *
        algebraMap (NumberField.RingOfIntegers D.E) (Ô D.E) ↑(ϑ.normQ * D.M ^ D.natB) *
      (star ((gridModulus ϑ).generator.val * (P.q₁ D.towerExp * (P.α D.towerExp).val)) *
        (P.α D.towerExp)⁻¹.val) ∈
      Ô D.E := by
  -- `t`, `q₁ * α` and `α⁻¹` are integral, and `t` divides `normQ * M ^ natB`.
  have h_red : (gridModulus ϑ).reduction (algebraMap (NumberField.RingOfIntegers D.E) (Ô D.E)
      ↑(ϑ.normQ * D.M ^ D.natB)) = 0 :=
    (Modulus.reduction_eq_zero_iff _).2 (Ideal.mem_map_of_mem _ normQ_mul_M_pow_mem_modulus)
  rw [Modulus.reduction_eq_zero_iff_generator_inv_mul_mem] at h_red
  exact mul_mem h_red (mul_mem
    (star_mem_Ô (mul_mem (gridModulus ϑ).generator_mem P.q₁_mul_alpha_mem)) P.inv_alpha_mem)

/-- Let `ϑ` be an `m`-fold twist, `ϑ.normQ` the product of the norms of its places, and `p` a prime
that does not divide it. Let `u` be the flip scalar `star (t * α) / (t * α)` of the modulus
`gridModulus ϑ` (`t` generates the modulus, `α` is a fixed idele), as a `1 × 1` matrix (index type
`Unit`) over the finite adeles. For an infinite place `τ : D.Φ` of the CM field `D.E`, map the
matrix `(u ^ m)⁻¹` to `ℂ_[p]`. The map is the component at the prime above `p` of the embedding
`weightEmbedding ιₚ τ`. Let `δ` be the determinant of the image. For every integer `l`, the product
of `(M ^ natB * q₁) ^ (m * |l|)` and `(δ ^ l)⁻¹` has absolute value at most `1`. -/
lemma norm_mul_det_flipScalar_zpow_le_one {ϑ : D.MFoldTwist} {p : ℕ} [Fact p.Prime] [PadicPlace p]
    (hp : p.Coprime ϑ.normQ) (τ : D.Φ) (l : ℤ) :
    ‖((D.M ^ D.natB * D.q₁) ^ (D.m * l.natAbs) : ℕ) *
      (((((gridModulus ϑ).flipScalar Unit).val ^ D.m)⁻¹.map
        (adeleExtension (weightEmbedding ιₚ τ))).det ^ l)⁻¹.val‖ ≤ 1 := by
  -- According to the sign of `l`, the number has the norm of a power of the integral adele `a` or
  -- of its conjugate, because `ϑ.normQ` is a `p`-adic unit.
  let f : 𝔸f D.E →+* ℂ_[p] := adeleExtension (weightEmbedding ιₚ τ)
  let u : unitary (𝔸f D.E) := divStar (star ((gridModulus ϑ).generator * P.α D.towerExp))
  let a : 𝔸f D.E := (gridModulus ϑ).generator⁻¹.val *
      algebraMap (NumberField.RingOfIntegers D.E) (Ô D.E) ↑(ϑ.normQ * D.M ^ D.natB) *
    (star ((gridModulus ϑ).generator.val * (P.q₁ D.towerExp * (P.α D.towerExp).val)) *
      (P.α D.towerExp)⁻¹.val)
  have ha_eq : a = ((ϑ.normQ * (D.M ^ D.natB * D.q₁) : ℕ) : 𝔸f D.E) * u.val := by
    have hnat : (algebraMap (NumberField.RingOfIntegers D.E) (Ô D.E)
        ↑(ϑ.normQ * D.M ^ D.natB) : 𝔸f D.E) = ((ϑ.normQ * D.M ^ D.natB : ℕ) : 𝔸f D.E) := by
      simp
    have hu : u.val = star (gridModulus ϑ).generator.val * star (P.α D.towerExp).val *
        (gridModulus ϑ).generator⁻¹.val * (P.α D.towerExp)⁻¹.val := by
      simp only [u, coe_divStar, _root_.mul_inv_rev, Units.val_mul, ← star_inv, Units.coe_star,
        star_mul', star_star]
      ring
    dsimp only [a]
    rw [hnat, hu]
    simp only [star_mul', star_natCast, Nat.cast_mul, Nat.cast_pow]
    ring
  have hstar_a_eq : star a = ((ϑ.normQ * (D.M ^ D.natB * D.q₁) : ℕ) : 𝔸f D.E) * (u⁻¹).val := by
    rw [ha_eq, star_mul', star_natCast]
    rfl
  have hdet : (((((gridModulus ϑ).flipScalar Unit).val ^ D.m)⁻¹.map f).det : ℂ_[p]) =
      (f u.val ^ D.m)⁻¹ := by
    have h1 : ((((gridModulus ϑ).flipScalar Unit).val.map f).det : ℂ_[p]) = f u.val := by
      change ((((gridModulus ϑ).flipScalar Unit).val : Matrix Unit Unit (𝔸f D.E)).map f).det =
        f u.val
      rw [Matrix.det_unique, Matrix.map_apply]
      congr 1
    rw [map_inv, map_pow, map_inv, map_pow, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, h1]
  have hnorm (c : 𝔸f D.E) (v : unitary (𝔸f D.E))
      (hc : c = ((ϑ.normQ * (D.M ^ D.natB * D.q₁) : ℕ) : 𝔸f D.E) * v.val) :
      ‖((D.M ^ D.natB * D.q₁ : ℕ) : ℂ_[p]) * f v.val‖ = ‖f c‖ := by
    symm
    rw [hc, map_mul, map_natCast, Nat.cast_mul ϑ.normQ, mul_assoc, norm_mul,
      hp.norm_natCast_eq_one, one_mul]
  obtain ⟨k, rfl | rfl⟩ := l.eq_nat_or_neg
  · have h_eq : ‖((D.M ^ D.natB * D.q₁) ^ (D.m * (k : ℤ).natAbs) : ℕ) *
        (((((gridModulus ϑ).flipScalar Unit).val ^ D.m)⁻¹.map f).det ^ (k : ℤ))⁻¹.val‖ =
        ‖f a‖ ^ (D.m * k) := by
      rw [Int.natAbs_natCast, Nat.cast_pow, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
        zpow_natCast, hdet, inv_pow, inv_inv, ← pow_mul, ← mul_pow, norm_pow, hnorm a u ha_eq]
    rw [h_eq]
    exact pow_le_one₀ (norm_nonneg _)
      (norm_adeleExtension_le_one _ (generator_inv_mul_normQ_mul_star_mem ϑ))
  · have h_eq : ‖((D.M ^ D.natB * D.q₁) ^ (D.m * (-(k : ℤ)).natAbs) : ℕ) *
        (((((gridModulus ϑ).flipScalar Unit).val ^ D.m)⁻¹.map f).det ^ (-(k : ℤ)))⁻¹.val‖ =
        ‖f (star a)‖ ^ (D.m * k) := by
      rw [Int.natAbs_neg, Int.natAbs_natCast, Nat.cast_pow, Units.val_inv_eq_inv_val,
        Units.val_zpow_eq_zpow_val, _root_.zpow_neg, zpow_natCast, inv_inv, hdet, inv_pow,
        ← pow_mul, ← inv_pow,
        ← (show f (u⁻¹).val = (f u.val)⁻¹ from map_units_inv f (Unitary.toUnits u)),
        ← mul_pow, norm_pow, hnorm (star a) u⁻¹ hstar_a_eq]
    rw [h_eq]
    exact pow_le_one₀ (norm_nonneg _)
      (norm_adeleExtension_le_one _ (star_mem_Ô (generator_inv_mul_normQ_mul_star_mem ϑ)))

end Denominators

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- The pairing `lastPathPairing v' v = v' ⬝ᵥ lastPathBranching *ᵥ v` of the two halves at the
middle of the last path, given by an integer branching matrix, is cleared by one natural number
`N ≠ 0` with `log N ≤ x ^ 98 * b ^ 2`. For every twist `ϑ` and every prime `p` prime to the norm
`ϑ.normQ` of its places, if `v'` has gauge at most `1` at `g` and `v` at the block point
`lastPathBlockPoint ϑ g = diag (g, u ^ m)`, with `u` the flip scalar of the modulus `gridModulus ϑ`,
then `N` times the pairing of `v'` and `v`, read `p`-adically by `ιₚ`, is integral. -/
lemma exists_norm_mul_lastPathPairing_le_one : ∃ N ≠ (0 : ℕ),
    log N ≤ D.x ^ 98 * D.b ^ 2 ∧
    ∀ {ϑ : D.MFoldTwist} {p : ℕ} [Fact p.Prime] [PadicPlace p], p.Coprime ϑ.normQ →
      ∀ {g : Gf D.E (D.LastPathIndex false D.m)} {v' : D.LastPathVector false D.m}
        {v : D.LastPathVector true D.m},
        weylGauge (D.lastPathColumns false) (D.lastPathDetExp false D.m) g v' ≤ 1 →
        weylGauge (D.lastPathColumns true) (D.lastPathDetExp true D.m) (lastPathBlockPoint ϑ g) v ≤
          1 →
        ‖ιₚ (N * D.lastPathPairing v' v)‖ ≤ 1 := by
  -- By equivariance the pairing is the inverse of the character `∏ τ, det u' ^ L τ` at
  -- `u' = (flipScalar ^ m)⁻¹` times the pairing of the translated vectors, which have integral
  -- entries; the product of the numbers `N τ` clears the character.
  obtain ⟨L, h_equiv, hL⟩ := D.exists_lastPathBranching_equivariant
  have hL_le (τ : D.Φ) : (L τ).natAbs ≤ D.natB * D.r ^ 4 + ⌈20 * D.b⌉₊ :=
    (hL τ).trans (add_le_add (boxes_lastPathColumns_le_natB_mul true le_rfl)
      (natAbs_lastPathDetExp_le true le_rfl τ))
  let N (τ : D.Φ) : ℕ := (D.M ^ D.natB * D.q₁) ^ (D.m * (L τ).natAbs)
  have h_log : log (∏ τ, N τ : ℕ) ≤ D.x ^ 98 * D.b ^ 2 :=
    calc _ = ∑ τ, D.m * (L τ).natAbs *
          (D.natB * log D.M + (log P.q₀ + log (towerDeg D.towerExp))) := by
          simp [N, log_prod, log_mul, NeZero.ne, -Nat.cast_natAbs]
      _ ≤ _ := by
          grw [hL_le]
          rw [sum_const, card_univ, nsmul_eq_mul]
          exact D.le_of_hasLogBound
  refine ⟨∏ τ, N τ, by simp [N, NeZero.ne, prod_eq_zero_iff], h_log,
    fun {ϑ p _ _} hp g v' v hv' hv ↦ ?_⟩
  let f (τ : D.Φ) : 𝔸f D.E →+* ℂ_[p] := adeleExtension (weightEmbedding ιₚ τ)
  let u' : Gf D.E Unit := ((gridModulus ϑ).flipScalar ^ D.m)⁻¹
  let χ (τ : D.Φ) : ℂ_[p]ˣ := (u'.val.map (f τ)).det ^ L τ
  let w' : WeylIndex (D.LastPathIndex false D.m) (D.lastPathColumns false) → ℂ_[p] :=
    weylRep (D.lastPathColumns false) (D.lastPathDetExp false D.m) (fun τ ↦ g⁻¹.1.map (f τ)) *ᵥ ιₚ ∘
      v'
  let w : WeylIndex (D.LastPathIndex true D.m) (D.lastPathColumns true) → ℂ_[p] :=
    weylRep (D.lastPathColumns true) (D.lastPathDetExp true D.m)
      (fun τ ↦ (U.block (D.gridDiagEquiv D.m) (g⁻¹, u')).val.map (f τ)) *ᵥ ιₚ ∘ v
  have hw' : ∀ i, ‖w' i‖ ≤ 1 := (pi_norm_le_iff_of_nonneg one_pos.le).1 hv'
  have hw : ∀ i, ‖w i‖ ≤ 1 := by
    simpa [u', weylGauge, lastPathBlockPoint, ← map_inv, pi_norm_le_iff_of_nonneg] using hv
  -- Elements of norm at most `1` form a subring, which contains the entries of `w'` and `w`.
  have h_int : ‖w' ⬝ᵥ D.lastPathBranching.map (↑) *ᵥ w‖ ≤ 1 :=
    NormedField.valuation.integer.sum_mem fun i _ ↦
      mul_mem (hw' i) (sum_mem fun k _ ↦ mul_mem (by simp) (hw k))
  have h_char : w' ⬝ᵥ D.lastPathBranching.map (↑) *ᵥ w = (∏ τ, χ τ : ℂ_[p]ˣ) * ιₚ
    (D.lastPathPairing v' v) :=
    (h_equiv _ _ f g⁻¹ u' _ _).trans <| by
      congr 1
      simp only [LinearMap.compl₂_apply, Matrix.mulVecLin_apply, dotProductBilin_apply_apply,
        dotProduct, mulVec, map_sum, map_mul, map_intCast, Matrix.map_apply, Function.comp_apply]
  calc _ = (∏ τ, ‖N τ * (χ τ)⁻¹.val‖) * ‖w' ⬝ᵥ D.lastPathBranching.map (↑) *ᵥ w‖ := by
        rw [h_char, ← norm_prod, ← norm_mul, ← mul_assoc, Units.coe_prod, ← prod_mul_distrib]
        simp only [mul_assoc, Units.inv_mul, mul_one, map_mul, map_natCast, map_prod,
          Nat.cast_prod]
    _ ≤ 1 := (mul_le_of_le_one_left (norm_nonneg _)
        (prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun τ _ ↦
      norm_mul_det_flipScalar_zpow_le_one hp τ (L τ))).trans h_int

/-- There is a natural number `0 < N ≤ exp (x ^ 99 * b ^ 2)`, with `x = D.x` and `b = D.b` the size
parameters of the data, such that for every twist `ϑ`, path datum `Ψ` on the last path, pair of
forms `y` fixed by the levels at the outer ends of the two halves and prime `p` prime to the norm
`ϑ.normQ` of the places of `ϑ`: if both forms, read as algebraic forms by `lastPathToAlgForm`, have
gauge at most `1` at every point, then `N * lastPathPeriod Ψ y` lies in `embValRing`, the ring of
`p`-integral complex numbers. -/
lemma exists_mul_lastPathPeriod_mem_embValRing : ∃ N ≠ (0 : ℕ),
    N ≤ exp (D.x ^ 99 * D.b ^ 2) ∧
    ∀ {ϑ : D.MFoldTwist} {n : ℕ} {Ψ : EdgeTuple ϑ → ℂ} {y : ∀ z : Bool, D.GridForm z 0 D.m}
      {p : ℕ} [Fact p.Prime] [PadicPlace p],
      IsPathDatum n (TwoGridPath.last D.m).edges Ψ → FixedByOuterLevels ϑ y →
      p.Coprime ϑ.normQ →
      (∀ (z : Bool) (g : Gf D.E (D.LastPathIndex z 0)),
        weylGauge (D.lastPathColumns z) (D.lastPathDetExp z 0) g
          ((D.lastPathToAlgForm z (y z)).val g) ≤ 1) →
      N * lastPathPeriod Ψ y ∈ embValRing := by
  -- By `exists_lastPathPeriod_mem_smul_norm_le` the sum `lastPathPeriod Ψ y` consists of branching
  -- pairings of vectors got from `y` by `m` lifts each. Here `d = liftDenominator` clears each lift
  -- and `M` clears the pairing, so `N = M * d ^ (2 * m)`.
  obtain ⟨M, hM_ne, hM_le, h_pair⟩ := D.exists_norm_mul_lastPathPairing_le_one
  let d : ℕ := D.liftDenominator
  have hd_ne : d ≠ 0 := by simp [d, liftDenominator, NeZero.ne]
  have h_log_d : log d ≤ 2 * Core.numInfPlaces D.E * (2 * D.n D.m * (2 * D.n D.m)) *
      (D.natB * log D.M) + D.natB * D.r ^ 4 * (D.natB * log D.M + log P.d) := by
    simp [d, liftDenominator, log_mul, NeZero.ne]
  have h_log : log (M * (d ^ D.m * d ^ D.m) : ℕ) ≤ D.x ^ 99 * D.b ^ 2 :=
    calc _ = log M + (D.m * log d + D.m * log d) := by simp [log_mul, hM_ne, hd_ne]
      _ ≤ _ := by
        grw [hM_le, h_log_d]
        exact D.le_of_hasLogBound
  refine ⟨M * (d ^ D.m * d ^ D.m), by simp [hM_ne, hd_ne], le_exp_of_log_le h_log,
    fun {ϑ n Ψ y p _ _} hΨ hy hp h_int ↦ ?_⟩
  -- After `j` lifts, `d ^ j • v` has gauge at most `1`.
  let IsCleared (z : Bool) (j : ℕ) (g : Gf D.E (D.LastPathIndex z j)) (v : D.LastPathVector z j) :
    Prop :=
    weylGauge (D.lastPathColumns z) (D.lastPathDetExp z j) g ((d : ℂ) ^ j • v) ≤ 1
  have h_lift (S : EdgeTuple ϑ) (z : Bool) (j : ℕ) (hj : j < D.m) (g : Gf D.E (D.LastPathIndex z j))
      (h : Gf D.E (D.LastPathIndex z (j + 1))) (v : D.LastPathVector z j) (hv : IsCleared z j g v) :
      IsCleared z (j + 1) h
        ((lastPathKernel ϑ z j).jetMap ((lastPathKernel ϑ z j).ω (g, h) (lastPathEdgeDatum S z j))
          v) :=
    le_trans (by simpa [pow_succ, mul_smul] using
      liftDenominator_smul_lastPathEdgeDatum_mem_raises hp S z hj g h ((d : ℂ) ^ j • v)) hv
  have h_end {g : Gf D.E (D.LastPathIndex false D.m)} {v' : D.LastPathVector false D.m}
      {v : D.LastPathVector true D.m} (hv' : IsCleared false D.m g v')
      (hv : IsCleared true D.m (lastPathBlockPoint ϑ g) v) :
      ‖ιₚ ((M * (d ^ D.m * d ^ D.m) : ℕ) * D.lastPathPairing v' v)‖ ≤ 1 := by
    simpa [mul_assoc] using h_pair hp hv' hv
  obtain ⟨L, -, h_sum⟩ := exists_lastPathPeriod_mem_smul_norm_le hΨ hy IsCleared ιₚ h_lift
    (fun z g ↦ by simpa [IsCleared] using h_int z g) h_end
  -- The numbers that `N` makes integral form an additive group, so it contains this multiple sum.
  let A : AddSubgroup ℂ := embValRing.toAddSubgroup.comap
    (AddMonoidHom.mulLeft ((M * (d ^ D.m * d ^ D.m) : ℕ) : ℂ))
  exact A.nsmul_subset .rfl h_sum

/-! ### Sizes on the last path -/

/-- For the trivial twist, the class numbers of the levels along the last path are at most
`exp (x ^ 99 * b ^ 2)`. -/
lemma card_stdClasses_lastPathLevel_le (z : Bool) {j : ℕ} (hj : j ≤ D.m) :
    Nat.card (StdClasses (lastPathLevel (1 : D.MFoldTwist) z j)) ≤ exp (D.x ^ 99 * D.b ^ 2) := by
  have h_level : principalLevel _ (1 * D.M ^ D.natB : ℕ) ≤ lastPathLevel (1 : D.MFoldTwist) z
    j := by
    unfold lastPathLevel
    rw [← show (1 : D.MFoldTwist).normQ = 1 by simp [toAutChar_one_and_toTwist_one_and_Q_one]]
    exact Modulus.principalLevel_le_levelOfSubgroup normQ_mul_M_pow_mem_modulus
  refine (D.card_stdClasses_le_exp_mul_log _ (card_lastPathIndex_le z hj) h_level).trans ?_
  simpa using D.le_of_hasLogBound

/-- For the trivial twist, the theta kernel `lastPathKernel 1 z j` lifts forms from the `j`-th to
the next space of the half `z` of the last path. Let `S` be a tuple of matrices on the edges. The
operator by which the datum `lastPathEdgeDatum S z j` of this edge carries a value `v` at the point
`g` to a value at `h` multiplies the norm `√(weylNormSq ·)` of the `σ`-conjugate of `v` by at most
`exp (x ^ 99 * b ^ 2)`, for each `σ` in `Aut(ℂ)`. -/
lemma sqrt_weylNormSq_lastPathKernel_le (σ : ℂ ≃+* ℂ) (S : EdgeTuple (1 : D.MFoldTwist)) (z : Bool)
    {j : ℕ} (hj : j < D.m) (g : Gf D.E (D.LastPathIndex z j))
    (h : Gf D.E (D.LastPathIndex z (j + 1))) (v : D.LastPathVector z j) :
    √(weylNormSq
        (σ ∘ (lastPathKernel 1 z j).jetMap
          ((lastPathKernel 1 z j).ω (g, h) (lastPathEdgeDatum S z j)) v)) ≤
      exp (D.x ^ 99 * D.b ^ 2) * √(weylNormSq (σ ∘ v)) := by
  have h_liftWeight := D.isLiftWeight_lastPathColumns z j
  -- The datum is the indicator of one matrix, so the operator bound for jets applies with size `1`.
  apply (P.sqrt_weylNormSq_schurJet_le_of_isVacuumCombination
    (P.isVacuumCombination_of_isAdmissibleCombination
    (P.isAdmissibleCombination_vacuumDatum_indicator (S (rowEdge z j D.m)))) g h 1 h_liftWeight
      v).trans
  simp_rw [Parameters.jetSizeBound, schurGrowthExponent, sum_range, ← sum_prod_type']
  -- Each row length is at most their sum, the number of boxes.
  have h_row (q : D.Φ × Fin (card (D.LastPathIndex z j))) :
      diagramWeight (rankAt fun _ : D.Φ ↦ D.LastPathIndex z (j + 1)) (D.lastPathColumns z)
        (q.1, q.2.val) ≤
        D.natB * D.r ^ 4 :=
    (single_le_sum (by simp) (mem_univ q)).trans
      (h_liftWeight.1.sum_diagramWeight_eq_boxes.trans_le
        (boxes_lastPathColumns_le_natB_mul z hj))
  grw [le_abs_self (log (‖σ 1‖ ^ 2 / P.bigOmega D.towerExp)), one_mul, h_row]
  gcongr
  -- 'le_of_hasLogBound' uses these two bounds for the ranks as local instances.
  have := D.hasLogUpper_of_le (card_lastPathIndex_le z hj)
  have := D.hasLogUpper_of_le (card_lastPathIndex_le z hj.le)
  simpa using D.le_of_hasLogBound

/-- Conjugates of `Ξ = lastPathPeriod Ψ y` for the trivial twist. Let `Ψ` be a path datum on the
last path and `y` a pair of forms fixed by the levels at the outer ends of the two halves, whose
values as algebraic forms have `σ`-conjugates of squared norm at most `B false` and `B true`. Then
`‖σ Ξ‖` is at most `exp (x ^ 200 * b ^ 2) * √(B false) * √(B true)`, with `x = D.x` the length of
the prime sum and `b = D.b` the weight at the `b`-places. -/
lemma norm_lastPathPeriod_le {Ψ : EdgeTuple (1 : D.MFoldTwist) → ℂ}
    {y : ∀ z : Bool, D.GridForm z 0 D.m}
    (hΨ : IsPathDatum (lastPathBound (1 : D.MFoldTwist)) (TwoGridPath.last D.m).edges Ψ)
    (hy : D.FixedByOuterLevels 1 y) (σ : ℂ ≃+* ℂ) {B : Bool → ℝ}
    (hB : ∀ (z : Bool) (g : Gf D.E (D.LastPathIndex z 0)),
      weylNormSq (σ ∘ (D.lastPathToAlgForm z (y z)).val g) ≤ B z) :
    ‖σ (lastPathPeriod Ψ y)‖ ≤ exp (D.x ^ 200 * D.b ^ 2) * √(B false) * √(B true) := by
  -- By `exists_lastPathPeriod_mem_smul_norm_le` the sum `lastPathPeriod Ψ y` consists of branching
  -- pairings of vectors got from `y` by `m` lifts each. Each lift costs a factor `G` in norm and
  -- each class number is at most `G`.
  let G : ℝ := exp (D.x ^ 99 * D.b ^ 2)
  -- After `j` lifts the norm is at most `G ^ j` times its bound at the start.
  let IsSmall (z : Bool) (j : ℕ) (v : D.LastPathVector z j) : Prop :=
    √(weylNormSq (σ ∘ v)) ≤ G ^ j * √(B z)
  have h_lift (S : EdgeTuple (1 : D.MFoldTwist)) (z : Bool) (j : ℕ) (hj : j < D.m)
      (g : Gf D.E (D.LastPathIndex z j)) (h : Gf D.E (D.LastPathIndex z (j + 1)))
        (v : D.LastPathVector z j)
      (hv : IsSmall z j v) :
      IsSmall z (j + 1)
        ((lastPathKernel 1 z j).jetMap ((lastPathKernel 1 z j).ω (g, h) (lastPathEdgeDatum S z j))
          v) :=
    calc _ ≤ G * √(weylNormSq (σ ∘ v)) := D.sqrt_weylNormSq_lastPathKernel_le σ S z hj g h v
      _ ≤ G * (G ^ j * √(B z)) := by gcongr
      _ = G ^ (j + 1) * √(B z) := by ring
  let C : ℕ := ((D.natB * D.r ^ 4) ^ (D.natB * D.r ^ 4)) ^ 3
  let R : ℝ := C * (G ^ D.m * √(B false)) * (G ^ D.m * √(B true))
  -- 'C' bounds the branching pairing, so 'R' bounds each term of the sum.
  have h_end {v' : D.LastPathVector false D.m} {v : D.LastPathVector true D.m}
      (hv' : IsSmall false D.m v') (hv : IsSmall true D.m v) :
      ‖σ (1 * D.lastPathPairing v' v)‖ ≤ R :=
    calc _ = ‖(σ ∘ v') ⬝ᵥ D.lastPathBranching.map (↑) *ᵥ (σ ∘ v)‖ := by
          simp only [one_mul, LinearMap.compl₂_apply, Matrix.mulVecLin_apply,
            dotProductBilin_apply_apply, dotProduct, mulVec, map_sum, map_mul, map_intCast,
            Matrix.map_apply, Function.comp_apply]
      _ ≤ _ := D.norm_dotProduct_lastPathBranching_mulVec_le
        (boxes_lastPathColumns_le_natB_mul true le_rfl) _ _
      _ ≤ R := mul_le_mul (mul_le_mul_of_nonneg_left hv' (Nat.cast_nonneg _)) hv (sqrt_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg (exp_pos _).le _) (sqrt_nonneg _)))
  obtain ⟨L, hL, h_sum⟩ := exists_lastPathPeriod_mem_smul_norm_le hΨ hy (fun z j _ ↦ IsSmall z j)
    σ.toRingHom h_lift
    (fun z g ↦ by simp [IsSmall, sqrt_le_sqrt, hB]) h_end
  -- The number of terms is `L` times the `2 * m + 1` class numbers of the nodes `j < m` of the
  -- half `true` and `j ≤ m` of the half `false`; `(!z).toNat` counts the extra node.
  set n : ℕ := L * ∏ z : Bool, ∏ j ∈ range (D.m + (!z).toNat),
    Nat.card (StdClasses (lastPathLevel (1 : D.MFoldTwist) z j)) with hn
  have h_prod (z : Bool) (k : ℕ) (hk : k ≤ D.m + 1) :
      ∏ j ∈ range k, (Nat.card (StdClasses (lastPathLevel (1 : D.MFoldTwist) z j)) : ℝ) ≤ G ^
        k :=
    calc ∏ j ∈ range k, (Nat.card (StdClasses (lastPathLevel (1 : D.MFoldTwist) z j)) : ℝ)
      _ ≤ ∏ _j ∈ range k, G := by
          gcongr with j hj
          exact D.card_stdClasses_lastPathLevel_le z
            (Nat.le_of_lt_succ ((mem_range.1 hj).trans_le hk))
      _ = G ^ k := by rw [prod_const, card_range]
  have hn_le : n ≤ L * (G ^ D.m * G ^ (D.m + 1)) := by
    grw [← h_prod true D.m (by simp), ← h_prod false (D.m + 1) le_rfl]
    simp [hn, -Nat.card_eq_fintype_card]
  have h_const : L * (G ^ D.m * G ^ (D.m + 1)) * (C * G ^ D.m * G ^ D.m) ≤
      exp (D.x ^ 200 * D.b ^ 2) := by
    have hLC : (L : ℝ) * C ≤ exp (D.x ^ 199 * D.b ^ 2) := by
      have h_normQ : (1 : D.MFoldTwist).normQ = 1 := by
        simp [toAutChar_one_and_toTwist_one_and_Q_one]
      grw [hL]
      refine le_exp_of_log_le ?_
      rw [log_mul (by simp [lastPathBound, NeZero.ne]) (by simp [C, NeZero.ne]), lastPathBound,
        Nat.cast_mul, Nat.cast_mul,
        log_mul (by simp [NeZero.ne]) (by simp [NeZero.ne]),
        log_mul (by simp [NeZero.ne]) (by simp [NeZero.ne])]
      simp only [C, vectorCountBound, edgeMatrixCountBound, card_residueRing_twistModulus,
        prod_q_chosenPlace, h_normQ, mul_one, Nat.cast_pow, log_pow, Nat.cast_mul,
        Nat.cast_ofNat]
      exact D.le_of_hasLogBound
    have hG : G ^ (D.m + (D.m + 1) + D.m + D.m) =
        exp ((D.m + (D.m + 1) + D.m + D.m : ℕ) * (D.x ^ 99 * D.b ^ 2)) :=
      (exp_natCast_mul _ _).symm
    calc (L : ℝ) * (G ^ D.m * G ^ (D.m + 1)) * (C * G ^ D.m * G ^ D.m)
      _ = (L * C) * G ^ (D.m + (D.m + 1) + D.m + D.m) := by ring
      _ ≤ exp (D.x ^ 199 * D.b ^ 2) *
            exp ((D.m + (D.m + 1) + D.m + D.m : ℕ) * (D.x ^ 99 * D.b ^ 2)) := by
          rw [hG]; gcongr
      _ = exp (D.x ^ 199 * D.b ^ 2 +
            (D.m + (D.m + 1) + D.m + D.m : ℕ) * (D.x ^ 99 * D.b ^ 2)) := (exp_add _ _).symm
      _ ≤ exp (D.x ^ 200 * D.b ^ 2) := exp_le_exp.2 D.le_of_hasLogBound
  obtain ⟨a, ha, ha_sum⟩ := Set.mem_nsmul_iff_sum.1 h_sum
  calc _ = ‖∑ i, σ (a i)‖ := by rw [← ha_sum, map_sum]
    _ ≤ n * R :=
      (norm_sum_le_of_le univ fun i _ ↦ (by
        have h := ha i
        rw [Set.mem_ofPred_eq, one_mul] at h
        exact h : ‖σ (a i)‖ ≤ R)).trans_eq
        (by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul])
    _ = n * (C * G ^ D.m * G ^ D.m) * √(B false) * √(B true) := by ring
    _ ≤ exp (D.x ^ 200 * D.b ^ 2) * √(B false) * √(B true) := by grw [hn_le, h_const]

/-! ### Going back through the turns -/

/-- There are constants `c ϑ`, path data `Ψ ϑ` on the last path, a number `β` and a restriction map
`r` from `gridLevelForms` onto the forms on `Y₀` of principal level at the chosen places, such that
the index of the level `levelY ϑ m` times the pairing of `y'` with the chain of lifts of `r φ`
equals `β * Ξ / c ϑ`. Here `Ξ` is `lastPathPeriod` of `Ψ ϑ` at the pair `(y', φ)`, the sum over the
tuples `S` of matrices on the last path of `Ψ ϑ S` times the integral of the pairing of the lifts of
`y'` and `φ` along its two halves. `HasAbsUpToNormPower c f` says that `‖c ϑ‖²` is
`C * ϑ.normQ ^ k * (f ϑ) ^ 2`, with `C` and `k` independent of `ϑ` and `ϑ.normQ` the product of the
norms of the places in the set `Q` of `ϑ`, and `f` is the product over the `m ^ 2` turns of
`turnRatio i j`, a product of ratios of Hecke values at the twist `ϑ`. -/
lemma exists_integral_lowerChainUpTo_eq_lastPathPeriod : ∃ c : D.MFoldTwist → ℂˣ,
    D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
      (∏ i ∈ range D.m, ∏ j ∈ range D.m, D.turnRatio i j) ∧
    ∃ Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ,
      (∀ ϑ : D.MFoldTwist, IsPathDatum (lastPathBound ϑ) (TwoGridPath.last D.m).edges (Ψ ϑ)) ∧
      ∃ (β : ℂ) (r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)),
        r.range = ⊤ ∧
        ∀ (ϑ : D.MFoldTwist) (y' : D.GridForm false 0 D.m) (φ : D.gridLevelForms D.m),
          stdLevelIndex (D.levelY ϑ D.m) *
              ∫ x : New.G D.E (D.signsY D.m),
                y' x * D.lowerChainUpTo ϑ D.m (r φ) x ∂(D.spaceY D.m).quotMeasure =
            β * (lastPathPeriod (Ψ ϑ) (fun z : Bool ↦ z.rec y' φ.val) / c ϑ) := by
  -- Start from the data of the first path and carry them through the turns to the last path; a
  -- multiple of the sum `lastPathPeriod` of the resulting data is then the period of the first
  -- path.
  obtain ⟨Ψ₀, hΨ₀, g, α, r, hr_onto, h_first⟩ := D.exists_isPathDatum_first
  obtain ⟨c, hc, h_turns⟩ := D.exists_transfersPeriods_first_last
  obtain ⟨Ψ, hΨ, h_back⟩ := h_turns _ Ψ₀ hΨ₀
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, ∀ x : D.PeriodTriple, gridPeriod (.first D.m) Ψ₀ g x =
      β * ((lastPathPeriod (Ψ x.1) fun z ↦ z.rec x.2.1 x.2.2) / triangleGLCard false x.1 D.m / c
        x.1) :=
    h_back _ (D.isProportional_lastPathPeriod Ψ) g
  rw [prod_product' (range D.m) (range D.m) D.turnRatio] at hc
  refine ⟨c, hc, Ψ, hΨ, α * β, r, hr_onto, fun ϑ y' φ ↦ ?_⟩
  have h_index : triangleGLCard false ϑ D.m = stdLevelIndex (D.levelY ϑ D.m) :=
    LevelPlaces.card_GL_levelModulus (D.Y D.m) (D.levelPlaces ϑ)
  rw [h_first, hβ, ← h_index]
  field [show (triangleGLCard false ϑ D.m : ℂ) ≠ 0 from Nat.cast_ne_zero.2 Fintype.card_ne_zero]

/-! ### Values of a form from its pairings -/

/-- The space of values of the algebraic forms on `Y_m` of the dual weight. -/
abbrev DualVector : Type := WeylIndex (D.Y D.m) (D.lastPathColumns false) → ℂ

/-- The integer matrix of the invariant pairing of the dual weight on `Y_m`, that of the conjugate
forms, with the weight on `Y_m`. -/
def dualPairing : Matrix (WeylIndex (D.Y D.m) (D.lastPathColumns false))
    (WeylIndex (D.Y D.m) D.columnsY) ℤ :=
  (exists_isDualPairing_of_isHCParam D.isHCParam_paramY
    (D.isHCParam_lastPathColumns false zero_le)).choose

/-- The matrix `dualPairing` is a duality between the weight `(columnsY, lastEntry m)` on `Y_m` and
its dual weight `(lastPathColumns false, lastPathDetExp false 0)` (columns of the diagram, exponent
of the determinant), normalised at the highest vector of the parameter `paramY m` of `Y_m`. -/
lemma isDualPairing_dualPairing : IsDualPairing D.columnsY (D.lastPathColumns false)
    (D.lastEntry D.m) (D.lastPathDetExp false 0) (D.paramY D.m) D.dualPairing :=
  (exists_isDualPairing_of_isHCParam D.isHCParam_paramY
    (D.isHCParam_lastPathColumns false zero_le)).choose_spec

/-- The hook number of the dual of the weight on `Y_m`: the square norm of the highest weight
polynomial for the pairing by differentiation, a positive integer. -/
abbrev dualHook : ℤ := hookNumber (D.lastPathColumns false) (rankAt fun _ : D.Φ ↦ D.Y D.m)

/-- The product of the hook number of the dual weight, `exp (x ^ 99 * b ^ 2)` and
`exp (x ^ 200 * b ^ 2)` is at most `exp (x ^ 201 * b ^ 2)`. -/
lemma dualHook_mul_exp_le :
    D.dualHook * exp (D.x ^ 99 * D.b ^ 2) * exp (D.x ^ 200 * D.b ^ 2) ≤
      exp (D.x ^ 201 * D.b ^ 2) := by
  have h_hook : (D.dualHook : ℝ) ≤ (((D.natB * D.r ^ 4) ^ (D.natB * D.r ^ 4)) ^ 3 : ℕ) := by
    exact_mod_cast hookNumber_le (boxes_lastPathColumns_le_natB_mul false zero_le)
  rw [mul_assoc, ← exp_add]
  grw [h_hook]
  refine le_exp_of_log_le ?_
  rw [log_mul (by simp [NeZero.ne]) (exp_pos _).ne', log_exp, Nat.cast_pow, log_pow,
    Nat.cast_pow, log_pow]
  exact D.le_of_hasLogBound

/-- Let `ζ` be a vector of the weight on `Y_m`. Suppose that its pairing by `dualPairing` with every
integer vector `w` of the dual weight is `D.dualHook` times an element of `embValRing`. Then every
coordinate of `ζ` is `p`-integral. -/
lemma mem_embValRing_of_dualPairing_eq_dualHook_mul {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {ζ : WeylIndex (D.Y D.m) D.columnsY → ℂ}
    (hζ : ∀ w : WeylIndex (D.Y D.m) (D.lastPathColumns false) → ℤ, ∃ a ∈ embValRing,
      (fun k : WeylIndex (D.Y D.m) (D.lastPathColumns false) ↦ (w k : ℂ)) ⬝ᵥ
        D.dualPairing.map (↑) *ᵥ ζ = D.dualHook * a)
    (i : WeylIndex (D.Y D.m) D.columnsY) : ζ i ∈ embValRing := by
  -- The hook number times `ζ i` is the pairing of `ζ` with the `i`-th row of an integer matrix `C`
  -- with `C * dualPairing = dualHook • 1`.
  obtain ⟨C, hC⟩ : ∃ C : Matrix _ _ ℤ, ∀ v : WeylIndex (D.Y D.m) D.columnsY → ℂ,
      C.map (↑) *ᵥ D.dualPairing.map (↑) *ᵥ v = (D.dualHook : ℂ) • v :=
    D.isDualPairing_dualPairing.exists_mul_eq_hookNumber
  obtain ⟨a, ha, h_pair⟩ := hζ (C i)
  have h_coord : (D.dualHook : ℂ) * ζ i = D.dualHook * a := (congrFun (hC ζ) i).symm.trans h_pair
  rwa [mul_left_cancel₀ (by simp) h_coord]

/-- Let `σ` be an automorphism of `ℂ`, `ζ` a vector of the weight on `Y_m` and `K ≥ 0`. Suppose that
for each `v : D.DualVector`, the `σ`-conjugate of the pairing `v ⬝ᵥ dualPairing *ᵥ ζ` has absolute
value at most `K * √(weylNormSq (σ ∘ v))`. Then `weylNormSq (σ ∘ ζ) ≤ K ^ 2`. -/
lemma weylNormSq_le_of_dualPairing (σ : ℂ ≃+* ℂ) {ζ : WeylIndex (D.Y D.m) D.columnsY → ℂ} {K : ℝ}
    (hK : 0 ≤ K)
    (hζ : ∀ v : D.DualVector,
      ‖σ (v ⬝ᵥ D.dualPairing.map (↑) *ᵥ ζ)‖ ≤ K * √(weylNormSq (σ ∘ v))) :
    weylNormSq (σ ∘ ζ) ≤ K ^ 2 := by
  -- The squared norm of `σ ∘ ζ` is its pairing with a vector `w` of the same norm.
  obtain ⟨w, hw_norm, hw_pair⟩ : ∃ w : D.DualVector, weylNormSq w = weylNormSq (σ ∘ ζ) ∧
      ∀ u : D.DualVector, u ⬝ᵥ D.dualPairing.map (↑) *ᵥ (σ ∘ ζ) = gramForm w u :=
    D.isDualPairing_dualPairing.exists_eq_gramForm (σ ∘ ζ)
  have h_eq : (weylNormSq w : ℂ) = σ ((σ.symm ∘ w) ⬝ᵥ D.dualPairing.map (↑) *ᵥ ζ) :=
    calc _ = w ⬝ᵥ D.dualPairing.map (↑) *ᵥ (σ ∘ ζ) :=
          (GL.coe_weylNormSq w).trans ((gramForm_apply w w).symm.trans (hw_pair w).symm)
      _ = _ := by
          simp only [dotProduct, mulVec, map_sum, map_mul, map_intCast, Matrix.map_apply,
            Function.comp_apply, RingEquiv.apply_symm_apply]
  have h_le : weylNormSq w ≤ K * √(weylNormSq w) :=
    calc weylNormSq w = ‖(weylNormSq w : ℂ)‖ := by simp [abs_of_nonneg]
      _ ≤ K * √(weylNormSq w) := by
        rw [h_eq]
        simpa [Function.comp_def] using hζ (σ.symm ∘ w)
  have h_root : √(weylNormSq w) ≤ K :=
    div_sqrt.ge.trans (div_le_of_le_mul₀ (sqrt_nonneg _) hK h_le)
  rw [← hw_norm]
  exact (sqrt_le_iff.1 h_root).2

section Delta

variable {P : Parameters} {D : Data P} (ϑ : D.MFoldTwist) (x : Gf D.E (D.Y D.m)) (v : D.DualVector)

/-- The algebraic form `δ_x(v)` of the dual weight on `Y_m`, of level `levelY ϑ m`, supported on the
class of `x`. -/
def lastPathDelta :
    levelSpace (algFormRep (D.lastPathColumns false) (D.lastPathDetExp false 0)) (D.levelY ϑ D.m) :=
  deltaForm stdEmbFin
    ((stdSpace D.E (D.Y D.m)).weightRep (D.lastPathColumns false) (D.lastPathDetExp false 0)) 1 x v

/-- The form `δ_x(v)` as a conjugate form on `Y_m`. -/
def lastPathConjDelta : D.GridForm false 0 D.m :=
  (D.lastPathToAlgForm false).symm (lastPathDelta ϑ x v).val

lemma lastPathToAlgForm_lastPathConjDelta :
    D.lastPathToAlgForm false (lastPathConjDelta ϑ x v) = (lastPathDelta ϑ x v).val :=
  (D.lastPathToAlgForm false).apply_symm_apply _

/-- Let `ϑ` be an `m`-fold twist, `x` a finite point of `Y_m`, `v` a vector of the dual weight,
`δ = lastPathConjDelta ϑ x v` the delta form on `Y_m` with value `v` on the class of `x`, and `φ` a
form in `gridLevelForms`. Then the pair `(δ, φ)` satisfies `FixedByOuterLevels ϑ`: as algebraic
forms, `δ` is fixed by the integral points of `Y_m` congruent to `1` modulo `gridModulus ϑ`, and `φ`
by the level `lastPathLevel ϑ true 0` of `Ỹ^m_0`, the integral points congruent to `1` modulo the
part of that modulus that does not depend on `ϑ`. -/
lemma fixedByOuterLevels_lastPathConjDelta (φ : D.gridLevelForms D.m) :
    FixedByOuterLevels ϑ fun z : Bool ↦ z.rec (lastPathConjDelta ϑ x v) φ.val := by
  -- `lastPathLevel ϑ false 0` is the principal level of `gridModulus ϑ`, which lies in `levelY`.
  have h_level : lastPathLevel ϑ false 0 ≤ D.levelY ϑ D.m := by
    refine Subgroup.map_mono fun k hk ↦ funext fun i ↦ Units.ext ?_
    -- Reduction modulo the place of index `i` factors through reduction modulo `gridModulus ϑ`.
    have h_red : (gridModulus ϑ).reductionGL k = 1 := hk
    have h_place : (D.levelPlaces ϑ.toTameChar).placeAt i ∈ (gridModulus ϑ).places :=
      places_levelModulus.ge ⟨i, rfl⟩
    exact (Rows.reductionGL_map_modulusResidue _ h_place k).symm.trans <| by
      rw [h_red, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
      rfl
  let e := (D.gridSpace 0 true 0 D.m).algFormEquiv (D.isHCParam_lastPathColumns true zero_le)
    (principalLevel (D.LastPathIndex true 0) D.gridLevelGen)
  have h_symm : (e.symm φ).val = D.lastPathToAlgForm true φ.val := rfl
  refine Bool.forall_bool.2 ⟨?_, ?_⟩
  · change D.lastPathToAlgForm false (lastPathConjDelta ϑ x v) ∈ _
    rw [lastPathToAlgForm_lastPathConjDelta]
    exact fun k ↦ (lastPathDelta ϑ x v).property ⟨k.val, h_level k.property⟩
  · change D.lastPathToAlgForm true φ.val ∈ _
    rw [← h_symm]
    exact fun k ↦ (e.symm φ).property ⟨k.val, lastPathLevel_le_principalLevel ϑ true 0 k.property⟩

/-- Pairing with a delta form reads a value. Let `ϑ` be an `m`-fold twist, `x` a finite point of
`Y_m`, `v` a vector of the dual weight and `y` a form on `Y₀`. The index of the level times the
integral of the delta form `δ_x(v) = lastPathConjDelta ϑ x v` against the chain of lifts
`lowerChainUpTo ϑ m y` is the pairing of `v` with the value at `x` of `lowerChain ϑ y`, the same
chain with values in algebraic forms, divided by the dimension of the weight.

The division by the dimension of the weight is the factor in Schur's orthogonality relations for
matrix coefficients of irreducible representations of compact groups, here for the weight on `Y_m`
paired with its dual. -/
lemma integral_lastPathConjDelta_mul (y : D.principalForms (D.spaceY 0)) :
    stdLevelIndex (D.levelY ϑ D.m) *
        ∫ g : New.G D.E (D.signsY D.m),
          lastPathConjDelta ϑ x v g * D.lowerChainUpTo ϑ D.m y g ∂(D.spaceY D.m).quotMeasure =
      (v ⬝ᵥ D.dualPairing.map (↑) *ᵥ (D.lowerChain ϑ y).val x) /
        card (WeylIndex (D.Y D.m) D.columnsY) := by
  have h_fix (k : Gf D.E (D.Y D.m)) (hk : k ∈ D.levelY ϑ D.m) :
      algFormRep D.columnsY (D.lastEntry D.m) k (D.lowerChain ϑ y) = D.lowerChain ϑ y :=
    (D.lowerChainAtLevel ϑ y).algFormRep_eq_self_of_mem hk
  -- The integral is a class sum, which the delta form reduces to its term at `x`.
  let L (g : Gf D.E (D.Y D.m)) : D.DualVector →+ ℂ :=
    .mk' (fun w ↦ w ⬝ᵥ D.dualPairing.map (↑) *ᵥ (D.lowerChain ϑ y).val g) fun w w' ↦
      add_dotProduct w w' _
  let f (g : Gf D.E (D.Y D.m)) : ℂ := L g ((lastPathDelta ϑ x v).val.val g)
  have h_integral : ∫ g : New.G D.E (D.signsY D.m),
      lastPathConjDelta ϑ x v g * D.lowerChainUpTo ϑ D.m y g ∂(D.spaceY D.m).quotMeasure =
        (card (WeylIndex (D.Y D.m) D.columnsY) * stdLevelIndex (D.levelY ϑ D.m) : ℂ)⁻¹ *
          classIntegral stdRatPoints (D.levelY ϑ D.m) f := by
    have h_chain : (D.lowerChainUpTo ϑ D.m y).val =
        ofAlgForm (D.paramY D.m) (D.signsY D.m) (D.lowerChain ϑ y) :=
      (ofAlgForm_toAlgForm D.isHCParam_paramY (D.lowerChainUpTo ϑ D.m y)).symm
    have h_delta : (lastPathConjDelta ϑ x v).val =
        ofAlgForm (-D.paramY D.m) (D.signsY D.m) (lastPathDelta ϑ x v).val := rfl
    let B (g : Gf D.E (D.Y D.m)) : (WeylIndex (D.Y D.m) D.columnsY → ℂ) →ₗ[ℂ] ℂ :=
      (dotProductBilin ℂ ℂ).compl₂ (D.dualPairing.map (↑)).mulVecLin ((lastPathDelta ϑ x v).1.1 g)
    have h_f : (fun g ↦ B g ((D.lowerChain ϑ y).val g)) = f :=
      funext fun g ↦ by
        simp only [B, f, L, AddMonoidHom.mk'_apply, LinearMap.compl₂_apply, Matrix.mulVecLin_apply,
          dotProductBilin_apply_apply]
    refine (MeasureTheory.integral_congr_ae (.of_forall fun (g : New.G D.E (D.signsY D.m)) ↦
      congrArg₂ (· * ·) (congrFun h_delta g) (congrFun h_chain g))).trans ?_
    rw [← h_f]
    exact integral_mul_eq_classIntegral (V := D.spaceY D.m) D.isHCParam_paramY (D.levelY ϑ D.m)
      (isAutomorphic_algFormCoeff (lastPathDelta ϑ x v).val) B
      (D.isDualPairing_dualPairing.ofAlgForm_eq_bilin (D.signsY D.m) (lastPathDelta ϑ x v).val)
  have h_sum : classSum stdRatPoints (D.levelY ϑ D.m) f = L x v := by
    refine classSum_deltaForm L fun γ k ↦ ?_
    have h_value : (D.lowerChain ϑ y).val ((stdSpace D.E (D.Y D.m)).embFin γ * x * k.val) =
        (stdSpace D.E (D.Y D.m)).weightRep D.columnsY (D.lastEntry D.m) γ
          ((D.lowerChain ϑ y).val x) :=
      (congrFun (congrArg Subtype.val (h_fix k.val k.property)) _).trans
        ((D.lowerChain ϑ y).property.2 γ x)
    simp only [MonoidHom.one_apply, one_smul, L, AddMonoidHom.mk'_apply, h_value]
    exact D.isDualPairing_dualPairing.invariant ℂ _ v ((D.lowerChain ϑ y).val x)
  rw [h_integral, classIntegral_eq_classSum, h_sum]
  · simp [L, field, -Fintype.card_pi]
  · intro k hk g
    have h_left : (lastPathDelta ϑ x v).val.val (g * k) = (lastPathDelta ϑ x v).val.val g :=
      (congrFun (congrArg Subtype.val ((lastPathDelta ϑ x v).property ⟨k, hk⟩)) g).trans
        (one_smul ℂ _)
    have h_right : (D.lowerChain ϑ y).val (g * k) = (D.lowerChain ϑ y).val g :=
      congrFun (congrArg Subtype.val (h_fix k hk)) g
    simp only [f, L, AddMonoidHom.mk'_apply, h_left, h_right]

/-- If `x` is integral above `p` and `w` is an integer vector, then the delta form `δ_x(w)` has
`p`-adic gauge at most `1` at every point. -/
lemma weylGauge_lastPathConjDelta_le_one {p : ℕ} [Fact p.Prime] [PadicPlace p]
    (hx : x ∈ integralAbove (D.Y D.m) p)
    (w : WeylIndex (D.Y D.m) (D.lastPathColumns false) → ℤ) (g : Gf D.E (D.Y D.m)) :
    weylGauge (D.lastPathColumns false) (D.lastPathDetExp false 0) g
      ((D.lastPathToAlgForm false (lastPathConjDelta ϑ x fun i ↦ w i)).val g) ≤ 1 := by
  rw [lastPathToAlgForm_lastPathConjDelta]
  refine (weylGauge_deltaForm_le (n := D.Y D.m) (by simp)).trans ?_
  simp [IsUltrametricDist.norm_intCast_le_one, weylGauge_le_one_iff, hx]

/-- The conjugates of the values of the delta form `δ_x(v)` are no longer than those of `v`, because
the level `levelY ϑ m` is sufficiently small. -/
lemma weylNormSq_lastPathConjDelta_le (σ : ℂ ≃+* ℂ) (g : Gf D.E (D.Y D.m)) :
    weylNormSq (σ ∘ (D.lastPathToAlgForm false (lastPathConjDelta ϑ x v)).val g) ≤
      weylNormSq (σ ∘ v) := by
  rw [lastPathToAlgForm_lastPathConjDelta]
  refine (weylNormSq_deltaForm_le (n := D.Y D.m) (by simp) σ x v g).trans ?_
  simp [D.classAut_eq_bot_of_le_chosenLevel (levelY_le_chosenLevel ..)
    (card_lastPathIndex_le false zero_le : card (D.LastPathIndex false 0) ≤ 2 * D.n D.m)]

end Delta

/-- There are constants `c ϑ`, whose modulus is, up to a constant and a fixed power of the norm
`ϑ.normQ` of the places of `ϑ`, the product over the `m ^ 2` turns of `turnRatio`, functions `Ψ ϑ`
of the matrices on the edges that are path data on the last path, a number `β` and a restriction map
`r` from `gridLevelForms` onto the forms on `Y₀`, such that the pairing of `v` with the value at `x`
of `(c ϑ / c 1) • lowerChain ϑ (r φ)` is `β` times `lastPathPeriod` at the pair `(δ_x(v), φ)`: the
sum over the tuples `S` of `Ψ ϑ S` times the integrated pairing of the lifts of `φ` and of the delta
form `δ_x(v) = lastPathConjDelta ϑ x v` along the two halves of the last path. -/
lemma exists_dualPairing_eq_mul_lastPathPeriod : ∃ c : D.MFoldTwist → ℂˣ,
    D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
      (∏ i ∈ range D.m, ∏ j ∈ range D.m, D.turnRatio i j) ∧
    ∃ Ψ : ∀ ϑ : D.MFoldTwist, EdgeTuple ϑ → ℂ,
      (∀ ϑ : D.MFoldTwist, IsPathDatum (lastPathBound ϑ) (TwoGridPath.last D.m).edges (Ψ ϑ)) ∧
      ∃ (β : ℂ) (r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)),
        r.range = ⊤ ∧
        ∀ (ϑ : D.MFoldTwist) (φ : D.gridLevelForms D.m) (x : Gf D.E (D.Y D.m))
          (v : D.DualVector),
          v ⬝ᵥ D.dualPairing.map (↑) *ᵥ ((c ϑ / c 1 : ℂ) • D.lowerChain ϑ (r φ)).val x =
            β * lastPathPeriod (Ψ ϑ) fun z : Bool ↦ z.rec (lastPathConjDelta ϑ x v) φ.val := by
  obtain ⟨c, hc, Ψ, hΨ, β, r, hr_onto, h_period⟩ :=
    D.exists_integral_lowerChainUpTo_eq_lastPathPeriod
  refine ⟨c, hc, Ψ, hΨ, card (WeylIndex (D.Y D.m) D.columnsY) * β / c 1, r, hr_onto,
    fun ϑ φ x v ↦ ?_⟩
  have h_value :
      (v ⬝ᵥ D.dualPairing.map (↑) *ᵥ (D.lowerChain ϑ (r φ)).val x) / card
        (WeylIndex (D.Y D.m) D.columnsY) =
        β * (lastPathPeriod (Ψ ϑ) (fun z ↦ z.rec (lastPathConjDelta ϑ x v) φ.val) / c ϑ) :=
    (integral_lastPathConjDelta_mul ϑ x v (r φ)).symm.trans (h_period ϑ _ φ)
  simpa [field, mul_comm (c ϑ : ℂ), mulVec_smul, -Fintype.card_pi] using h_value

/-! ### Integrality and size of the values -/

/-- There are constants `c ϑ` whose modulus is, up to a constant and a fixed power of the norm
`ϑ.normQ` of the places of `ϑ`, the product of the ratios `turnRatio`, a restriction map `r` from
`gridLevelForms` onto the forms on `Y₀` and a number `s ≠ 0` with two properties. (a) If the
algebraic form `lastPathToAlgForm true φ` of `φ` has `p`-integral values at a prime `p` that does
not divide `ϑ.normQ`, then `(c ϑ / c 1) • lowerChainAtLevel ϑ (s • r φ)` is in `integralForms`, the
forms with `p`-integral values. (b) For the trivial twist and `σ` in `Aut(ℂ)`, if the `σ`-conjugates
of the values of that algebraic form have squared norm `weylNormSq` at most `B`, then those of
`lowerChain 1 (s • r φ)` have squared norm at most `exp (2 * x ^ 201 * b ^ 2) * B`. -/
lemma exists_lowerChain_integral_and_weylNormSq_le : ∃ c : D.MFoldTwist → ℂˣ,
    D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
      (∏ i ∈ range D.m, ∏ j ∈ range D.m, D.turnRatio i j) ∧
    ∃ (r : D.gridLevelForms D.m →ₗ[ℂ] D.principalForms (D.spaceY 0)) (s : ℂ),
      r.range = ⊤ ∧ s ≠ 0 ∧
      (∀ (ϑ : D.MFoldTwist) (p : ℕ) [Fact p.Prime] (place : PadicPlace p)
          (φ : D.gridLevelForms D.m),
        p.Coprime ϑ.normQ → GaugeLe 1 1 (D.lastPathToAlgForm true φ.val) →
        (c ϑ / c 1 : ℂ) • D.lowerChainAtLevel ϑ (s • r φ) ∈ integralForms (l := p) place) ∧
      ∀ (σ : ℂ ≃+* ℂ) (φ : D.gridLevelForms D.m) (B : ℝ),
        (∀ g : Gf D.E (D.LastPathIndex true 0),
          weylNormSq (σ ∘ (D.lastPathToAlgForm true φ.val).val g) ≤ B) →
        ∀ g : Gf D.E (D.Y D.m),
          weylNormSq (σ ∘ (D.lowerChain .one (s • r φ)).val g) ≤
            exp (2 * D.x ^ 201 * D.b ^ 2) * B := by
  obtain ⟨c, hc, Ψ, hΨ, β, r, hr_onto, h_period⟩ :=
    D.exists_dualPairing_eq_mul_lastPathPeriod
  obtain ⟨N, hN_ne, hN_le, h_integral⟩ := D.exists_mul_lastPathPeriod_mem_embValRing
  -- If `β = 0` all pairings vanish and `s = 1`, `ε = 0` will do; otherwise `s` turns `β` into the
  -- hook number times `N`.
  let s : ℂ := if β = 0 then 1 else D.dualHook * N / β
  let ε : ℂ := if β = 0 then 0 else 1
  have hs_ne : s ≠ 0 := by
    by_cases hβ0 : β = 0
    · simp [s, hβ0]
    · simp [s, hβ0, hN_ne]
  have hs : s * β = D.dualHook * (ε * N) := by
    by_cases hβ0 : β = 0 <;> simp [s, ε, hβ0]
  let Ξ (ϑ : D.MFoldTwist) (φ : D.gridLevelForms D.m) (x : Gf D.E (D.Y D.m))
      (v : D.DualVector) : ℂ :=
    lastPathPeriod (Ψ ϑ) fun z ↦ z.rec (lastPathConjDelta ϑ x v) φ.val
  have h_pair (ϑ : D.MFoldTwist) (φ : D.gridLevelForms D.m) (x : Gf D.E (D.Y D.m))
      (v : D.DualVector) :
      v ⬝ᵥ D.dualPairing.map (↑) *ᵥ ((c ϑ / c 1 : ℂ) • D.lowerChain ϑ (s • r φ)).val x =
        D.dualHook * (ε * (N * Ξ ϑ φ x v)) :=
    calc _ = s * (v ⬝ᵥ D.dualPairing.map (↑) *ᵥ ((c ϑ / c 1 : ℂ) • D.lowerChain ϑ (r φ)).1 x) := by
          rw [map_smul, smul_comm, Submodule.coe_smul_of_tower, Pi.smul_apply, mulVec_smul,
            dotProduct_smul, smul_eq_mul]
      _ = s * (β * Ξ ϑ φ x v) := by rw [h_period]
      _ = _ := by rw [← mul_assoc, hs, mul_assoc, mul_assoc]
  refine ⟨c, hc, r, s, hr_onto, hs_ne, fun ϑ p _ _ φ hp hφ ↦ ?_, fun σ φ B hB x ↦ ?_⟩
  · -- (a) At integral points the delta forms of integral vectors are integral.
    have hε_int : ε ∈ embValRing := by by_cases hβ0 : β = 0 <;> simp [ε, hβ0]
    have hΞ_int {x : Gf D.E (D.Y D.m)} (hx : x ∈ integralAbove (D.Y D.m) p)
        (w : WeylIndex (D.Y D.m) (D.lastPathColumns false) → ℤ) :
        N * Ξ ϑ φ x (fun i ↦ w i) ∈ embValRing := by
      refine h_integral (hΨ ϑ) (fixedByOuterLevels_lastPathConjDelta ϑ x _ φ) hp (Bool.forall_bool.2
        ⟨weylGauge_lastPathConjDelta_le_one ϑ x hx w, fun g ↦ ?_⟩)
      simpa only [mul_one] using hφ g
    exact weylGauge_le_one_of_integralAbove _ fun x hx ↦
      D.mem_embValRing_of_dualPairing_eq_dualHook_mul fun w ↦
        ⟨_, mul_mem hε_int (hΞ_int hx w), h_pair ϑ φ x _⟩
  -- (b) The conjugates of the sum `Ξ` for delta forms are small.
  have hΞ_le (v : D.DualVector) :
      ‖σ (Ξ 1 φ x v)‖ ≤ exp (D.x ^ 200 * D.b ^ 2) * √(weylNormSq (σ ∘ v)) * √B :=
    D.norm_lastPathPeriod_le (hΨ 1) (fixedByOuterLevels_lastPathConjDelta 1 x v φ) σ
      (B := fun z ↦ if z then B else weylNormSq (σ ∘ v))
      (Bool.forall_bool.2 ⟨weylNormSq_lastPathConjDelta_le 1 x v σ, hB⟩)
  have hε_le : ‖σ ε‖ ≤ 1 := by by_cases hβ0 : β = 0 <;> simp [ε, hβ0]
  have h_hook : (0 : ℝ) ≤ D.dualHook := mod_cast hookNumber_pos.le
  have h_pair_le (v : D.DualVector) :
      ‖σ (v ⬝ᵥ D.dualPairing.map (↑) *ᵥ (D.lowerChain .one (s • r φ)).val x)‖ ≤
        exp (D.x ^ 201 * D.b ^ 2) * √B * √(weylNormSq (σ ∘ v)) :=
    calc _ = ‖σ (D.dualHook * (ε * (N * Ξ 1 φ x v)))‖ := by
          rw [← h_pair, div_self (c 1).ne_zero, one_smul]
          rfl
      _ = D.dualHook * ‖σ ε‖ * N * ‖σ (Ξ 1 φ x v)‖ := by
          simp [abs_of_nonneg h_hook, mul_assoc]
      _ ≤ D.dualHook * 1 * exp (D.x ^ 99 * D.b ^ 2) *
          (exp (D.x ^ 200 * D.b ^ 2) * √(weylNormSq (σ ∘ v)) * √B) := by
          gcongr
          exact hΞ_le v
      _ = D.dualHook * exp (D.x ^ 99 * D.b ^ 2) * exp (D.x ^ 200 * D.b ^ 2) * √B *
          √(weylNormSq (σ ∘ v)) := by ring
      _ ≤ _ := by grw [D.dualHook_mul_exp_le]
  refine (D.weylNormSq_le_of_dualPairing σ (by positivity) h_pair_le).trans_eq ?_
  rw [mul_pow, sq_sqrt ((weylNormSq_nonneg _).trans (hB 1)), ← exp_natCast_mul, Nat.cast_ofNat,
    ← mul_assoc]

/-- The space `gridLevelForms` of forms of level `J(𝔟)` on `Ỹ^m_0`, the space at the outer end of
the half `true` of the last path, is spanned by the forms `φ` whose algebraic forms
`lastPathToAlgForm true φ` are short: their values are integral at every prime and all conjugates of
the values have squared norm at most `exp (x ^ 99 * b ^ 2)`, with `x = D.x` the length of the prime
sum and `b = D.b` the weight at the `b`-places. -/
lemma span_isShort_eq_top_gridLevelForms : span ℂ {φ : D.gridLevelForms D.m |
    IsShort (exp (D.x ^ 99 * D.b ^ 2)) (D.lastPathToAlgForm true φ.val)} = ⊤ := by
  -- Transport along the isomorphism `e` between algebraic forms and forms of level `gridLevelGen`.
  let e : _ ≃ₗ[ℂ] D.gridLevelForms D.m :=
    (D.gridSpace 0 true 0 D.m).algFormEquiv (D.isHCParam_lastPathColumns true zero_le)
      (principalLevel (D.LastPathIndex true 0) D.gridLevelGen)
  have h_card := D.card_lastPathIndex_le true zero_le
  rw [← e.range, e.range_eq_map, ← New.span_isShort_eq_top
    (D.classAut_eq_bot_of_le_chosenLevel (D.principalLevel_le_chosenLevel piM_dvd_gridLevelGen)
      h_card) P.conductor_mem_differentIdeal
    (by grw [boxes_lastPathColumns_le_natB_mul true zero_le, h_card]) _,
    map_span, LinearEquiv.coe_coe, e.image_eq_preimage_symm]
  · rfl
  · grw [shortBasisConst, h_card]
    exact le_exp_of_log_le D.le_of_hasLogBound

/-- The space of forms on `Y₀` of principal level at the chosen places is spanned by auxiliary forms
with integral and small lifts. There are constants `c ϑ`, whose modulus is, up to a constant and a
fixed power of the norm `ϑ.normQ` of the places of `ϑ`, the product of the ratios `turnRatio`, such
that this space is spanned by the forms `y` with two properties: for all twists `ϑ`,
`(c ϑ / c 1) • lowerChainAtLevel ϑ y` has values integral at every prime not dividing `ϑ.normQ`, and
all conjugates of the values of `lowerChain 1 y`, the chain of lifts for the trivial twist, have
squared norm `weylNormSq` at most `exp (x ^ 202 * b ^ 2)`, with `x = D.x` the length of the prime
sum and `b = D.b` the weight at the `b`-places. -/
lemma exists_span_short_lifts_eq_top : ∃ c : D.MFoldTwist → ℂˣ,
    D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
      (∏ i ∈ range D.m, ∏ j ∈ range D.m, D.turnRatio i j) ∧
    span ℂ {y : D.principalForms (D.spaceY 0) |
      (∀ (ϑ : D.MFoldTwist) (l : ℕ) [Fact l.Prime] (place : PadicPlace l), l.Coprime ϑ.normQ →
        (c ϑ / c 1 : ℂ) • D.lowerChainAtLevel ϑ y ∈ integralForms (l := l) place) ∧
      ∀ (σ : ℂ ≃+* ℂ) (g : Gf D.E (D.Y D.m)),
        weylNormSq (σ ∘ (D.lowerChain .one y).val g) ≤ exp (D.x ^ 202 * D.b ^ 2)} = ⊤ := by
  -- Short forms `φ` span and `r` is onto, so the forms `s • r φ` span.
  obtain ⟨c, hc, r, s, hr_onto, hs_ne, h_integral, h_norm⟩ :=
    D.exists_lowerChain_integral_and_weylNormSq_le
  refine ⟨c, hc, eq_top_mono ?_ hr_onto⟩
  rw [r.range_eq_map, ← D.span_isShort_eq_top_gridLevelForms, map_span_le]
  intro φ hφ
  refine (smul_mem_iff _ hs_ne).1 (subset_span
    ⟨fun ϑ p _ place hp ↦ h_integral ϑ p place φ hp (hφ.1 p), fun σ g ↦ ?_⟩)
  calc _ ≤ exp (2 * D.x ^ 201 * D.b ^ 2) * exp (D.x ^ 99 * D.b ^ 2) :=
        h_norm σ φ _ (hφ.2 σ) g
    _ = exp (2 * D.x ^ 201 * D.b ^ 2 + D.x ^ 99 * D.b ^ 2) := by rw [exp_add]
    _ ≤ _ := exp_le_exp.2 D.le_of_hasLogBound

end New.Data

end
