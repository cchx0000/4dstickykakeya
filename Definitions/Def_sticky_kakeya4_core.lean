import Mathlib

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace StickyKakeya4

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev MarkedLine := (E4 × E4) × ℝ

def direction (line : MarkedLine) : E4 := line.1.1
def offset (line : MarkedLine) : E4 := line.1.2
def mark (line : MarkedLine) : ℝ := line.2

def IsValidLine (line : MarkedLine) : Prop :=
  ‖direction line‖ = 1 ∧ inner ℝ (offset line) (direction line) = 0

def lineCarrier (lines : Set MarkedLine) : Set (E4 × E4) :=
  (fun line => (direction line, offset line)) '' lines

def FullDirection (lines : Set MarkedLine) : Prop :=
  ∀ θ : E4, ‖θ‖ = 1 → ∃ line ∈ lines, direction line = θ

def IsDirectionSelector (lines : Set MarkedLine) : Prop :=
  ∀ θ : E4, ‖θ‖ = 1 → ∃! line, line ∈ lines ∧ direction line = θ

def unitFront (lines : Set MarkedLine) : Set E4 :=
  {x | ∃ line ∈ lines, ∃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
    x = offset line + (mark line + t) • direction line}

def coversAtRadius {X : Type*} [PseudoMetricSpace X]
    (s : Set X) (r : ℝ) (centers : Finset X) : Prop := by
  classical
  exact s ⊆ ⋃ x ∈ (centers : Set X), Metric.ball x r

def coveringNumber {X : Type*} [PseudoMetricSpace X]
    (s : Set X) (r : ℝ) : ℝ≥0∞ := by
  classical
  exact sInf {n : ℝ≥0∞ | ∃ centers : Finset X,
    coversAtRadius s r centers ∧ n = centers.card}

def upperMinkowskiDim {X : Type*} [PseudoMetricSpace X]
    (s : Set X) : ℝ≥0∞ :=
  sInf {d : ℝ≥0∞ | d ≠ ⊤ ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      coveringNumber s r ≤ C * (ENNReal.ofReal r).rpow (-d.toReal)}

def packingDim {X : Type*} [PseudoMetricSpace X]
    (s : Set X) : ℝ≥0∞ :=
  sInf {d : ℝ≥0∞ | ∃ pieces : ℕ → Set X,
    s ⊆ ⋃ n, pieces n ∧ ∀ n, upperMinkowskiDim (pieces n) ≤ d}

def IsStickyDatum (lines : Set MarkedLine) : Prop :=
  IsCompact lines ∧
  (∀ line ∈ lines, IsValidLine line) ∧
  FullDirection lines ∧
  packingDim (lineCarrier lines) ≤ 3

def collisionTime (α β : E3) : ℝ :=
  -inner ℝ α β / ‖α‖ ^ 2

def collisionResidual (α β : E3) : E3 :=
  β + collisionTime α β • α

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

def pencil (A B : Mat3) (s : ℝ) : Mat3 := B + s • A

def graphPlane (A B : Mat3) : Set (E3 × E3) :=
  {(x, y) | ∃ c : E3, x = A.mulVec c ∧ y = B.mulVec c}

def lagrangianPencil (s : ℝ) : Set (E3 × E3) :=
  {(x, y) | y = (-s) • x}

/-!
Finite-scale marked sources.  The tree is part of the data rather than a
cardinality parameter: its cells are nested along parent edges, and the
affine fibre mark is retained separately from the unmarked carrier.
-/

structure NestedCarrierTree (n : ℕ) where
  parent : Fin n → Option (Fin n)
  level : Fin n → ℕ
  parent_level : ∀ {i p}, parent i = some p → level p < level i
  carrierCell : Fin n → Set (E4 × E4)
  nested : ∀ {i p}, parent i = some p → carrierCell i ⊆ carrierCell p

structure FiniteScaleSource (n : ℕ) where
  thickness : ℝ
  line : Fin n → MarkedLine
  /-- A finite source is a weighted family of actual marked lines, not a
  multiplicity list.  Exact duplicates would otherwise create arbitrary
  source mass without adding any geometric direction or carrier data. -/
  line_injective : Function.Injective line
  shading : Fin n → Set E4
  weight : Fin n → ℝ≥0∞
  fibreMark : Fin n → ℝ
  tree : NestedCarrierTree n
  line_in_carrier : ∀ i, (direction (line i), offset (line i)) ∈ tree.carrierCell i

def sourceFunction {n : ℕ} (D : FiniteScaleSource n) (x : E4) : ℝ≥0∞ := by
  classical
  exact ∑ i, if x ∈ D.shading i then D.weight i else 0

def sourceMass {n : ℕ} (D : FiniteScaleSource n) : ℝ≥0∞ :=
  ∫⁻ x, sourceFunction D x ∂volume

def sourceUnion {n : ℕ} (D : FiniteScaleSource n) : Set E4 :=
  {x | 0 < sourceFunction D x}

/-- Total marked source weight whose direction lies in a metric ball.  This is
the weighted replacement for merely counting occupied direction cells: it is
stable under fractional source restrictions and forbids arbitrary
multiplicity inside one thickness-scale carrier cell. -/
def directionWeightInBall {n : ℕ} (D : FiniteScaleSource n)
    (theta : E4) (r : ℝ) : ℝ≥0∞ := by
  classical
  exact ∑ i, if dist (direction (D.line i)) theta < r then D.weight i else 0

def ComesFromSelector {n : ℕ} (D : FiniteScaleSource n)
    (selector : Set MarkedLine) : Prop :=
  ∀ i, D.line i ∈ selector

def IsAdmissibleStickySource {n : ℕ} (D : FiniteScaleSource n)
    (ε : ℝ) (C : ℝ≥0∞) : Prop :=
  0 < D.thickness ∧ D.thickness < 1 ∧
  (∀ i, D.weight i ≤ 1) ∧
  (∀ i, D.fibreMark i = mark (D.line i)) ∧
  (∀ i, IsValidLine (D.line i)) ∧
  (∀ i, MeasurableSet (D.shading i)) ∧
  (∀ i, 0 < D.weight i →
    (ENNReal.ofReal D.thickness).rpow (3 + ε) ≤ volume (D.shading i)) ∧
  (∀ i x, x ∈ D.shading i →
    Metric.infDist x (unitFront {D.line i}) ≤ D.thickness) ∧
  (∀ theta : E4, ∀ r : ℝ, D.thickness ≤ r → r ≤ 1 →
    directionWeightInBall D theta r ≤
      C * (ENNReal.ofReal (r / D.thickness)).rpow (3 + ε)) ∧
  (∀ r : ℝ, D.thickness ≤ r → r ≤ 1 →
    coveringNumber (lineCarrier (Set.range D.line)) r ≤
      C * (ENNReal.ofReal r).rpow (-(3 + ε)))

def IsFractionalSourceRestriction {n : ℕ}
    (R D : FiniteScaleSource n) : Prop :=
  R.thickness = D.thickness ∧
  R.line = D.line ∧
  R.fibreMark = D.fibreMark ∧
  R.tree = D.tree ∧
  (∀ i, MeasurableSet (R.shading i)) ∧
  (∀ i, R.shading i ⊆ D.shading i) ∧
  ∀ i, R.weight i ≤ D.weight i

def IsCarrierDescendant {n : ℕ} (T : NestedCarrierTree n)
    (child root : Fin n) : Prop :=
  Relation.ReflTransGen (fun i p => T.parent i = some p) child root

def IsRetainedDescendant {n : ℕ} (R D : FiniteScaleSource n)
    (root : Fin n) : Prop :=
  IsFractionalSourceRestriction R D ∧
  ∀ i, 0 < R.weight i → IsCarrierDescendant D.tree i root

/-!
The coherent form is the Hausdorff-scale interface.  A single probability
measure on the physical front is discretized at every small radius.  For each
ball at that radius there is a measurable shading/weight restriction whose
mass dominates the measure of the ball and whose physical union stays in the
doubled ball.  Thus the source-hereditary union estimate can be applied at the
same radius as the desired Frostman bound.
-/

def HasCoherentFiniteScaleSources
    (selector ambient : Set MarkedLine) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
    ∃ μ : Measure E4,
      IsProbabilityMeasure μ ∧
      μ (unitFront ambient)ᶜ = 0 ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∃ n : ℕ, ∃ D : FiniteScaleSource n,
          D.thickness = δ ∧
          ComesFromSelector D selector ∧
          IsAdmissibleStickySource D ε C ∧
          C⁻¹ ≤ sourceMass D ∧ sourceMass D ≤ C ∧
          ∀ x : E4, ∃ R : FiniteScaleSource n,
            IsFractionalSourceRestriction R D ∧
            sourceUnion R ⊆ Metric.closedBall x (2 * δ) ∧
            μ (Metric.ball x δ) ≤ C * sourceMass R

/-- The admissibility exponent uses a fixed fraction of the requested output
loss.  This leaves room for the ambient root-mass normalization and the
subpower contact/symplectic decompositions instead of spending the same
epsilon twice. -/
def HasUniformMarkedSourceEstimate (selector : Set MarkedLine) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ Cpack : ℝ≥0∞, Cpack ≠ 0 → Cpack ≠ ⊤ →
    ∃ A : ℝ≥0∞, A ≠ 0 ∧ A ≠ ⊤ ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (n : ℕ) (D R : FiniteScaleSource n),
      D.thickness ≤ δ₀ →
      ComesFromSelector D selector →
      IsAdmissibleStickySource D (ε / 10) Cpack →
      IsFractionalSourceRestriction R D →
      sourceMass R ≤
          A * (ENNReal.ofReal D.thickness).rpow (-ε) * volume (sourceUnion R)

/--
The finite certificate produced by the contact/symplectic stopping argument.
`conservation` is the edge-flow identity on a finite level-decreasing carrier
forest.  Continuing child flow telescopes exactly.  The only nonterminal
defect is `routingError`, whose total is at most half the root flow and is
absorbed once after telescoping.  The last two fields are the local geometric
payment bound and its weighted Carleson summation.  In particular, the desired
union estimate is not a field of the certificate.
-/
structure ContactSymplecticEdgeFlowCertificate {n : ℕ}
    (D R : FiniteScaleSource n) (ε : ℝ) (A : ℝ≥0∞) where
  incoming : Fin n → ℝ≥0∞
  paid : Fin n → ℝ≥0∞
  terminalMass : Fin n → ℝ≥0∞
  routingError : Fin n → ℝ≥0∞
  capacity : Fin n → ℝ≥0∞
  conservation : ∀ i,
    incoming i = paid i + terminalMass i + routingError i +
      Finset.univ.sum (fun j : Fin n =>
        if R.tree.parent j = some i then incoming j else 0)
  sourceAtRoots : sourceMass R =
    Finset.univ.sum (fun i : Fin n =>
      if R.tree.parent i = none then incoming i else 0)
  smallError :
    Finset.univ.sum routingError + Finset.univ.sum routingError ≤
      Finset.univ.sum (fun i : Fin n =>
        if R.tree.parent i = none then incoming i else 0)
  localCharge : ∀ i,
    paid i + terminalMass i ≤ capacity i * volume (sourceUnion R)
  capacityCarleson : Finset.univ.sum capacity ≤
    A * (ENNReal.ofReal D.thickness).rpow (-ε)

def HasContactSymplecticEdgeFlowCertificates
    (selector : Set MarkedLine) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ Cpack : ℝ≥0∞, Cpack ≠ 0 → Cpack ≠ ⊤ →
    ∃ A : ℝ≥0∞, A ≠ 0 ∧ A ≠ ⊤ ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (n : ℕ) (D R : FiniteScaleSource n),
      D.thickness ≤ δ₀ →
      ComesFromSelector D selector →
      IsAdmissibleStickySource D (ε / 10) Cpack →
      IsFractionalSourceRestriction R D →
      Nonempty (ContactSymplecticEdgeFlowCertificate D R ε A)

def HasFrontFrostmanMeasures (selector : Set MarkedLine) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 4 →
    ∃ μ : Measure E4,
      IsProbabilityMeasure μ ∧
      μ (unitFront selector)ᶜ = 0 ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ (x : E4) (r : ℝ), 0 < r → r ≤ 1 →
          μ (Metric.ball x r) ≤
            C * (ENNReal.ofReal r).rpow (4 - ε)

end StickyKakeya4
