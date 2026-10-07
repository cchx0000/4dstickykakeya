import Theorems.Thm_StickyKakeya4_native_same_Q_source_restriction

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeSameQFineGraph
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeRelativeParentLabels NativeRelativeParentProfiles
open NativeConfiguredIncidenceFibers NativeSameQSourceRestriction
open scoped BigOperators

/-- The coarser Q label is attached to the unchanged baseline tube index. -/
def phase {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (a : ℝ) (m b0 b : ℕ) (p : Parent)
    (i : OutputIndex h R Eref a m b0 p) : Parent :=
  NativeDyadicParentCells.ancestor b0 b
    (NativeCoarseCellSource.parentIndex
      ((univ : Finset (Fin (parentLabels D R a (2 ^ m) p).card)).image
        (parentLabel (source h R Eref a m p) 0 (2 ^ b0))) i)

/-- Literal fine configured pairs, retaining the baseline b0 tube index. -/
def graph {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (a : ℝ) (m b0 : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (configured : Index → E4) (T : Finset (Fin n × Index)) :=
  T.image (fun z => (configured z.2, outputTube h R Eref a m b0 p hS z.1))

/-- The weight supplied to same-Q selection counts actual fine pairs. -/
def weight {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (a : ℝ) (m b0 b : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (configured : Index → E4) (T : Finset (Fin n × Index)) (q : Parent) : ℝ :=
  (((graph h R Eref a m b0 p hS configured T).filter
    (fun z => phase h R Eref a m b0 b p z.2 = q)).card : ℝ)

theorem graph_restrict {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (m b0 b : ℕ) (hb : b ≤ b0) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (configured : Index → E4) (Q : Finset Parent)
    (hT : ∀ z ∈ T, z.1 ∈ parentLabels D R a (2 ^ m) p) :
    graph h R Eref a m b0 p hS configured (restrict D a m b p Q T) =
      (graph h R Eref a m b0 p hS configured T).filter
        (fun z => phase h R Eref a m b0 b p z.2 ∈ Q) := by
  unfold graph
  rw [filter_image]
  apply congrArg (fun A : Finset (Fin n × Index) =>
    A.image (fun z => (configured z.2, outputTube h R Eref a m b0 p hS z.1)))
  apply filter_congr
  intro z hz
  change relativeLabel D a (2 ^ m) p (2 ^ b) z.1 ∈ Q ↔
    phase h R Eref a m b0 b p (outputTube h R Eref a m b0 p hS z.1) ∈ Q
  rw [phase, outputTube_ancestor_readback h R Eref a m b0 b hb p hS z.1 (hT z hz)]

/-- Exact retained fine mass of the selected Q, before any new-tube
collision or coarse point identification is charged. -/
theorem sum_weight_eq_graph {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (m b0 b : ℕ) (hb : b ≤ b0) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (configured : Index → E4) (Q : Finset Parent)
    (hT : ∀ z ∈ T, z.1 ∈ parentLabels D R a (2 ^ m) p) :
    (∑ q ∈ Q, weight h R Eref a m b0 b p hS configured T q) =
      ((graph h R Eref a m b0 p hS configured (restrict D a m b p Q T)).card : ℝ) := by
  rw [graph_restrict h R Eref T a m b0 b hb p hS configured Q hT]
  let G := graph h R Eref a m b0 p hS configured T
  let f := fun z : E4 × OutputIndex h R Eref a m b0 p => phase h R Eref a m b0 b p z.2
  have hcard : (G.filter (fun z => f z ∈ Q)).card =
      ∑ q ∈ Q, (G.filter (fun z => f z = q)).card := by
    rw [card_eq_sum_card_fiberwise (fun z hz => (mem_filter.mp hz).2)]
    apply sum_congr rfl
    intro q hq
    congr 1
    ext z
    simp only [mem_filter]
    constructor
    · exact fun hz => ⟨hz.1.1, hz.2⟩
    · intro hz
      exact ⟨⟨hz.1, by rw [hz.2]; exact hq⟩, hz.2⟩
  change (∑ q ∈ Q, ((G.filter (fun z => f z = q)).card : ℝ)) =
    ((G.filter (fun z => f z ∈ Q)).card : ℝ)
  exact_mod_cast hcard.symm

/-- The same literal parent family used by the weighted selector contains
every original retained phase; hence its total weight is the fine graph. -/
theorem total_weight_eq_graph {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (m b0 b : ℕ) (hb : b ≤ b0) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (configured : Index → E4)
    (hT : ∀ z ∈ T, z.1 ∈ parentLabels D R a (2 ^ m) p) :
    (∑ q ∈ (univ : Finset (Fin (parentLabels D R a (2 ^ m) p).card)).image
      (parentLabel (source h R Eref a m p) 0 (2 ^ b)),
        weight h R Eref a m b0 b p hS configured T q) =
      ((graph h R Eref a m b0 p hS configured T).card : ℝ) := by
  let Q := (univ : Finset (Fin (parentLabels D R a (2 ^ m) p).card)).image
    (parentLabel (source h R Eref a m p) 0 (2 ^ b))
  have he : restrict D a m b p Q T = T := by
    apply filter_eq_self.mpr
    intro z hz
    rw [← outputTube_readback h R Eref a m b p hS z.1 (hT z hz)]
    exact NativeCoarseCellSource.parentIndex_mem Q (outputTube h R Eref a m b p hS z.1)
  have hh := sum_weight_eq_graph h R Eref T a m b0 b hb p hS configured Q hT
  rwa [he] at hh

end NativeSameQFineGraph
