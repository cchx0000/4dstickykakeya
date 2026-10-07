import Theorems.Thm_StickyKakeya4_native_column_population_bounds
import Theorems.Thm_StickyKakeya4_native_retained_slice_count_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeRetainedColumnPairCore
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeCoarseShadingUniformity
open NativeAnisotropicGlobalSourceBridge NativeRetainedSliceCountTransfer SelfUniform
open NativeConditionedPairMenu

/-- One parent-tagged actual phase/column label, fixed before the second core.
The outer parent is part of the equality, so conditioning retains whole fibers. -/
def taggedPair {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ)
    (z : Fin n × Index) : Parent × (Parent × Index) :=
  (parentLabel D a (2^m) z.1,
    columnPair D a m f (parentLabel D a (2^m) z.1) z)

def relations {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (depths : Fin K → ℕ) : Fin K → (Fin n × Index) → (Fin n × Index) → Prop :=
  fun j x y => taggedPair D a m (depths j) x=taggedPair D a m (depths j) y

lemma relations_refl {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (depths : Fin K → ℕ) : ∀j x,relations D a m depths j x x := by
  intro j x
  rfl

lemma relations_symm {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (depths : Fin K → ℕ) :
    ∀j x y,relations D a m depths j x y → relations D a m depths j y x := by
  intro j x y H
  exact H.symm

/-- Decode preinstalled equality relations on the unchanged E2. This theorem
does not assert uniformity for a later arbitrary retained subset. -/
theorem caller_parent_pair_uniformity {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (depths : Fin K → ℕ) (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (relations D a m depths j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (relations D a m depths j) E y)
    (p : Parent) (j : Fin K) :
    HasUniformFibers (parentEdges D a (2^m) E p) Q (columnPair D a m (depths j) p) := by
  have hU : HasUniformFibers E Q (taggedPair D a m (depths j)) := by
    intro x hx y hy
    have hh := H j x y hx hy
    change degree (fun _ : Fin n × Index => 1)
      (fun x y => taggedPair D a m (depths j) x=taggedPair D a m (depths j) y) E x ≤
      Q^2*degree (fun _ : Fin n × Index => 1)
        (fun x y => taggedPair D a m (depths j) x=taggedPair D a m (depths j) y) E y at hh
    simpa only [unit_degree_eq_fiber] using hh
  apply uniformity_congr _
    (fun z => columnPair D a m (depths j) (parentLabel D a (2^m) z.1) z) _ Q
  · intro z hz
    rw [(mem_filter.mp hz).2]
  · exact conditioned_uniformity E (fun z => parentLabel D a (2^m) z.1) _ Q hU p

/-- Arbitrary subsequent original-edge retention retains distinct geometric
phase/column incidences. Multiple original labels are counted only once. -/
theorem retained_pair_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m f : ℕ) (E H : Finset (Fin n × Index)) (p : Parent) (Q : ℕ)
    (hH : H⊆parentEdges D a (2^m) E p)
    (hEn : (parentEdges D a (2^m) E p).Nonempty)
    (HU : HasUniformFibers (parentEdges D a (2^m) E p) Q (columnPair D a m f p))
    (lambda G : ℝ) (hG : 0 ≤ G)
    (hret : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ G*H.card) :
    lambda*((parentEdges D a (2^m) E p).image (columnPair D a m f p)).card ≤
      G*(Q:ℝ)^2*(H.image (columnPair D a m f p)).card :=
  point_image_retention _ H hH hEn (columnPair D a m f p) Q HU lambda G hG hret

/-- The point denominator can only decrease under the same original cut.
No time-filling or post-cut uniformity is used in this multiplicity transfer. -/
theorem retained_pair_multiplicity {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m f : ℕ) (E H : Finset (Fin n × Index)) (p : Parent) (Q : ℕ)
    (hH : H⊆parentEdges D a (2^m) E p)
    (hEn : (parentEdges D a (2^m) E p).Nonempty)
    (HU : HasUniformFibers (parentEdges D a (2^m) E p) Q (columnPair D a m f p))
    (lambda G : ℝ) (hlambda : 0 ≤ lambda) (hG : 0 < G) (hQ : 0 < Q)
    (hret : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ G*H.card) :
    (lambda/(G*(Q:ℝ)^2))*NativeIncidenceMultiplicityTower.multiplicity
        ((parentEdges D a (2^m) E p).image (columnPair D a m f p)) ≤
      NativeIncidenceMultiplicityTower.multiplicity (H.image (columnPair D a m f p)) := by
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hcost : 0 < G*(Q:ℝ)^2 := by positivity
  apply NativeCoarseFineMultiplicity.retained_incidence_multiplicity
    ((parentEdges D a (2^m) E p).image (columnPair D a m f p))
    (H.image (columnPair D a m f p)) (image_subset_image hH) (div_nonneg hlambda hcost.le)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hcost).mpr
  simpa only [mul_comm] using retained_pair_card D a m f E H p Q hH hEn HU lambda G hG.le hret

end NativeRetainedColumnPairCore
