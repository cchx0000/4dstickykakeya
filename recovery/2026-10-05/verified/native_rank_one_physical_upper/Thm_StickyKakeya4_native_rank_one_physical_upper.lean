import Theorems.Thm_StickyKakeya4_native_rank_one_parent_cap
import Theorems.Thm_StickyKakeya4_native_rank_one_reference_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeRankOnePhysicalUpper
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeCubicalIncidenceCounts NativeDirectionRankDichotomy
open NativeJointUniformCoarseRelations NativeIncidenceMultiplicityTower NativeRankOneParentCap
open NativeRankOneReferenceUpper

/-- An actual pointwise rank-one cut is paid by the original reference
parent upper. Its finite parent menu is derived from the geometric planes,
not assumed, and the sparse cut is never readmitted as a native source. -/
theorem rank_one_multiplicity_upper {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E1 F : Finset (Fin n × Index)) (hE1 : E1 ⊆ incidences original) (hF : F ⊆ E1)
    (m rad : ℕ) (r U : ℝ) (hr : 0 < r) (hrsmall : r ≤ 1/4) (hU : 0 ≤ U)
    (hNr : 48*((2^m:ℕ):ℝ)*r ≤ 1) (hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (planes : Index → Submodule ℝ E4)
    (hdim : ∀k∈F.image Prod.snd,Module.finrank ℝ (planes k) ≤ 1)
    (hnear : ∀z∈F,Metric.infDist (slopeVector D z.1) (planes z.2:Set E4) ≤ r)
    (H : HasUniformFibers E1 rad (formalPair D a m))
    (hupper : ∀p,(parentEdges D a (2^m) E1 p).Nonempty →
      multiplicity (parentEdges D a (2^m) E1 p) ≤ U) :
    multiplicity F ≤ (9261:ℝ)*(rad:ℝ)^2*U := by
  apply original_selected_parent_cap_upper D a m E1 F hF rad 9261 U hU H hupper
  intro k hk
  have hsub : F.filter (fun z => z.2=k) ⊆
      nearLabels (E1.filter (fun z => z.2=k)) (fun z => slopeVector D z.1) r (planes k) := by
    intro z hz
    obtain ⟨hzF,hzk⟩ := mem_filter.mp hz
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨hF hzF,hzk⟩,?_⟩
    simpa only [hzk] using hnear z hzF
  exact (card_le_card (image_subset_image hsub)).trans
    (actual_near_parent_card_le h original horiginal ha E1 hE1 k (planes k) (hdim k hk)
      r hr hrsmall (2^m) hNr hscale)

end NativeRankOnePhysicalUpper
