import Theorems.Thm_StickyKakeya4_native_rank_one_physical_upper
import Theorems.Thm_StickyKakeya4_native_rank_one_power_exclusion
import Theorems.Thm_StickyKakeya4_native_same_source_multiplicity_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeRankOneBranchBudget
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeCubicalIncidenceCounts NativeDirectionRankDichotomy
open NativeJointUniformCoarseRelations NativeIncidenceMultiplicityTower NativeRankOnePhysicalUpper
open NativeCoarseFineMultiplicity NativeFixedCompactKakeyaExponent

/-- The actual rank-one branch forces its scalar power budget. Its lower
comes from the true retained original incidences, and its upper from the
original reference geometry and installed parent/point relation. No sparse
native admission, supplied multiplicity bound for F, or bounded-parent-menu premise occurs. -/
theorem actual_rank_one_budget {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hk : 0 < extremalExponent)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E1 F : Finset (Fin n × Index)) (hE1 : E1 ⊆ incidences original) (hF : F ⊆ E1)
    (m rad : ℕ) (r stopEta power theta nu G : ℝ)
    (hr : 0 < r) (hrsmall : r ≤ 1/4) (hdeltar : D.thickness ≤ r)
    (hpower : 0 < power) (hradius : r ≤ D.thickness^power)
    (hstop : stopEta ≤ extremalExponent/2) (hG : 0 < G)
    (hNr : 48*((2^m:ℕ):ℝ)*r=1)
    (planes : Index → Submodule ℝ E4)
    (hdim : ∀k∈F.image Prod.snd,Module.finrank ℝ (planes k) ≤ 1)
    (hnear : ∀z∈F,Metric.infDist (slopeVector D z.1) (planes z.2:Set E4) ≤ r)
    (H : HasUniformFibers E1 rad (formalPair D a m))
    (hparent : ∀p,(parentEdges D a (2^m) E1 p).Nonempty →
      multiplicity (parentEdges D a (2^m) E1 p) ≤
        D.thickness^(-theta)*(((2^m:ℕ):ℝ)*D.thickness/64)^(-extremalExponent))
    (hret : r^stopEta/G*(E1.card:ℝ) ≤ F.card)
    (hglobal : D.thickness^(-extremalExponent+nu) ≤ multiplicity E1) :
    1 ≤ (9261*(6144:ℝ)^3)*G*(rad:ℝ)^2*
      D.thickness^(power*extremalExponent/2-theta-nu) := by
  have hd := h.1.2.1
  have hN : (0:ℝ) < ((2^m:ℕ):ℝ) := by positivity
  have hNr' : ((2^m:ℕ):ℝ)*r=1/48 := by nlinarith only [hNr]
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdeltar hN.le
    rw [hNr'] at hh
    linarith
  have hc : 0 ≤ r^stopEta/G := div_nonneg (Real.rpow_pos_of_pos hr _).le hG.le
  have hretain := retained_incidence_multiplicity E1 F hF hc hret
  have hlo : r^stopEta/G*D.thickness^(-extremalExponent+nu) ≤ multiplicity F :=
    (mul_le_mul_of_nonneg_left hglobal hc).trans hretain
  have hu := rank_one_multiplicity_upper h original horiginal ha E1 F hE1 hF m rad r
    (D.thickness^(-theta)*(((2^m:ℕ):ℝ)*D.thickness/64)^(-extremalExponent))
    hr hrsmall (by positivity) hNr.le hscale planes hdim hnear H hparent
  apply NativeRankOnePowerExclusion.rank_one_budget_le hd h.1.2.2.1 hr hk
    extremalExponent_le_three hstop hpower hradius hN _ hG (Nat.cast_nonneg rad) hlo
  · simpa only [mul_assoc] using hu
  · rw [hNr']
    norm_num

end NativeRankOneBranchBudget
