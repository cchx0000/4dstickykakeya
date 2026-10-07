import Theorems.Thm_StickyKakeya4_native_rank_one_branch_budget
import Theorems.Thm_StickyKakeya4_native_rank_one_source_cutoff
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section

namespace NativeRankOneExcludedFromSourceCost
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeCubicalIncidenceCounts NativeDirectionRankDichotomy
open NativeJointUniformCoarseRelations NativeIncidenceMultiplicityTower
open NativeFixedCompactKakeyaExponent NativeRankOneBranchBudget NativeRankOneSourceCutoff

/-- One cutoff, selected before every actual source and returned parameter,
excludes the geometric rank-one branch. Its strict budget is derived from
the original source's returned transfer cost. The retained F is used only
as its literal original incidences; neither a multiplicity estimate for F
nor a new native admission is a hypothesis. -/
theorem exists_actual_rank_one_exclusion {power theta nu b G : ℝ}
    (hk : 0 < extremalExponent) (hpower : 0 < power) (hG : 0 < G)
    (hgap : b < power * extremalExponent / 2 - theta - nu) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta a : ℝ), 0 ≤ eta →
        ∀ _h : IsWangZakharovNativeFiniteInput D eta, D.thickness ≤ delta0 →
          ∀ original : Fin n → Finset Index,
            (∀ i, D.shading i = wzCellShading (mesh D) original i) →
            (∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
              Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) →
            ∀ E1 F : Finset (Fin n × Index), E1 ⊆ incidences original → F ⊆ E1 →
              ∀ m rad costFactor : ℕ, 0 < costFactor →
                (125 * 175616 * 16384 : ℝ) * (costFactor : ℝ) * (rad : ℝ) ^ (2 : ℕ) *
                  D.thickness ^ (-eta) ≤ D.thickness ^ (-b) →
                ∀ r stopEta : ℝ, 0 < r → r ≤ 1 / 4 → D.thickness ≤ r →
                  r ≤ D.thickness ^ power → stopEta ≤ extremalExponent / 2 →
                  48 * ((2 ^ m : ℕ) : ℝ) * r = 1 →
                  ∀ planes : Index → Submodule ℝ E4,
                    (∀ k ∈ F.image Prod.snd, Module.finrank ℝ (planes k) ≤ 1) →
                    (∀ z ∈ F, Metric.infDist (slopeVector D z.1) (planes z.2 : Set E4) ≤ r) →
                    HasUniformFibers E1 rad (formalPair D a m) →
                    (∀ p, (parentEdges D a (2 ^ m) E1 p).Nonempty →
                      multiplicity (parentEdges D a (2 ^ m) E1 p) ≤
                        D.thickness ^ (-theta) *
                          (((2 ^ m : ℕ) : ℝ) * D.thickness / 64) ^ (-extremalExponent)) →
                    r ^ stopEta / G * (E1.card : ℝ) ≤ F.card →
                    D.thickness ^ (-extremalExponent + nu) ≤ multiplicity E1 → False := by
  obtain ⟨delta0, hd0, hd01, hcut⟩ := exists_source_cutoff hG hgap
  refine ⟨delta0, hd0, hd01, ?_⟩
  intro n D eta a heta h hsmall original horiginal ha E1 F hE1 hF
    m rad costFactor hFactor hcost r stopEta hr hrsmall hdeltar hradius hstop hNr
    planes hdim hnear H hparent hret hglobal
  have hbudget := actual_rank_one_budget h hk original horiginal ha E1 F hE1 hF
    m rad r stopEta power theta nu G hr hrsmall hdeltar hpower hradius hstop hG hNr
    planes hdim hnear H hparent hret hglobal
  have hstrict := hcut D.thickness h.1.2.1 hsmall costFactor rad hFactor eta heta hcost
  exact (not_lt_of_ge hbudget) hstrict

end NativeRankOneExcludedFromSourceCost
