import Theorems.Thm_StickyKakeya4_native_history_grain_cleanup
import Theorems.Thm_StickyKakeya4_native_rank_four_packet_count

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000

noncomputable section
namespace NativeHistoryGrainPowerDensity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeSpatialAngularGeometry NativeDirectionRankDichotomy
open NativeSquaredGrainQueries NativeOriginalPacketReference NativeQueriedVertexWeights
open NativeJointUniformCoarseRelations NativeCompatibleNodeDirections NativeActualGrainHistory
open NativeActualProjectedGrainCount NativeHistoryGrainCount NativeActualRichPacketLayers
open NativeHistoryGrainCleanup RichDirectionalLayers WeightedRichDirectionalLayers
open scoped BigOperators

/-- The actual original-weight fraction enters the gain at every scale. -/
def scaleGain {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : ℕ) (S : Finset Index) (ell : ℕ) (lambda c1 c2 : ℝ) : ℝ :=
  ((mass S (pointWeight E):ℝ)/(E.card:ℝ))*lambda*D.thickness^(c1+5*c2)/
    (2*(ell:ℝ)*(referenceConstant:ℝ)*(64/((2^m:ℕ):ℝ)))

lemma scaleGain_nonneg {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m : ℕ) (S : Finset Index) (ell : ℕ) (lambda c1 c2 : ℝ)
    (hd : 0 < D.thickness) (hlambda : 0 ≤ lambda) :
    0 ≤ scaleGain D E m S ell lambda c1 c2 := by
  dsimp only [scaleGain]
  positivity

/-- The derived threshold bounds supply the full inverse-scale power. The
ceiling factors are the literal predecessor counts from the actual layers. -/
theorem scale_predecessor_power_lower {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (m : ℕ) (S : Finset Index)
    (ell : ℕ) (dir : ℕ → Index → Fin n) (Q : ℕ) (lambda c1 c2 : ℝ)
    (hd : 0 < D.thickness) (hlambda : 0 ≤ lambda)
    (HU : HasUniformFibers E Q (fun z => spatialLabel D (2^(phaseDepth m)) z.2))
    (H : HasScaleRecord D E m S ell dir Q lambda c1 c2) :
    (scaleGain D E m S ell lambda c1 c2)^ell ≤
      (predecessorProduct D m E Q (scaleThreshold D E m S ell dir) ell:ℝ) := by
  obtain ⟨_hUA,_hw,_hN,_hb,_hz,_hnest,_hA,_hhalf,_hpos,_hpre,_hp,hthreshold⟩ := H
  have hM := vertexCap_pos E hE (spatialLabel D (2^(phaseDepth m))) Q HU
  rw [predecessorProduct,Nat.cast_prod]
  calc
    _ = ∏_i∈range ell,scaleGain D E m S ell lambda c1 c2 := by simp
    _ ≤ _ := prod_le_prod (fun _ _ => scaleGain_nonneg D E m S ell lambda c1 c2 hd hlambda)
      (fun i hi => (hthreshold i (mem_range.mp hi)).le.trans
        (NativeRankFourPacketCount.ratio_le_ceilDiv _ _ hM))

/-- Quantitative final grain density with the full Delta^(-ell) gain derived
from the actual history. The original current and final mass ratios remain
explicit, and the original raw-vertex cap is never discarded. -/
theorem exists_actual_power_dense_grain_core {n J : ℕ}
    {D : FiniteScaleSource n} {eta a q lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (E : Finset (Fin n × Index)) (hE : E.Nonempty)
    (hJ : 0 < J) (m : Fin J → ℕ) (hm : ∀j,6 ≤ m j) (ell : ℕ) (hell : ell ≤ 4)
    (S0 : Finset Index) (hS0 : S0⊆E.image Prod.snd) (Q : ℕ)
    (HU : ∀j,HasUniformFibers E Q (fun z => spatialLabel D (2^(phaseDepth (m j))) z.2))
    (hq : 0 < q) (hq1 : q ≤ 1) (hlambda : 0 ≤ lambda)
    (point : Fin J → Index → Index)
    (tuple : Fin J → Index → Fin ell → (Fin n × Index))
    (anchor : Fin J → Index → Fin ell → Fin n)
    (Hsys : ∀j,IsNodeDirectionSystem D a (m j) E S0 q ell (point j) (tuple j) (anchor j))
    (Hhistory : HasGrainHistory D E m ell (fun j => natStageDirectionIndex h (tuple j))
      S0 Q lambda c1 c2) :
    let S := history D E m ell (fun j => natStageDirectionIndex h (tuple j)) S0
    let F := S J
    let P := fun j node => spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple j node))
    let f := fun j => taggedLabel D (m j) (P j) ell
    let gain := fun j => scaleGain D E (m j) (S j.val) ell lambda c1 c2
    let M := fun j => vertexCap E (spatialLabel D (2^(phaseDepth (m j)))) Q
    ∃K⊆F,K.Nonempty ∧ mass F (pointWeight E) ≤ 2*mass K (pointWeight E) ∧
      mass S0 (pointWeight E) ≤ 2^(J+1)*mass K (pointWeight E) ∧
      (∀j : Fin J,(M j:ℝ)*(gain j)^ell*(F.image (f j)).card ≤
        625*transverseCost q ell*(Q:ℝ)^2*E.card) ∧
      ∀j : Fin J,∀x∈K,
        ((mass F (pointWeight E):ℝ)/(E.card:ℝ))*(M j:ℝ)*(gain j)^ell/
          (1250*(J:ℝ)*transverseCost q ell*(Q:ℝ)^2) <
            (mass (classFiber K (f j) (f j x)) (pointWeight E):ℝ) ∧
        ∀y∈classFiber K (f j) (f j x),
          spatialLabel D (2^(m j)) y=spatialLabel D (2^(m j)) x ∧
          Metric.infDist (rawVertex D (phaseDepth (m j)) y-rawVertex D (phaseDepth (m j)) x)
            (P j (spatialLabel D (2^(m j)) x):Set E4) ≤ 2*grainWidth (m j) ell := by
  intro S F P f gain M
  obtain ⟨K,hKF,hKn,hhalf,hret,hcounts,hfiber⟩ :=
    exists_actual_final_grain_core h E hE hJ m hm ell hell S0 hS0 Q HU hq hq1
      point tuple anchor Hsys Hhistory
  have hpower (j : Fin J) : (gain j)^ell ≤
      (predecessorProduct D (m j) E Q
        (scaleThreshold D E (m j) (S j.val) ell (natStageDirectionIndex h (tuple j))) ell:ℝ) :=
    scale_predecessor_power_lower D E hE (m j) (S j.val) ell _ Q lambda c1 c2
      h.1.2.1 hlambda (HU j) (Hhistory.2.2.2.2.1 j)
  refine ⟨K,hKF,hKn,hhalf,hret,?_,?_⟩
  · intro j
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hpower j) (Nat.cast_nonneg (M j))) (Nat.cast_nonneg _)).trans
      (hcounts j).2
  · intro j x hx
    obtain ⟨_hsmall,hdensity,hgeometry⟩ := hfiber j x hx
    refine ⟨?_,hgeometry⟩
    have hD : 0 < transverseCost q ell := transverseCost_pos hq ell
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hpower j) (by positivity)) (by positivity)).trans_lt hdensity

end NativeHistoryGrainPowerDensity
