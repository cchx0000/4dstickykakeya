import Theorems.Thm_StickyKakeya4_native_history_grain_count
import Theorems.Thm_StickyKakeya4_native_automatic_weighted_grain_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000

noncomputable section
namespace NativeHistoryGrainCleanup
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeSpatialAngularGeometry NativeDirectionRankDichotomy
open NativeSquaredGrainQueries NativeOriginalPacketReference NativeQueriedVertexWeights
open NativeJointUniformCoarseRelations NativeCompatibleNodeDirections NativeActualGrainHistory
open NativeActualProjectedGrainCount NativeHistoryGrainCount NativeActualRichPacketLayers
open RichDirectionalLayers WeightedRichDirectionalLayers NativeAutomaticWeightedGrainCore
open scoped BigOperators

lemma classical_image_eq {A B : Type*} [DecidableEq B] (S : Finset A) (f : A → B) :
    @Finset.image A B (fun a b => Classical.propDecidable (a=b)) f S=S.image f := by
  ext b
  simp only [mem_image]

/-- A proved grain count improves the actual final class density. The vertex
multiplicity factor M is retained through this original-mass comparison. -/
lemma density_from_count {W M L G J C B : ℝ} (hW : 0 ≤ W) (hJ : 0 < J)
    (hG : 0 < G) (hC : 0 < C) (hcount : G*M*L ≤ C)
    (hdensity : W/(2*J*G) < B) : W*M*L/(2*J*C) < B := by
  have hh : W*M*L/(2*J*C) ≤ W/(2*J*G) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ = (W*(2*J))*(G*M*L) := by ring
      _ ≤ (W*(2*J))*C := mul_le_mul_of_nonneg_left hcount (mul_nonneg hW (by positivity))
      _ = _ := by ring
  exact hh.trans_lt hdensity

/-- Automatic simultaneous cleanup of the ACTUAL history-final old points.
Every count comes from genuine packet predecessors and the same installed node
tuples. Every final fiber density uses the unchanged E2 incidence weights. -/
theorem exists_actual_final_grain_core {n J : ℕ} {D : FiniteScaleSource n} {eta a q lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (E : Finset (Fin n × Index)) (hE : E.Nonempty)
    (hJ : 0 < J) (m : Fin J → ℕ) (hm : ∀j,6 ≤ m j) (ell : ℕ) (hell : ell ≤ 4)
    (S0 : Finset Index) (hS0 : S0⊆E.image Prod.snd) (Q : ℕ)
    (HU : ∀j,HasUniformFibers E Q (fun z => spatialLabel D (2^(phaseDepth (m j))) z.2))
    (hq : 0 < q) (hq1 : q ≤ 1)
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
    let L := fun j => predecessorProduct D (m j) E Q
      (scaleThreshold D E (m j) (S j.val) ell (natStageDirectionIndex h (tuple j))) ell
    let M := fun j => vertexCap E (spatialLabel D (2^(phaseDepth (m j)))) Q
    ∃K⊆F,K.Nonempty ∧ mass F (pointWeight E) ≤ 2*mass K (pointWeight E) ∧
      mass S0 (pointWeight E) ≤ 2^(J+1)*mass K (pointWeight E) ∧
      (∀j : Fin J,0 < L j ∧ (M j:ℝ)*L j*(F.image (f j)).card ≤
        625*transverseCost q ell*(Q:ℝ)^2*E.card) ∧
      ∀j : Fin J,∀x∈K,
        threshold (mass F (pointWeight E)) J (F.image (f j)).card ≤
          mass (classFiber K (f j) (f j x)) (pointWeight E) ∧
        ((mass F (pointWeight E):ℝ)/(E.card:ℝ))*(M j:ℝ)*(L j:ℝ)/
          (1250*(J:ℝ)*transverseCost q ell*(Q:ℝ)^2) <
            (mass (classFiber K (f j) (f j x)) (pointWeight E):ℝ) ∧
        ∀y∈classFiber K (f j) (f j x),
          spatialLabel D (2^(m j)) y=spatialLabel D (2^(m j)) x ∧
          Metric.infDist (rawVertex D (phaseDepth (m j)) y-rawVertex D (phaseDepth (m j)) x)
            (P j (spatialLabel D (2^(m j)) x):Set E4) ≤ 2*grainWidth (m j) ell := by
  intro S F P f L M
  have hFn : F.Nonempty := (Hhistory.2.2.1 J le_rfl).1
  have hFE : F⊆E.image Prod.snd := (Hhistory.2.2.1 J le_rfl).2.1.trans hS0
  have hW : 0 < mass F (pointWeight E) := original_point_mass_positive E F hFE hFn
  have hQ : 0 < Q := by
    by_contra hnot
    have hz : Q=0 := Nat.eq_zero_of_not_pos hnot
    have hp := vertexCap_pos E hE (spatialLabel D (2^(phaseDepth (m ⟨0,hJ⟩)))) Q (HU ⟨0,hJ⟩)
    simp only [hz,vertexCap,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,Nat.zero_div,lt_self_iff_false] at hp
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hEr : (0:ℝ)<E.card := by exact_mod_cast card_pos.mpr hE
  have hJr : (0:ℝ)<J := by exact_mod_cast hJ
  have hD : 0 < transverseCost q ell := transverseCost_pos hq ell
  have hcounts := history_grain_counts h E hE m hm ell hell S0 hS0 Q HU hq hq1 point tuple anchor Hsys Hhistory
  obtain ⟨K,hKF,hKn,hhalf,_hloss,hmin⟩ :=
    exists_automatic_simultaneous_dense_core (β:=fun _ : Fin J => Index × Index)
      hJ F f (pointWeight E) hW
  have hret : mass S0 (pointWeight E) ≤ 2^(J+1)*mass K (pointWeight E) := by
    calc
      _ ≤ 2^J*mass F (pointWeight E) := Hhistory.2.2.2.1
      _ ≤ 2^J*(2*mass K (pointWeight E)) := Nat.mul_le_mul_left _ hhalf
      _ = _ := by rw [pow_succ]; ring
  refine ⟨K,hKF,hKn,hhalf,hret,hcounts,?_⟩
  intro j x hx
  have hfx : f j x∈@Finset.image Index (Index × Index)
      (fun a b => Classical.propDecidable (a=b)) (f j) K := by
    simp only [mem_image]
    exact ⟨x,hx,rfl⟩
  obtain ⟨hsmall,hdensity⟩ := hmin j (f j x) hfx
  rw [classical_image_eq] at hsmall hdensity
  have hG : (0:ℝ)<(F.image (f j)).card := by
    exact_mod_cast card_pos.mpr (hFn.image (f j))
  have hcount : ((F.image (f j)).card:ℝ)*(M j:ℝ)*(L j:ℝ) ≤
      625*transverseCost q ell*(Q:ℝ)^2*E.card := by
    calc
      _ = (M j:ℝ)*(L j:ℝ)*((F.image (f j)).card:ℝ) := by ring
      _ ≤ _ := (hcounts j).2
  have hd := density_from_count (Nat.cast_nonneg (mass F (pointWeight E))) hJr hG
    (show (0:ℝ)<625*transverseCost q ell*(Q:ℝ)^2*E.card by positivity) hcount hdensity
  have he : (mass F (pointWeight E):ℝ)*(M j:ℝ)*(L j:ℝ)/
      (2*(J:ℝ)*(625*transverseCost q ell*(Q:ℝ)^2*E.card)) =
      ((mass F (pointWeight E):ℝ)/(E.card:ℝ))*(M j:ℝ)*(L j:ℝ)/
      (1250*(J:ℝ)*transverseCost q ell*(Q:ℝ)^2) := by ring
  rw [he] at hd
  refine ⟨hsmall,hd,?_⟩
  intro y hy
  simp only [classFiber,mem_filter] at hy
  have hg := tagged_same_label_near D (m j) (P j) ell y x hy.2
  exact ⟨hg.1,by simpa only [hg.1] using hg.2⟩

end NativeHistoryGrainCleanup
