import Theorems.Thm_StickyKakeya4_native_sharp_population_admission
import Theorems.Thm_StickyKakeya4_native_normalized_cell_source_angular

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

noncomputable section
namespace NativeSharpReferenceAngularUpper
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeSpatialAngularGeometry
open NativeSharpPopulationAdmission NativeNormalizedPopulationAdmissionBudget
open NativeRankExponentHierarchy NativeLocalParentSource NativeMiddleWindowBalance
open NativeNormalizedCellSourceAngular NativeNormalizedCellAngularMenu
open NativeRelativeCoarseReadback NativeJointUniformCoarseRelations NativeUnitParentNormalization
open NativeFixedCompactKakeyaExponent NativeQueriedVertexWeights

lemma angular_menu_mono {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m M : ℕ) (p : Parent) {T E : Finset (Fin n × Index)} (hTE : T⊆ E) (q : Index) :
    angularMenu D a m M p T q⊆ angularMenu D a m M p E q := by
  exact image_subset_image (filter_subset_filter _ hTE)

/-- The selected sharp population parent pays the unchanged reference
parent as well; subsequent edge cuts use its angular union by inclusion. -/
lemma reference_population {n : ℕ} {D : FiniteScaleSource n} {population : ℝ}
    (hd : 0≤ D.thickness) {P : Finset (Fin n)} {H E : Finset (Fin n × Index)}
    (hHE : H⊆ E) (hpop : population*P.card≤ D.thickness*H.card) :
    population*P.card≤ D.thickness*E.card :=
  hpop.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hHE)) hd)

/-- The local exponent, hierarchy cap, and original-scale cutoff are all
chosen before D. The source's literal rank mass and H1/H2 costs pay every
local-admission budget. The angular upper uses the reference E2 parent and
therefore survives every subsequent retained subset without a new admission.

The two explicit relative-scale window inequalities remain hypotheses. -/
theorem exists_actual_reference_angular_upper {epsilon window : ℝ}
    (hepsilon : 0< epsilon) (hwindow : 0< window) :
    ∃e localEta initialCap : ℝ,0< e ∧ 0< localEta ∧ 0< initialCap ∧
      ∀g : ℕ,∃delta0 : ℝ,0< delta0 ∧ delta0≤ 1/8 ∧
      ∀eta0 c tau seed zeta c2 : ℝ,
        0< eta0 → eta0≤ initialCap → 0≤ c → c≤ 1 →
        tau≤ commonBudget eta0 c/1024 → seed≤ tau/16384 →
        0≤ zeta → zeta≤ seed/256 → c2=commonBudget eta0 c/4 →
      ∀(rank : Fin 4) (ell : ℕ),ell≤ 3 →
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta a r : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0≤ eta → eta≤ seed/8 → D.thickness≤ delta0 → D.thickness≤ r → r≤ 1 →
      ∀(original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ),
        HasOriginalBackbone D original R a level zeta →
      ∀(E2 : Finset (Fin n × Index)) (points : Finset Index),
        E2.Nonempty → E2⊆ retained original R →
        r^((2*(ell:ℝ)+1)*rankLoss eta0 c rank)*(E2.card:ℝ)≤ 
          (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ) →
      ∀F1 F2 G Q1 Q2 : ℕ,0< F1 → 0< G → 1≤ Q1 → 1≤ Q2 → G≤ F2 →
        (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta)≤ D.thickness^(-(seed/8)) →
        (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta)≤ D.thickness^(-c2) →
      ∀m : ℕ,m≤ level → D.thickness≤ (64/((2^m:ℕ):ℝ))^2 →
      ∀p : Parent,∀hp : (parentLabels D R a (2^m) p).Nonempty,
      ∀H : Finset (Fin n × Index),H⊆ parentEdges D a (2^m) E2 p →
        let mu := ((r^(rankLoss eta0 c rank)/(4*((g:ℝ)+1)))*(WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)/
          (2*(F1:ℝ)*G*(E2.card:ℝ)))*D.thickness^eta
        mu*(parentLabels D R a (2^m) p).card≤ D.thickness*H.card →
        let E := parentEdges D a (2^m) E2 p
        IsWangZakharovNativeFiniteInput (source h R E a m p) localEta ∧
        (∀i,(source h R E a m p).line i∈fixedCompactClass) ∧
        ∀s : ℕ,s≤ level-m+6 →
          1/((2^s:ℕ):ℝ)≤ (source h R E a m p).thickness^window →
          (source h R E a m p).thickness/(1/((2^s:ℕ):ℝ))≤ (source h R E a m p).thickness^window →
        ∀Q : ℕ,HasUniformFibers E Q (doublePair h R a m p hp (2^s)) →
          HasUniformFibers E Q (fun z => (doublePair h R a m p hp (2^s) z).2) →
        ∀T⊆ E,∀q : Index,
          ((angularMenu D a m (2^s) p T q).card:ℝ)≤ 
            81*(Q:ℝ)^4*(source h R E a m p).thickness^(-(7*(window*e/32)))*
              (64/((2^s:ℕ):ℝ))^(-extremalExponent-epsilon) := by
  obtain ⟨e,localEta,eps0,he,hlocal,heps,hUpper⟩ := exists_source_angular_upper hepsilon hwindow
  let profileExp := window*e/32
  have hprofile : 0< profileExp := by dsimp [profileExp]; positivity
  let initialCap := min (localEta/80) (profileExp/4)
  refine ⟨e,localEta,initialCap,he,hlocal,lt_min (by positivity) (by positivity),?_⟩
  intro g
  obtain ⟨delta0,hd0,hd01,hBudget⟩ := exists_sharp_admission_cutoff localEta profileExp eps0
    hlocal hprofile heps g
  refine ⟨delta0,hd0,hd01,?_⟩
  intro eta0 c tau seed zeta c2 heta0 hcap hc hc1 htau hseed hzeta hzseed hc2 rank ell hell
    n D eta a r h heta hetaseed hdsmall hdr hr1 original R level Hbackbone E2 points hE2n hE2R hmass
    F1 F2 G Q1 Q2 hF1 hG hQ1 hQ2 hGF H1 H2 m hm hsquare p hp H hHE muStored hpop
  let E := parentEdges D a (2^m) E2 p
  let loss := rankLoss eta0 c rank
  let W : ℝ := (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)
  let mu := ((r^loss/(4*((g:ℝ)+1)))*W/(2*(F1:ℝ)*G*(E2.card:ℝ)))*D.thickness^eta
  have hd := h.1.2.1
  have hr : 0< r := hd.trans_le hdr
  have hloss : 0≤ loss := by dsimp [loss,rankLoss]; positivity
  have hcount : (0:ℝ)< E2.card := by exact_mod_cast hE2n.card_pos
  have hellr : (ell:ℝ)≤ 3 := by exact_mod_cast hell
  have hmass7 : r^(7*loss)*(E2.card:ℝ)≤ W := by
    have hexp : (2*(ell:ℝ)+1)*loss≤ 7*loss := by nlinarith only [hellr,hloss]
    exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 hexp) (Nat.cast_nonneg E2.card)).trans hmass
  have hW : 0< W := (mul_pos (Real.rpow_pos_of_pos hr _) hcount).trans_le hmass7
  have hmu : 0< mu := by dsimp [mu]; positivity
  obtain ⟨hbase,hcw,hprof⟩ := hierarchy_admission_margins heta0 hc hc1
    (hcap.trans (min_le_left _ _)) (hcap.trans (min_le_right _ _)) htau hseed hetaseed hzseed hc2 rank 3 (by omega)
  have hbase' : eta+8*loss+seed/8+c2≤ localEta/8 := by
    norm_num only [Nat.cast_ofNat] at hbase
    dsimp [loss]
    linarith only [hbase]
  have hDelta : (0:ℝ)< 64/((2^m:ℕ):ℝ) := by positivity
  obtain ⟨hsmall,hAd,hCw,hDen,hProf⟩ := hBudget D.thickness (64/((2^m:ℕ):ℝ)) r eta zeta loss
    (seed/8) c2 0 W E2.card 1 F1 F2 G Q1 Q2 hd hdsmall hDelta hsquare hdr heta hloss
    hcount hF1 hG (by norm_num) hQ1 hQ2 hGF hmass7 hbase' (by positivity) hcw hprof H1 H2
    (by simp)
  have hThickness : (source h R E a m p).thickness=D.thickness/(64/((2^m:ℕ):ℝ)) := by
    rw [source_thickness]
    field_simp
  rw [←hThickness] at hsmall hAd hCw hDen hProf
  simp only [div_one] at hDen
  have hE : E⊆ incidences original := (filter_subset _ _).trans (hE2R.trans (filter_subset _ _))
  have hlabels : ∀z∈E,z.1∈parentLabels D R a (2^m) p := by
    intro z hz
    obtain ⟨hz,hzp⟩ := mem_filter.mp hz
    exact (mem_parentLabels D R a (2^m) p z.1).mpr ⟨(mem_filter.mp (hE2R hz)).2,hzp⟩
  have hReference := reference_population hd.le hHE hpop
  obtain ⟨hNative,hCompact⟩ := NativeNormalizedCellSourceUpper.source_native_from_population h hzeta
    original R level Hbackbone m hm p E hE hlabels hp mu hmu hReference hAd hCw hDen
  refine ⟨hNative,hCompact,?_⟩
  intro s hs hcoarse hfine Q hPair hPoint T hTE q
  exact (Nat.cast_le.mpr (card_le_card (angular_menu_mono D a m (2^s) p hTE q))).trans
    (hUpper localEta hlocal le_rfl n D eta zeta a h hzeta original R level Hbackbone m hm p E hE hlabels hp
      mu hmu hReference hAd hCw hDen hsmall hProf s hs hcoarse hfine Q hPair hPoint q)

end NativeSharpReferenceAngularUpper
