import Theorems.Thm_StickyKakeya4_native_absorbed_source_envelope
import Theorems.Thm_StickyKakeya4_native_original_ad_alignment
import Theorems.Thm_StickyKakeya4_native_uniform_output_bounds
import Theorems.Thm_StickyKakeya4_native_top_scale_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NativeFinalOriginalAlignment
open NativeCommonEnvelope NativeEnvelopeGrowth NativeAlignmentParameterBudget NativeSourceSizeBounds
open NativeAbsorbedSourceEnvelope NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeSelectedParentPreparation
open NativeParentSpines NativeAngularChartSelection SmallFiberAlignment FractionalFiberAlignment
open FiniteVoronoiRealADCoarsening NativeOriginalADAlignment NativeOriginalAlignmentGeometry
open NativeOriginalParentAssembly NativeNormalizedParentOutput NativeUniformOutputBounds
open NativeFractionalReferenceComposition NativeContactFractionalComposition NativeParentRefinement
open ShearedGridADReference ActualScalarADProfiles LiteralAffineFiberCoordinates

noncomputable section
attribute [local instance] Classical.propDecidable

def originalBall (A : Finset Plane) (A' : Finset A) (j : Fin 2) (b : ℝ) (q : A) : Finset Plane :=
  (A'.filter (fun p => dist (EuclideanAlignmentPatches.euclidean (position A p))
    (EuclideanAlignmentPatches.euclidean (position A q)) < 64 * b)).image (chartPosition A j)

/-- The final assertion mentions only original retained points, literal
quantized images, their real fibers, and the original/output scale ratio. -/
def NearAlignment (A : Finset Plane) (delta t zeta chi : ℝ) : Prop :=
  ∃ mu b s : ℝ, ∃ j : Fin 2, ∃ A' : Finset A, ∃ angle : A → ℝ,
    0 < mu ∧ 0 < b ∧ delta ≤ 64 * mu ∧ 64 * mu ≤ b ∧ b ≤ 1 / 64 ∧
    (∃ ia ib : ℕ, 64 * mu = scale delta ia ∧ b = scale delta ib) ∧
    0 ≤ s ∧ s ≤ min t 1 ∧ A'.Nonempty ∧
    delta ^ (-chi) ≤ b / mu ∧
    (A.card : ℝ) ≤ (b / mu) ^ zeta * (A'.card : ℝ) ∧
    ∀ q ∈ A', |angle q| ≤ 1 ∧
      NearGraphImage (originalBall A A' j b q) mu (angle q) b (chartPosition A j q) ∧
      UniformBounds ((originalBall A A' j b q).image (vertex mu (angle q)))
        mu (angle q) b t s ((b / mu) ^ zeta) (chartPosition A j q)

/-- Parameter-absorbed near-alignment from original AD, uniformly for every
sufficiently deep top dyadic bracket. All profile, chart, spine and refinement
data are constructed inside the proof. -/
theorem exists_dyadic_original_near_alignment {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ eta chi : ℝ, 0 < eta ∧ eta ≤ 1 ∧ 0 < chi ∧ ∃ Nmin : ℕ,
      ∀ (A : Finset Plane) (delta K t : ℝ) (Nold : ℕ), Nmin ≤ Nold →
        A.Nonempty → 0 < delta → delta ≤ (128 : ℝ)⁻¹ ^ 2 →
        1 ≤ K → K ≤ delta ^ (-eta) → 0 ≤ t → t ≤ 2 →
        (1 : ℝ) / 128 ≤ scale delta Nold → scale delta Nold ≤ 1 / 64 →
        (∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) → ADBounds A delta K t →
        NearAlignment A delta t zeta chi := by
  obtain ⟨B⟩ := exists_choice hzeta
  let chi := CoverProfileStopping.separationExponent B.epsilon / (2 * (B.m : ℝ))
  have hchi : 0 < chi := by
    exact div_pos (CoverProfileStopping.separationExponent_pos _ B.epsilon_pos)
      (mul_pos (by norm_num) (Nat.cast_pos.mpr B.m_pos))
  obtain ⟨n0, hn0⟩ := source_envelope_absorbed hzeta B
  obtain ⟨nl, hnl⟩ := exists_nat_gt (4 * (Real.log 72 / Real.log 2) /
    B.epsilon ^ CoverProfileStopping.stepBudget B.epsilon)
  let Nmin := max (max n0 nl) 1
  refine ⟨B.eta, chi, B.eta_pos, B.eta_one, hchi, Nmin, ?_⟩
  intro A delta K t Nold hNmin hne hdelta hsmall hK hKsmall ht ht2 htoplo htop hdiam hAD
  have hN : 0 < Nold := lt_of_lt_of_le (by omega : 0 < 1) ((le_max_right _ _).trans hNmin)
  have hn : n0 ≤ Nold := ((le_max_left _ _).trans (le_max_left _ _)).trans hNmin
  have hnlN : nl ≤ Nold := ((le_max_right _ _).trans (le_max_left _ _)).trans hNmin
  have hdeltaone : delta ≤ 1 := hsmall.trans (by norm_num)
  have hlarge : 4 * (Real.log 72 / Real.log 2) <
      B.epsilon ^ CoverProfileStopping.stepBudget B.epsilon * (Nold : ℝ) := by
    have heps : 0 < B.epsilon ^ CoverProfileStopping.stepBudget B.epsilon := pow_pos B.epsilon_pos _
    have hh := (div_lt_iff₀ heps).mp hnl
    have hnlR : (nl : ℝ) ≤ Nold := by exact_mod_cast hnlN
    nlinarith only [hh, mul_le_mul_of_nonneg_left hnlR heps.le]
  let Q1 := radix A.card B.L1
  let Q2 := radix A.card B.L2
  have hQ1 : 4 ≤ Q1 := radix_four_le _ _
  have hQ2 : 4 ≤ Q2 := radix_four_le _ _
  obtain ⟨e, D, _hD, j, S, hout⟩ := exists_original_AD_near_alignment A delta B.epsilon K t Nold
    B.m Q1 B.L1 Q2 B.L2 B.H hne hdelta hN htop B.epsilon_pos B.epsilon_half hK ht ht2
    hlarge hdiam hAD B.m_pos hQ1 (card_le_radix_pow A.card B.L1_pos)
    hQ2 (card_le_radix_pow A.card B.L2_pos) B.H_pos
  dsimp only at hout
  rcases hout with ⟨hsource, hab, hbtop, hscale, _hnormal, A', _hsub, hne', hretain, hpatch⟩
  let ia := workingLevel D.pair.1 (D.pair.2 - D.pair.1) B.m S.index
  let ib := workingLevel D.pair.1 (D.pair.2 - D.pair.1) B.m (S.index + 1)
  let mu := scale delta ia / 64
  let b := scale delta ib
  let R : ℝ := (2 ^ (ib - ia + 6) : ℕ)
  let I : ℝ := Fintype.card (Index Nold)
  let E : ℝ := epochCost A Nold
  let F1 : ℝ := refinementCost (B.m + 1) B.L1
  let F2 : ℝ := retentionCost ((B.H + 1) + ((B.H + 1) + 1)) B.L2
  let T := profileBound B.m B.epsilon K R
  let C := productBound I E F1 F2 Q1 Q2 K R B.m B.H B.epsilon
  have hmu : 0 < mu := div_pos (scale_pos hdelta _) (by norm_num)
  have hb : 0 < b := scale_pos hdelta _
  have hR : 1 ≤ R := by
    dsimp [R]
    exact_mod_cast Nat.one_le_pow (ib - ia + 6) 2 (by omega)
  have hRpos := zero_lt_one.trans_le hR
  have hratio : b / mu = R := (div_eq_iff hmu.ne').mpr (by simpa only [mul_comm] using hscale.symm)
  have hI : 1 ≤ I := index_card_real_one_le Nold
  have hE : 1 ≤ E := epoch_cost_real_one_le hne.card_pos Nold
  have hF1 : 1 ≤ F1 := refinementCost_ge_one (B.m + 1) B.L1 (by omega)
  have hF2 : 1 ≤ F2 := retentionCost_ge_one _ B.L2 (by omega)
  have hQ1R : (1 : ℝ) ≤ Q1 := by exact_mod_cast (show 1 ≤ Q1 by omega)
  have hQ2R : (1 : ℝ) ≤ Q2 := by exact_mod_cast (show 1 ≤ Q2 by omega)
  have hT : 1 ≤ T := profileBound_ge_one B.m B.epsilon_pos.le hK hR
  have hJ := interpolationBound_ge_one B.H hR
  have hCmp := comparisonBound_ge_one hF2 hQ2R
  have hBad := ambientBound_ge_one hK
  have hBcol := columnBound_ge_one hI hF1 hQ1R hK hT
  have hBtube := tubeBound_ge_one hT
  have hX := densityBound_ge_one B.m hE hF1 hQ1R hK hR
  have hKpos := zero_lt_one.trans_le hK
  have hIpos := zero_lt_one.trans_le hI
  have hF1pos := zero_lt_one.trans_le hF1
  have hQ1pos := zero_lt_one.trans_le hQ1R
  have hJpos := zero_lt_one.trans_le hJ
  have hCmppos := zero_lt_one.trans_le hCmp
  have hBadbarpos := zero_lt_one.trans_le hBad
  have hBcolbarpos := zero_lt_one.trans_le hBcol
  have hBtubebarpos := zero_lt_one.trans_le hBtube
  have hXpos := zero_lt_one.trans_le hX
  have hCpos : 0 < C := by dsimp [C, productBound]; positivity
  have hCupper : C ≤ R ^ zeta := by
    rw [show C = envelope I E F1 F2 Q1 Q2 K R B.m B.H B.epsilon from
      productBound_eq_envelope _ _ _ _ _ _ _ _ _ _ _ hRpos]
    exact hn0 A delta K t Nold hn hne hdelta hdeltaone hK hKsmall ht2 htoplo hdiam hAD D S.index
  have hseparate := NativeAlignmentScaleSeparation.original_delta_output_separation (position A) D
    hdelta B.epsilon_pos hsmall (by simpa only [one_div] using htoplo) S.index B.m_pos
  have hRscale : 64 * (scale delta ib / scale delta ia) = R := by
    rw [← hratio]
    dsimp [b, mu]
    field_simp
  have hsep : delta ^ (-chi) ≤ b / mu := by
    rw [hratio]
    exact hseparate.2.trans_eq hRscale
  have hretcost : E * F1 * (Q1 : ℝ) ^ 2 * (Q1 : ℝ) ^ 2 *
      (angularCost D.pair.1 D.pair.2 B.m : ℝ) * (64 ^ 2 * F2) * 260 ^ 2 ≤ C :=
    (retention_le_comparison_density B.m (zero_le_one.trans hE) (zero_le_one.trans hF1)
      (zero_le_one.trans hF2) hQ1R hQ2R hK hRpos.le
      (NativeAngularCostBound.angularCost_le_extent_root D.pair.1 D.pair.2 S.index B.m_pos)).trans
      (product_dominates_comparison_density B.m B.H hI hE hF1 hF2 hQ1R hQ2R hK hR B.epsilon_pos.le)
  have hret : (A.card : ℝ) ≤ (b / mu) ^ zeta * (A'.card : ℝ) := by
    have hretR : (A.card : ℝ) ≤ (E * F1 * (Q1 : ℝ) ^ 2 * (Q1 : ℝ) ^ 2 *
        (angularCost D.pair.1 D.pair.2 B.m : ℝ) * (64 ^ 2 * F2) * 260 ^ 2) * (A'.card : ℝ) := by
      dsimp only [E, F1, F2]
      exact_mod_cast hretain
    rw [hratio]
    exact hretR.trans (mul_le_mul_of_nonneg_right (hretcost.trans hCupper) (Nat.cast_nonneg _))
  refine ⟨mu, b, D.exponent, j, A', (fun q => S.angle (ActualTubeFootprintProfiles.grid (position A) b q)),
    hmu, hb, hsource, hab, hbtop, ⟨ia, ib, by dsimp [mu]; ring, rfl⟩,
    D.exponent_nonneg, D.exponent_le, hne', hsep, hret, ?_⟩
  intro q hq
  obtain ⟨F, hball, hnear, hreal, hdensity⟩ := hpatch q hq
  have hcost := actual_cost_bounds D hdelta B.epsilon_pos.le hK ht ht2 S.index B.m Q1 B.L1 B.H
    B.m_pos (by omega)
  dsimp only at hcost
  rcases hcost with ⟨hloss, hbad, hcol, htube, hden, hfull, hinterp⟩
  have hlosspos := zero_lt_one.trans_le (D.loss_ge_one hdelta B.epsilon_pos.le hK ht)
  have hBadpos : 0 < adConstant K t := by
    have hKpos := zero_lt_one.trans_le hK
    unfold adConstant ShearedGridADReference.referenceFactor
    positivity
  have hColpos : 0 < contactColumnConstant 2 K D.loss t
      (spineConstant Nold (B.m + 1) Q1 B.L1 K t D.loss) := by
    rw [NativeParameterConstants.column_cost_expand Nold (B.m + 1) Q1 B.L1 (by omega) (by omega) hK hlosspos]
    have hsp := spatialConstant_pos (t := t) hK
    positivity
  have hTubepos : 0 < tubeConstant D.loss := by unfold tubeConstant; positivity
  have hComparison : 0 < comparisonCost (B.H + 1) B.L2 Q2 := by
    change 0 < comparisonBound F2 Q2
    exact zero_lt_one.trans_le hCmp
  have hrec : 1 ≤ densityBound E F1 Q1 K R B.m * density F.residue F.cap (2 ^ (ib - ia + 6)) t :=
    hdensity.trans (mul_le_mul_of_nonneg_right hden F.density_pos.le)
  have htubecost : 170100 * D.loss * (2 : ℝ) ^ D.exponent ≤ C := by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hloss (by norm_num))
      (by positivity)).trans
    exact product_dominates_tube B.m B.H hI hE hF1 hF2 hQ1R hQ2R hK hR B.epsilon_pos.le
      (D.exponent_le.trans (min_le_right _ _))
  have hst : D.exponent ≤ t := D.exponent_le.trans (min_le_left _ _)
  have huniform : UniformBounds (F.points.image (vertex mu (S.angle (ActualTubeFootprintProfiles.grid (position A) b q))))
      mu (S.angle (ActualTubeFootprintProfiles.grid (position A) b q)) b t D.exponent C (chartPosition A j q) :=
    NativeUniformOutputBounds.AllRealBounds.to_uniform_majorants hreal hmu hb F.density_pos D.exponent_nonneg hst ht2
      hComparison hBadpos hColpos hTubepos hJ hCmp hBad hBcol hBtube hX hrec
      le_rfl hbad hcol htube (hinterp t ht ht2)
      (hfull D.exponent D.exponent_nonneg (hst.trans ht2))
      (hfull (t - D.exponent) (sub_nonneg.mpr hst) (by linarith [D.exponent_nonneg])) htubecost
  have hfinal := NativeUniformOutputBounds.UniformBounds.mono huniform hmu hb hCpos hCupper
  rw [← hratio] at hfinal
  change originalBall A A' j b q = F.points at hball
  rw [← hball] at hnear hfinal
  exact ⟨S.angle_bound _, hnear, hfinal⟩

/-- Full original small-scale quantifiers. The constants eta, chi and delta0
are chosen from zeta before the original AD source and its scale are supplied. -/
theorem exists_original_near_alignment {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ eta chi delta0 : ℝ, 0 < eta ∧ eta ≤ 1 ∧ 0 < chi ∧ 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (A : Finset Plane) (delta K t : ℝ),
        A.Nonempty → 0 < delta → delta ≤ delta0 → 1 ≤ K → K ≤ delta ^ (-eta) →
        0 ≤ t → t ≤ 2 → (∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) → ADBounds A delta K t →
        NearAlignment A delta t zeta chi := by
  obtain ⟨eta, chi, heta, hetaone, hchi, Nmin, hmain⟩ := exists_dyadic_original_near_alignment hzeta
  refine ⟨eta, chi, NativeTopScaleSelection.deltaThreshold Nmin, heta, hetaone, hchi,
    NativeTopScaleSelection.deltaThreshold_pos Nmin, ?_, ?_⟩
  · exact (min_le_left _ _).trans (by norm_num : (128 : ℝ)⁻¹ ^ 2 ≤ 1)
  · intro A delta K t hne hdelta hthreshold hK hKsmall ht ht2 hdiam hAD
    obtain ⟨N, hN, hsmall, htoplo, htop⟩ := NativeTopScaleSelection.choose_top_scale Nmin hdelta hthreshold
    exact hmain A delta K t N hN hne hdelta hsmall hK hKsmall ht ht2 htoplo.le htop hdiam hAD

/-- The standard AD source formulation, with its original delta^(-eta)
constant. No auxiliary dyadic, tube, angular or output-profile premise remains. -/
theorem original_AD_near_alignment {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ eta chi delta0 : ℝ, 0 < eta ∧ 0 < chi ∧ 0 < delta0 ∧
      ∀ (A : Finset Plane) (delta t : ℝ),
        A.Nonempty → 0 < delta → delta ≤ delta0 → 0 ≤ t → t ≤ 2 →
        (∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) → ADBounds A delta (delta ^ (-eta)) t →
        NearAlignment A delta t zeta chi := by
  obtain ⟨eta, chi, delta0, heta, _hetaone, hchi, hdelta0, hdelta01, hmain⟩ :=
    exists_original_near_alignment hzeta
  refine ⟨eta, chi, delta0, heta, hchi, hdelta0, ?_⟩
  intro A delta t hne hdelta hdeltasmall ht ht2 hdiam hAD
  have hd1 := hdeltasmall.trans hdelta01
  have hK : 1 ≤ delta ^ (-eta) := by
    rw [Real.rpow_neg_eq_inv_rpow]
    exact Real.one_le_rpow ((one_le_inv₀ hdelta).mpr hd1) heta.le
  exact hmain A delta (delta ^ (-eta)) t hne hdelta hdeltasmall hK le_rfl ht ht2 hdiam hAD

end
end NativeFinalOriginalAlignment
