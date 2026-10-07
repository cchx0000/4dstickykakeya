import Theorems.Thm_StickyKakeya4_native_matched_shadow_configured_output
import Theorems.Thm_StickyKakeya4_native_matched_shadow_mass
import Theorems.Thm_StickyKakeya4_native_actual_sparse_reference_admission

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeActualBaselineGraphMass
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeRelativeCoarseReadback NativeLocalParentSource CanonicalConfiguredE4Bridge
open NativeConfiguredIncidenceFibers NativeMatchedShadowConfiguredOutput NativeMatchedShadowMass
open NativeActualSparseReferenceAdmission NativeMiddleWindowBalance

/-- The actual admitted shading supplies a normalized TOTAL of distinct
configured pairs. No height count or original-edge cardinal is substituted.
Only the inverse shadow menu is needed, so point separation is unnecessary. -/
theorem of_admitted_core {n : ℕ} {D : FiniteScaleSource n} {eta etaS a e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (R : Finset (Fin n)) (Eref T : Finset (Fin n × Index)) (hT : T ⊆ incidences original) (level m b : ℕ) (hm : 6 ≤ m) (_hb : 6 ≤ b)
    (hdy : D.thickness = (2 : ℝ)⁻¹ ^ level) (hmb : m + b ≤ level)
    (p : Parent) (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hparent : ∀ z ∈ T, z.1 ∈ parentLabels D R a (2 ^ m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t u v, |F t u v| ≤ 1 / 4) (hCfg : ∀ t u v, |Fcfg t u v| ≤ 1 / 4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m * (R0 : ℝ))
    (hmatch : mu m * (R0 : ℝ) = 4096 / ((2 ^ b : ℕ) : ℝ))
    (Q : Finset Parent)
    (hQP : Q ⊆ (univ : Finset (Fin (parentLabels D R a (2 ^ m) p).card)).image
      (parentLabel (source h R Eref a m p) 0 (2 ^ b)))
    (hsep : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → 64 / ((2 ^ b : ℕ) : ℝ) ≤
      dist (direction ((source h R Eref a m p).line
        (NativeCoarseDirectionThinning.representative hS univ 0 (2 ^ b) u)))
        (direction ((source h R Eref a m p).line
          (NativeCoarseDirectionThinning.representative hS univ 0 (2 ^ b) v))))
    (hshade : (64 / ((2 ^ b : ℕ) : ℝ)) ^ (5 * e / 16) ≤
      (wzTotalShadingVolume (NativeCoarseCellSource.source hS 0 (level - m + 6) b Q
        (NativeCoarseDirectionThinning.representative hS univ 0 (2 ^ b))
        (incidences (sourceCells D R T a (2 ^ m) p)) hsep)).toReal) :
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0
    let G := T.image (fun z => (cfg z.2, outputTube h R Eref a m b p hS z.1))
    (16/(5:ℝ)^4)*(64/((2^b:ℕ):ℝ))^(5*e/16) ≤
      (64/((2^b:ℕ):ℝ))^4*(G.card:ℝ) := by
  intro cfg G
  let Delta : ℝ := 64 / ((2 ^ b : ℕ) : ℝ)
  have hQ : (parentLabels D R a (2 ^ m) p).Nonempty := card_pos.mp hS.1.1
  let shadow := T.image (doublePair h R a m p hQ (2 ^ b))
  have hmlevel : m ≤ level := by omega
  have hbl : b ≤ level - m + 6 := by omega
  have hN : ((2 ^ m : ℕ) : ℝ) * D.thickness ≤ 1 :=
    NativeCompactAncestorRegularity.dyadic_parent_scale hdy ⟨m, by omega⟩
  have hNM : ((2 ^ m : ℕ) : ℝ) * D.thickness * ((2 ^ b : ℕ) : ℝ) ≤ 64 := by
    calc
      _ = ((2 ^ (m + b) : ℕ) : ℝ) * D.thickness := by
        push_cast
        rw [pow_add]
        ring
      _ ≤ 1 := NativeCompactAncestorRegularity.dyadic_parent_scale hdy ⟨m + b, by omega⟩
      _ ≤ 64 := by norm_num
  have hcounts := actual_inverse_output_image_bounds h original horiginal ha R Eref T m b hm hN hNM
    p hQ hS hT hparent s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch.le
  have hpairs : (shadow.card : ℝ) ≤ (5 : ℝ) ^ 4 * (G.card : ℝ) := by
    exact_mod_cast hcounts.2
  have hmass : Delta ^ (5 * e / 16) ≤ (5 : ℝ) ^ 4 * (G.card : ℝ) * (Delta / 2) ^ 4 := by
    calc
      _ ≤ (wzTotalShadingVolume (NativeCoarseCellSource.source hS 0 (level - m + 6) b Q
          (NativeCoarseDirectionThinning.representative hS univ 0 (2 ^ b))
          (incidences (sourceCells D R T a (2 ^ m) p)) hsep)).toReal := hshade
      _ ≤ (wzTotalShadingVolume (NativeFullCoarseShadow.fullSource hS univ 0 (level - m + 6) b
          (incidences (sourceCells D R T a (2 ^ m) p)))).toReal :=
        core_mass_le_full hS univ 0 (level - m + 6) b _ Q hQP hsep
      _ = (shadow.card : ℝ) * (Delta / 2) ^ 4 := by
        rw [mixed_full_pair_mass h R Eref T a level m b p hQ hparent hS hdy hmlevel hbl]
        congr 1
        dsimp only [Delta]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hpairs (by positivity)
  have hc : 0 < (5:ℝ)^4 := by positivity
  have hh : 16*Delta^(5*e/16) ≤ (5:ℝ)^4*(Delta^4*(G.card:ℝ)) := by
    have ht := mul_le_mul_of_nonneg_left hmass (by norm_num : (0:ℝ) ≤ 16)
    convert ht using 1 <;> ring
  have hdiv := (div_le_iff₀ hc).mpr hh
  convert hdiv using 1 <;> ring

/-- Actual baseline sparse admission is invoked here on the same E1/R/T.
The normalized graph lower is a conclusion, not a supplied certificate. -/
theorem exists_actual_baseline_mass (e window : ℝ) (he : 0 < e) (hw : 0 < window) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta)
      (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
      (a zeta : ℝ), 0 ≤ zeta → HasOriginalBackbone D original R a level zeta →
      ∀ (Eref H T : Finset (Fin n × Index)) (m : ℕ), 6 ≤ m →
      ∀ (p : Parent) (etaRef : ℝ)
        (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef),
      T ⊆ Eref → Eref ⊆ incidences original →
      (∀ z ∈ T, z.1 ∈ parentLabels D R a (2 ^ m) p) →
      (source h R Eref a m p).thickness ≤ eps0 → etaRef ≤ window * e / 256 →
      (64 : ℝ) ^ 3 * (source h R Eref a m p).thickness ^ (window * e / 16) ≤ D.thickness ^ zeta →
      ∀ population cost : ℝ, 0 < population → 0 < cost →
        population * (parentLabels D R a (2 ^ m) p).card ≤ D.thickness * H.card →
        (H.card : ℝ) ≤ cost * T.card →
      ∀ b : ℕ, 6 ≤ b → m + b ≤ level →
        64 / ((2 ^ b : ℕ) : ℝ) ≤ (source h R Eref a m p).thickness ^ window →
        retentionFactor cost population ≤ (64 / ((2 ^ b : ℕ) : ℝ)) ^ (-(e / 32)) →
      ∀ (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
        (hd : Module.finrank ℝ P = tangentDim s)
        (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ),
      (∀ t u v, |F t u v| ≤ 1 / 4) → (∀ t u v, |Fcfg t u v| ≤ 1 / 4) →
      ∀ (R0 : ℕ), 0 < R0 → rho m ≤ mu m * (R0 : ℝ) →
        mu m * (R0 : ℝ) = 4096 / ((2 ^ b : ℕ) : ℝ) →
      let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0
      let G := T.image (fun z => (cfg z.2, outputTube h R Eref a m b p href z.1))
      (16/(5:ℝ)^4)*(64/((2^b:ℕ):ℝ))^(5*e/16) ≤
        (64/((2^b:ℕ):ℝ))^4*(G.card:ℝ) := by
  obtain ⟨eps0, heps0, Hadmit⟩ := exists_actual_sparse_admission e window he hw
  refine ⟨eps0, heps0, ?_⟩
  intro n D eta h original R level a zeta hzeta HB Eref H T m hm p etaRef href
    hTE hEorig hparent hsmall heta hprofile population cost hpop hcost
    hpopulation hretain b hb hmb hwindow hpaid s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
  obtain ⟨Q, hsep, hQP, _hQne, _hnative, _hcompact, _hupper, hshade⟩ :=
    Hadmit n D eta h original R level a zeta hzeta HB Eref H T m p etaRef href
      hTE hEorig hparent hsmall heta hprofile population cost hpop hcost hpopulation hretain
      b hb hmb hwindow hpaid
  exact of_admitted_core h original HB.1 HB.2.2.1 R Eref T (hTE.trans hEorig) level m b hm hb
    HB.2.1 hmb p href hparent s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
    Q hQP hsep hshade

end NativeActualBaselineGraphMass
