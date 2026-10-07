import Theorems.Thm_StickyKakeya4_native_matched_pair_height_lower
import Theorems.Thm_StickyKakeya4_native_actual_sparse_reference_admission

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeActualPairHeightDensity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeLocalParentSource NativeMiddleWindowBalance CanonicalConfiguredE4Bridge
open NativeConfiguredIncidenceFibers NativeActualSparseReferenceAdmission NativeMatchedPairHeightLower

/-- The existing sparse-reference admission supplies the actual coarse
shading lower bound internally. The conclusion counts G(T), never the full
tube family, against any unchanged original baseline B containing T. The
cutoff and scalar input losses retain their original pre-source order. -/
theorem exists_actual_density (e window : ℝ) (he : 0 < e) (hw : 0 < window) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta)
      (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
      (a zeta : ℝ), 0 ≤ zeta → HasOriginalBackbone D original R a level zeta →
      ∀ (Eref H T B : Finset (Fin n × Index)) (m : ℕ), 6 ≤ m →
      ∀ (p : Parent) (etaRef : ℝ)
        (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef),
      T ⊆ Eref → Eref ⊆ incidences original → T ⊆ B → B ⊆ incidences original →
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
      (∀ x ∈ T.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
        ∀ y ∈ T.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
        x ≠ y → (mu m * (R0 : ℝ)) / 64 ≤ dist x y) →
      let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0
      let G := T.image (fun z => (cfg z.2, outputTube h R Eref a m b p href z.1))
      let Z := B.image (fun z => cfg z.2 (3 : Fin 4))
      Z.Nonempty ∧
        (16 / (18 * (5 : ℝ) ^ 4)) * (64 / ((2 ^ b : ℕ) : ℝ)) ^ (5 * e / 16 - 3) ≤
          (G.card : ℝ) / Z.card := by
  obtain ⟨eps0, heps0, Hadmit⟩ := exists_actual_sparse_admission e window he hw
  refine ⟨eps0, heps0, ?_⟩
  intro n D eta h original R level a zeta hzeta HB Eref H T B m hm p etaRef href
    hTE hEorig hTB hB hparent hsmall heta hprofile population cost hpop hcost
    hpopulation hretain b hb hmb hwindow hpaid s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch hpointSep
  obtain ⟨Q, hsep, hQP, _hQne, _hnative, _hcompact, _hupper, hshade⟩ :=
    Hadmit n D eta h original R level a zeta hzeta HB Eref H T m p etaRef href
      hTE hEorig hparent hsmall heta hprofile population cost hpop hcost hpopulation hretain
      b hb hmb hwindow hpaid
  exact of_admitted_core h original HB.1 HB.2.2.1 R Eref T B hTB hB level m b hm hb
    HB.2.1 hmb p href hparent s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch hpointSep
    Q hQP hsep hshade

end NativeActualPairHeightDensity
