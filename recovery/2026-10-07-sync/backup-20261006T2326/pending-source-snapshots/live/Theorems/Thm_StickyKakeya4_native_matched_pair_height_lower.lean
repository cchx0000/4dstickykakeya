import Theorems.Thm_StickyKakeya4_native_matched_shadow_configured_output
import Theorems.Thm_StickyKakeya4_native_matched_shadow_mass
import Theorems.Thm_StickyKakeya4_native_matched_height_bound

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeMatchedPairHeightLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeRelativeCoarseReadback NativeLocalParentSource CanonicalConfiguredE4Bridge
open NativeConfiguredIncidenceFibers NativeMatchedShadowConfiguredOutput NativeMatchedShadowMass

/-- The half-mesh cell volume contributes the literal factor 16. -/
lemma ratio_of_cell_mass (delta exponent G Z : ℝ) (hd : 0 < delta) (hZ : 0 < Z)
    (hmass : delta ^ exponent ≤ (5 : ℝ) ^ 4 * G * (delta / 2) ^ 4)
    (hheight : delta * Z ≤ 18) :
    (16 / (18 * (5 : ℝ) ^ 4)) * delta ^ (exponent - 3) ≤ G / Z := by
  have hp4 : delta ^ exponent = delta ^ (exponent - 4) * delta ^ (4 : ℕ) := by
    calc
      _ = delta ^ ((exponent - 4) + (4 : ℝ)) := by congr 1; ring
      _ = delta ^ (exponent - 4) * delta ^ (4 : ℝ) := Real.rpow_add hd _ _
      _ = _ := by rw [Real.rpow_natCast]
  have hp1 : delta ^ (exponent - 3) = delta ^ (exponent - 4) * delta := by
    calc
      _ = delta ^ ((exponent - 4) + 1) := by congr 1; ring
      _ = delta ^ (exponent - 4) * delta ^ (1 : ℝ) := Real.rpow_add hd _ _
      _ = _ := by rw [Real.rpow_one]
  have hpair : 16 * delta ^ (exponent - 4) ≤ (5 : ℝ) ^ 4 * G := by
    apply (mul_le_mul_iff_of_pos_right (pow_pos hd 4)).mp
    calc
      _ = 16 * delta ^ exponent := by rw [hp4]; ring
      _ ≤ 16 * ((5 : ℝ) ^ 4 * G * (delta / 2) ^ 4) :=
        mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ = _ := by ring
  have hcross : 16 * delta ^ (exponent - 3) * Z ≤ (18 * (5 : ℝ) ^ 4) * G := by
    calc
      _ = (16 * delta ^ (exponent - 4)) * (delta * Z) := by rw [hp1]; ring
      _ ≤ (16 * delta ^ (exponent - 4)) * 18 :=
        mul_le_mul_of_nonneg_left hheight
          (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos hd _).le)
      _ = 18 * (16 * delta ^ (exponent - 4)) := by ring
      _ ≤ 18 * ((5 : ℝ) ^ 4 * G) := mul_le_mul_of_nonneg_left hpair (by norm_num)
      _ = _ := by ring
  apply (le_div_iff₀ hZ).mpr
  calc
    _ = (16 * delta ^ (exponent - 3) * Z) / (18 * (5 : ℝ) ^ 4) := by ring
    _ ≤ G := (div_le_iff₀ (by positivity : (0 : ℝ) < 18 * (5 : ℝ) ^ 4)).mpr hcross

/-- The lower bound returned by the actual sparse-reference admission
theorem implies density of the SAME configured graph. The final hshade
argument is exactly that theorem's last output, evaluated on its literal Q
and selected shading. No lower bound for G is assumed. The baseline B may
be larger than the selected T. Z is its physical configured-height image;
comparison with old translated-height labels requires the actual single-height property. -/
theorem of_admitted_core {n : ℕ} {D : FiniteScaleSource n} {eta etaS a e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (R : Finset (Fin n)) (Eref T B : Finset (Fin n × Index)) (hTB : T ⊆ B)
    (hB : B ⊆ incidences original) (level m b : ℕ) (hm : 6 ≤ m) (hb : 6 ≤ b)
    (hdy : D.thickness = (2 : ℝ)⁻¹ ^ level) (hmb : m + b ≤ level)
    (p : Parent) (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hparent : ∀ z ∈ T, z.1 ∈ parentLabels D R a (2 ^ m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t u v, |F t u v| ≤ 1 / 4) (hCfg : ∀ t u v, |Fcfg t u v| ≤ 1 / 4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m * (R0 : ℝ))
    (hmatch : mu m * (R0 : ℝ) = 4096 / ((2 ^ b : ℕ) : ℝ))
    (hpointSep : ∀ x ∈ T.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
      ∀ y ∈ T.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
      x ≠ y → (mu m * (R0 : ℝ)) / 64 ≤ dist x y)
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
    let Z := B.image (fun z => cfg z.2 (3 : Fin 4))
    Z.Nonempty ∧
      (16 / (18 * (5 : ℝ) ^ 4)) * (64 / ((2 ^ b : ℕ) : ℝ)) ^ (5 * e / 16 - 3) ≤
        (G.card : ℝ) / Z.card := by
  intro cfg G Z
  let Delta : ℝ := 64 / ((2 ^ b : ℕ) : ℝ)
  have hD : 0 < Delta := by dsimp [Delta]; positivity
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
  have hcounts := actual_output_image_bounds h original horiginal ha R Eref T m b hm hN hNM
    p hQ hS (hTB.trans hB) hparent s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch hpointSep
  have hpairs : (shadow.card : ℝ) ≤ (5 : ℝ) ^ 4 * (G.card : ℝ) := by
    exact_mod_cast hcounts.2.2.1
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
  have hTne : T.Nonempty := by
    by_contra hnot
    have hTe : T = ∅ := not_nonempty_iff_eq_empty.mp hnot
    have hz := hmass
    simp only [G, hTe, image_empty, card_empty, Nat.cast_zero, mul_zero, zero_mul] at hz
    exact (not_le_of_gt (Real.rpow_pos_of_pos hD _)) hz
  have hZne : Z.Nonempty := (hTne.mono hTB).image _
  have hZpos : (0 : ℝ) < Z.card := by exact_mod_cast card_pos.mpr hZne
  have hheight := NativeMatchedHeightBound.baseline_height_bound h original horiginal ha
    B hB m b hb p s P hP hd F Fcfg R0 hR0 hmatch
  have hheight' : Delta * (Z.card : ℝ) ≤ 18 := by
    have hh := (le_div_iff₀ hD).mp hheight
    simpa only [mul_comm] using hh
  exact ⟨hZne, ratio_of_cell_mass Delta (5 * e / 16) (G.card : ℝ) (Z.card : ℝ)
    hD hZpos hmass hheight'⟩

end NativeMatchedPairHeightLower
