import Theorems.Thm_StickyKakeya4_native_matched_shadow_configured_output

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeMatchedShadowMultiplicity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeRelativeCoarseReadback NativeLocalParentSource CanonicalConfiguredE4Bridge
open NativeConfiguredIncidenceFibers NativeMatchedShadowConfiguredOutput

/-- The actual configured incidence graph is bounded by the SAME full
reference shadow with a fixed factor. The fine native source is Eref; the
shadow shading consists of the literal selected A edges. The original depth
guard supplies both relative-scale bounds internally. -/
theorem actual_average_degree_le_full {n : ℕ} {D : FiniteScaleSource n} {eta etaS a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (R : Finset (Fin n)) (Eref A : Finset (Fin n × Index)) (level m b : ℕ) (hm : 6 ≤ m)
    (hdy : D.thickness = (2 : ℝ)⁻¹ ^ level) (hmb : m + b ≤ level)
    (p : Parent) (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hA : A ⊆ incidences original)
    (hparent : ∀ z ∈ A, z.1 ∈ parentLabels D R a (2 ^ m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t u v, |F t u v| ≤ 1 / 4) (hCfg : ∀ t u v, |Fcfg t u v| ≤ 1 / 4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m * (R0 : ℝ))
    (hmatch : mu m * (R0 : ℝ) = 4096 / ((2 ^ b : ℕ) : ℝ))
    (hsep : ∀ x ∈ A.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
      ∀ y ∈ A.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
      x ≠ y → (mu m * (R0 : ℝ)) / 64 ≤ dist x y) :
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0
    let output := A.image (fun z => (cfg z.2, outputTube h R Eref a m b p hS z.1))
    (output.card : ℝ) / (output.image Prod.fst).card ≤
      (165 : ℝ) ^ 4 *
        (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource hS univ 0 (level - m + 6) b
            (incidences (sourceCells D R A a (2 ^ m) p)))).toReal := by
  intro cfg output
  have hQ : (parentLabels D R a (2 ^ m) p).Nonempty := card_pos.mp hS.1.1
  let shadow := A.image (doublePair h R a m p hQ (2 ^ b))
  have hmlevel : m ≤ level := by omega
  have hb : b ≤ level - m + 6 := by omega
  have hNscale : ((2 ^ m : ℕ) : ℝ) * D.thickness ≤ 1 :=
    NativeCompactAncestorRegularity.dyadic_parent_scale hdy ⟨m, by omega⟩
  have hNM : ((2 ^ m : ℕ) : ℝ) * D.thickness * ((2 ^ b : ℕ) : ℝ) ≤ 1 := by
    calc
      _ = ((2 ^ (m + b) : ℕ) : ℝ) * D.thickness := by
        push_cast
        rw [pow_add]
        ring
      _ ≤ 1 := NativeCompactAncestorRegularity.dyadic_parent_scale hdy ⟨m + b, by omega⟩
  have hRelScale : ((2 ^ m : ℕ) : ℝ) * D.thickness * ((2 ^ b : ℕ) : ℝ) ≤ 64 :=
    hNM.trans (by norm_num)
  have hbounds := actual_output_image_bounds h original horiginal ha R Eref A m b hm
    hNscale hRelScale p hQ hS hA hparent s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch hsep
  have hread := NativeMatchedShadowReadback.mixed_full_multiplicity h R Eref A a level m b p
    hQ hparent hS hdy hmlevel hb
  rw [hread]
  change (output.card : ℝ) / (output.image Prod.fst).card ≤
    (165 : ℝ) ^ 4 * ((shadow.card : ℝ) / (shadow.image Prod.snd).card)
  by_cases hAn : A.Nonempty
  · have hoNat : 0 < (output.image Prod.fst).card := card_pos.mpr ((hAn.image _).image _)
    have hsNat : 0 < (shadow.image Prod.snd).card := card_pos.mpr ((hAn.image _).image _)
    have ho : (0 : ℝ) < (output.image Prod.fst).card := by exact_mod_cast hoNat
    have hs : (0 : ℝ) < (shadow.image Prod.snd).card := by exact_mod_cast hsNat
    have he : (output.card : ℝ) ≤ (33 : ℝ) ^ 4 * (shadow.card : ℝ) := by
      exact_mod_cast hbounds.2.2.2
    have hp : ((shadow.image Prod.snd).card : ℝ) ≤
        (5 : ℝ) ^ 4 * ((output.image Prod.fst).card : ℝ) := by
      exact_mod_cast hbounds.1
    have hr : (0 : ℝ) ≤ (shadow.card : ℝ) / (shadow.image Prod.snd).card :=
      div_nonneg (Nat.cast_nonneg _) hs.le
    apply (div_le_iff₀ ho).mpr
    calc
      (output.card : ℝ) ≤ (33 : ℝ) ^ 4 * (shadow.card : ℝ) := he
      _ = ((33 : ℝ) ^ 4 * ((shadow.card : ℝ) / (shadow.image Prod.snd).card)) *
          ((shadow.image Prod.snd).card : ℝ) := by field_simp [hs.ne']
      _ ≤ ((33 : ℝ) ^ 4 * ((shadow.card : ℝ) / (shadow.image Prod.snd).card)) *
          ((5 : ℝ) ^ 4 * ((output.image Prod.fst).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (by positivity) hr)
      _ = _ := by ring
  · have hAe : A = ∅ := not_nonempty_iff_eq_empty.mp hAn
    simp only [output, shadow, hAe, image_empty, card_empty, Nat.cast_zero, zero_div, mul_zero, le_refl]

end NativeMatchedShadowMultiplicity
