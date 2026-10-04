import Theorems.Thm_StickyKakeya4_original_line_cover_packets
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

open Filter MeasureTheory Set
open scoped ENNReal Topology Pointwise RealInnerProductSpace

namespace StickyKakeya4

/-- Finite estimates on one fixed original marked-line set. K is selected
before epsilon, eta and the mesh; no uniformity over unrelated K is asserted. -/
def HasWangZakharovFiniteEstimateOn (K : Set MarkedLine) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta : ℝ, 0 < eta ∧
    ∃ A : ENNReal, A ≠ 0 ∧ A ≠ ⊤ ∧
    ∃ deltaZero : ℝ, 0 < deltaZero ∧
    ∀ (n : ℕ) (D : FiniteScaleSource n),
      D.thickness ≤ deltaZero →
      IsWangZakharovNativeFiniteInput D eta →
      (∀ i,D.line i∈K) →
      A⁻¹ * (ENNReal.ofReal D.thickness).rpow (-4 + epsilon) ≤
        coveringNumber (sourceUnion D) D.thickness

def HasWangZakharovFiniteVolumeEstimateOn (K : Set MarkedLine) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta : ℝ, 0 < eta ∧
    ∃ A : ENNReal, A ≠ 0 ∧ A ≠ ⊤ ∧
    ∃ deltaZero : ℝ, 0 < deltaZero ∧
    ∀ (n : ℕ) (D : FiniteScaleSource n),
      D.thickness ≤ deltaZero →
      IsWangZakharovNativeFiniteInput D eta →
      (∀ i,D.line i∈K) →
      A⁻¹ * (ENNReal.ofReal D.thickness).rpow epsilon ≤
        volume (sourceUnion D)

theorem wang_zakharov_volume_on_to_covering (K : Set MarkedLine)
    (hWZ : HasWangZakharovFiniteVolumeEstimateOn K) :
    HasWangZakharovFiniteEstimateOn K := by
  intro epsilon hepsilon
  obtain ⟨eta, heta, A, hA0, hATop, deltaZero, hdeltaZero, hvolume⟩ :=
    hWZ epsilon hepsilon
  let Cball : ENNReal :=
    16 * ENNReal.ofReal (Real.pi ^ 2 / 2)
  let Acover : ENNReal := A * Cball
  have hCball0 : Cball ≠ 0 := by
    dsimp [Cball]
    positivity
  have hCballTop : Cball ≠ ⊤ := by
    dsimp [Cball]
    finiteness
  have hAcover0 : Acover ≠ 0 := mul_ne_zero hA0 hCball0
  have hAcoverTop : Acover ≠ ⊤ :=
    ENNReal.mul_ne_top hATop hCballTop
  refine ⟨eta, heta, Acover, hAcover0, hAcoverTop,
    deltaZero, hdeltaZero, ?_⟩
  intro n D hsmall hinput hDK
  have hdelta : 0 < D.thickness := hinput.1.2.1
  let e : ENNReal := ENNReal.ofReal D.thickness
  have he0 : e ≠ 0 := by
    dsimp [e]
    positivity
  have heTop : e ≠ ⊤ := by
    dsimp [e]
    exact ENNReal.ofReal_ne_top
  have hball : volume (Metric.ball (0 : E4) (2 * D.thickness)) =
      Cball * e ^ 4 := by
    rw [volume_ball_E4]
    have htwo : ENNReal.ofReal (2 * D.thickness) = 2 * e := by
      dsimp [e]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [htwo]
    dsimp [Cball]
    ring
  have hcover :=
    volume_div_twoBall_le_coveringNumber (sourceUnion D) hdelta
  rw [hball] at hcover
  have hvolume' : A⁻¹ * e.rpow epsilon ≤ volume (sourceUnion D) := by
    simpa [e] using hvolume n D hsmall hinput hDK
  have hquotient :
      (A⁻¹ * e.rpow epsilon) / (Cball * e ^ 4) ≤
        coveringNumber (sourceUnion D) D.thickness :=
    (ENNReal.div_le_div_right hvolume' (Cball * e ^ 4)).trans hcover
  have hpower :
      e.rpow (-4 + epsilon) = e.rpow epsilon * (e ^ 4)⁻¹ := by
    calc
      e.rpow (-4 + epsilon) = e.rpow (epsilon + (-4)) := by ring_nf
      _ = e.rpow epsilon * e.rpow (-4) :=
        ENNReal.rpow_add epsilon (-4) he0 heTop
      _ = e.rpow epsilon * (e.rpow 4)⁻¹ := by
        congr 1
        exact ENNReal.rpow_neg e 4
      _ = e.rpow epsilon * (e ^ 4)⁻¹ := by
        congr 1
        exact congrArg Inv.inv (ENNReal.rpow_natCast e 4)
  have hcoeff :
      Acover⁻¹ * e.rpow (-4 + epsilon) =
        (A⁻¹ * e.rpow epsilon) / (Cball * e ^ 4) := by
    rw [hpower]
    dsimp [Acover]
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hATop)]
    rw [div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl hCball0) (Or.inl hCballTop)]
    ring
  rw [hcoeff]
  exact hquotient


/-- The actual compact-source cover construction needs only the finite
estimate on that same fixed ambient marked family. This removes an
unneeded universal-in-K premise from the final compact-front route. -/
theorem dimH_eq_four_of_original_compact_volume
    (ambient selector : Set MarkedLine)
    (hcompact : IsCompact ambient) (hsub : selector⊆ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line∈selector,IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector)=3)
    (hboundary : HasCoherentConcentrationBoundary selector hmeasurable hvalid hselector)
    (hVolume : HasWangZakharovFiniteVolumeEstimateOn ambient) :
    dimH (unitFront ambient)=4 := by
  have hdimUpper : dimH (unitFront ambient) ≤ 4 := by
    calc
      dimH (unitFront ambient) ≤ dimH (Set.univ : Set E4) := dimH_mono (Set.subset_univ _)
      _ = 4 := by simp [E4,Real.dimH_univ_eq_finrank]
  apply le_antisymm hdimUpper
  by_contra hn
  have hdim : dimH (unitFront ambient) < 4 := lt_of_not_ge hn
  obtain ⟨chi,hchi,hchiFour,d,hd,hdimD⟩ := exists_hausdorff_exponent_gap_below_four
    (unitFront ambient) hdim
  have hpackets := packing_selector_has_original_line_wz_packets_at_exponent ambient selector
    hcompact hsub hmeasurable hvalid hselector hpacking hboundary chi d hchi hchiFour hd hdimD
  obtain ⟨eta,heta,A,hA0,hATop,delta0,hdelta0,hcover⟩ :=
    wang_zakharov_volume_on_to_covering ambient hVolume (chi/2) (by positivity)
  obtain ⟨n,D,target,C,hdpos,hsmall,hinput,hcomes,htarget,hgap,hupper⟩ :=
    hpackets eta heta A hA0 hATop delta0 hdelta0
  have hfinite := hcover n D hsmall hinput (fun i => hsub (hcomes i))
  have hw : ∀ i,D.weight i=1 := hinput.1.2.2.2.2.2.1
  have hsource : sourceUnion D⊆target := by
    rw [sourceUnion_eq_iUnion_shading_of_weights_one D hw]
    exact htarget
  have hlower := hfinite.trans (coveringNumber_mono hsource D.thickness)
  exact wz_covering_bounds_contradiction_ennreal_coefficients hdpos hgap hlower hupper

end StickyKakeya4
