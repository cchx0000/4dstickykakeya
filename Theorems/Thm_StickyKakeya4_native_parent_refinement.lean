import Theorems.Thm_StickyKakeya4_native_original_parent_assembly

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace NativeParentRefinement

open NativeOriginalParentAssembly NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeParentSpines
open NativeAngularChartSelection ActualTubeFootprintProfiles DisjointProfileEpochs
open NativeSeparatedFractionalPatches ParentAllRealTubeControl
open ShearedGridADReference ShearedGridTubeReference ShearedGridSpineColumns
open NativeContactFractionalComposition NativeFractionalReferenceComposition
open SmallFiberAlignment FractionalFiberAlignment SelfUniform
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The output is an actual retained set of original physical points and its
actual quantizer image. Every field is constructed by residue and fractional
selection, and source cardinality is counted before quantization. -/
structure RefinedParent {d : ℕ} (source : Finset Plane) (μ angle : ℝ)
    (R : Fin d → ℕ) (N Q L : ℕ) (δ K t s H ell : ℝ) where
  residue : Finset Plane
  residue_subset : residue ⊆ source
  residue_nonempty : residue.Nonempty
  residue_retained : source.card ≤ 64 ^ 2 * residue.card
  cap : ℕ
  cap_pos : 0 < cap
  cap_upper : (cap : ℝ) ≤ 2 * K * ((64 * μ) / δ) ^ t
  density_pos : 0 < density residue cap N t
  points : Finset Plane
  subset : points ⊆ residue
  nonempty : points.Nonempty
  retained : source.card ≤ (64 ^ 2 * retentionCost (d + (d + 1)) L) * points.card
  counts : RefinedCounts (points.image (vertex μ angle)) R N Q L t s (density residue cap N t)
    (adConstant K t) (contactColumnConstant 2 K H t ell) (tubeConstant H)
  separated : ∀ p ∈ points.image (quantized μ angle), ∀ q ∈ points.image (quantized μ angle),
    p ≠ q → 64 * μ ≤ dist p q

lemma quantizer_cap_total {δ μ b K t : ℝ} {U N : ℕ}
    (hδ : 0 < δ) (hμ : 0 < μ) (hNscale : μ * (N : ℝ) = b)
    (hcap : (U : ℝ) ≤ 2 * K * ((64 * μ) / δ) ^ t) :
    (U : ℝ) * (N : ℝ) ^ t ≤ 2 * K * (64 : ℝ) ^ t * (b / δ) ^ t := by
  have hmul := mul_le_mul_of_nonneg_right hcap (Real.rpow_nonneg (Nat.cast_nonneg N) t)
  have hb : 0 ≤ b := by rw [← hNscale]; positivity
  have hpow : ((64 * μ) / δ) ^ t * (N : ℝ) ^ t = (64 : ℝ) ^ t * (b / δ) ^ t := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ (64 * μ) / δ) (Nat.cast_nonneg N),
      ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64) (div_nonneg hb hδ.le)]
    congr 1
    rw [← hNscale]
    ring
  calc
    _ ≤ 2 * K * (((64 * μ) / δ) ^ t * (N : ℝ) ^ t) := by simpa only [mul_assoc] using hmul
    _ = _ := by rw [hpow]; ring

/-- A parent's actual original population, together with the constructed
integer vertex cap, supplies the density used by every later estimate. -/
lemma density_lower_from_parent_mass {d : ℕ} {source : Finset Plane}
    {μ angle : ℝ} {R : Fin d → ℕ} {N Q L : ℕ} {δ K t s H ell b C : ℝ}
    (F : RefinedParent source μ angle R N Q L δ K t s H ell)
    (hδ : 0 < δ) (hμ : 0 < μ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hN : 0 < N) (hNscale : μ * (N : ℝ) = b)
    (hmass : (b / δ) ^ t ≤ C * (source.card : ℝ)) :
    1 ≤ (8192 * K * (64 : ℝ) ^ t * C) * density F.residue F.cap N t := by
  have hden : 0 < (F.cap : ℝ) * (N : ℝ) ^ t := by
    have hu : (0 : ℝ) < F.cap := by exact_mod_cast F.cap_pos
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hcap := quantizer_cap_total hδ hμ hNscale F.cap_upper
  have hret : (source.card : ℝ) ≤ (64 : ℝ) ^ 2 * (F.residue.card : ℝ) := by
    exact_mod_cast F.residue_retained
  have hcost : 0 ≤ 2 * K * (64 : ℝ) ^ t := by positivity
  have hbound : (F.cap : ℝ) * (N : ℝ) ^ t ≤
      (8192 * K * (64 : ℝ) ^ t * C) * (F.residue.card : ℝ) := by
    calc
      _ ≤ 2 * K * (64 : ℝ) ^ t * (b / δ) ^ t := hcap
      _ ≤ (2 * K * (64 : ℝ) ^ t) * (C * (source.card : ℝ)) := mul_le_mul_of_nonneg_left hmass hcost
      _ ≤ (2 * K * (64 : ℝ) ^ t) * (C * ((64 : ℝ) ^ 2 * (F.residue.card : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hret hC) hcost
      _ = _ := by ring
  unfold density
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hden).mpr (by simpa only [one_mul] using hbound)

/-- One original parent is refined using actual angular contact witnesses and
all three literal dyadic queries of the SAME stopped profile. No reference
capacity, maximizing tube, contact spine or density is supplied as a certificate. -/
theorem refine_parent {A : Finset Plane} {δ ε K t : ℝ} {Nold : ℕ} {E₀ : Finset A}
    (D : StoppedProfile (position A) δ ε K t Nold E₀)
    (Fs : List (Finset A)) (B Ω : Finset A) (hΩ : Ω ⊆ B) (hB : B ⊆ support Fs)
    (hFs : ∀ F ∈ Fs, F ⊆ E₀)
    (T : Finset A → TubeData 1) (j : Fin 2)
    (hchart : ∀ F ∈ Fs, |(T F).direction j| = 1)
    (i k : ℕ) (hlo : D.pair.1 ≤ i) (hik : i ≤ k) (hhi : k ≤ D.pair.2)
    (angle : GridLabel 1 → ℝ) (hangle : ∀ c, |angle c| ≤ 1)
    (γ ell : ℝ) (hγ : 0 ≤ γ) (hell : 0 < ell)
    (hangleScale : γ * scale δ k ≤ scale δ i)
    (hwitness : ∀ q ∈ Ω, ∃ z ∈ Ω,
      grid (position A) (scale δ i) z = grid (position A) (scale δ i) q ∧
      |chartSlope j (T (owner Fs z)) - angle (grid (position A) (scale δ k) q)| ≤ γ ∧
      InTube (T (owner Fs z)) (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A z) ∧
      (∀ r ∈ parentSpine A Fs B (scale δ k) z, r ∈ B ∧
        grid (position A) (scale δ k) r = grid (position A) (scale δ k) q ∧
        InTube (T (owner Fs z)) (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A r)) ∧
      ell * (scale δ k / scale δ D.pair.1) ^ D.exponent ≤
        (((parentSpine A Fs B (scale δ k) z).image (grid (position A) (scale δ D.pair.1))).card : ℝ))
    (Q L Hwork : ℕ) (hHwork : 0 < Hwork) (hQ : 4 ≤ Q) (hheight : A.card ≤ Q ^ L)
    (hδ : 0 < δ) (hε : 0 ≤ ε) (htop : scale δ Nold ≤ 1 / 64)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t)
    (c : GridLabel 1) (hc : (parent A Ω (scale δ k) c).Nonempty) :
    Nonempty (RefinedParent ((parent A Ω (scale δ k) c).image (chartPosition A j))
      (scale δ i / 64) (angle c) (ActualScalarADProfiles.workingRadii (k - i + 6) Hwork)
      (2 ^ (k - i + 6)) Q L δ K t D.exponent D.loss ell) := by
  classical
  let p := chartPosition A j
  let μ := scale δ i / 64
  let b := scale δ k
  let E := (parent A B b c).image p
  let O := (parent A Ω b c).image p
  let D' := chartStoppedProfile (position A) D j
  have hmesh : 64 * μ = scale δ i := by dsimp [μ]; ring
  have hμ : 0 < μ := (native_grid_extent δ hδ i k hik).1
  have hNscale : μ * ((2 ^ (k - i + 6) : ℕ) : ℝ) = b := (native_grid_extent δ hδ i k hik).2
  have hB₀ : B ⊆ E₀ := by
    intro q hq
    obtain ⟨F, hF, hqF⟩ := (mem_support Fs q).mp (hB hq)
    exact hFs F hF hqF
  have hOE : O ⊆ E := by
    apply Finset.image_subset_image
    exact Finset.filter_subset_filter _ hΩ
  have hEA : E ⊆ A.image (chartPoint j) := by
    intro q hq
    obtain ⟨r, _hr, rfl⟩ := Finset.mem_image.mp hq
    exact chartPosition_mem A j r
  have hOcard : O.card ≤ Q ^ L := by
    rw [show O = (parent A Ω b c).image p from rfl, Finset.card_image_of_injective _ (chartPosition_injective A j)]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans (by simpa using hheight)
  obtain ⟨S, U, hS, hrich, hunit, hslope, hcontact, hTube⟩ :=
    physical_contacts A Fs B Ω hΩ hB T j hchart (scale δ i) b (scale δ D.pair.1)
      (scale δ D.pair.2) γ ell D.exponent angle hwitness
      (fun _ _ he => grid_scale_nested (position A) hik he) c
  have hqueries (l : ℕ) := D'.native_quantizer_queries hδ μ b i k l hmesh rfl hlo hik hhi
  have hR (l : Fin (Hwork + 1)) :
      0 < ActualScalarADProfiles.workingRadii (k - i + 6) Hwork l ∧
      ActualScalarADProfiles.workingRadii (k - i + 6) Hwork l ≤ 2 ^ (k - i + 6) := by
    refine ⟨by unfold ActualScalarADProfiles.workingRadii; positivity, ?_⟩
    apply Nat.pow_le_pow_right (by omega : 0 < 2)
    exact DyadicAlignmentParameters.level_le_endpoint (k - i + 6) Hwork l hHwork (by omega)
  have hb : b ≤ 1 / 64 := (scale_mono hδ.le (hhi.trans D.valid.2)).trans htop
  obtain ⟨O₀, hO₀, hne₀, hret₀, V, hV, hVupper, hdens, _hcap, O', hO', hne', hret', hcounts,
    hseparated, _hnear, _hback⟩ :=
    exists_native_separated_fractional_refinement (A.image (chartPoint j)) (E₀.image p) E O
      δ μ (angle c) ((c j : ℝ) * b) b (scale δ D.pair.1) (scale δ D.pair.2) γ K D.loss t D.exponent ell
      S U 2 (2 ^ (k - i + 6)) (ActualScalarADProfiles.workingRadii (k - i + 6) Hwork)
      hQ (hc.image p) hOcard hδ hμ (by rw [hmesh]; exact (scale_zero δ).symm.trans_le (scale_mono hδ.le (Nat.zero_le i)))
      (by rw [hmesh]; exact scale_mono hδ.le hik) hb (scale_pos hδ _)
      (by rw [hmesh]; exact scale_mono hδ.le hlo) (hangle c) hγ (by rwa [hmesh])
      hOE (parent_image_subset A B E₀ j b c hB₀) hEA (parent_chart_span A B j (scale_pos hδ k) c)
      (parent_chart_diameter A B j (scale_pos hδ k) c) hS hrich hunit hslope
      (by simpa only [hmesh, Nat.cast_ofNat] using hcontact) hTube
      (D.loss_ge_one hδ hε hK ht) hell (hqueries 0).1
      (fun l => (hqueries (DyadicAlignmentParameters.level (k - i + 6) Hwork l)).2.1)
      (fun l => (hqueries (DyadicAlignmentParameters.level (k - i + 6) Hwork l)).2.2)
      hK ht ht2 D.exponent_nonneg (D.exponent_le.trans (min_le_left _ _))
      (by intro x hx y hy; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
          rw [chartPoint_dist]; exact hdiam u hu v hv)
      (chart_AD j A δ K t hAD) hNscale hR
  exact ⟨⟨O₀, hO₀, hne₀, hret₀, V, hV, hVupper, hdens, O', hO', hne', hret', hcounts, hseparated⟩⟩

end
end NativeParentRefinement
