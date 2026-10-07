import Theorems.Thm_StickyKakeya4_native_reference_slice_class_bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeReferenceHorizontalMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeSliceCountComparison NativeColumnPopulationBounds
open NativeReferenceColumnExponents NativeReferenceSliceClassBounds NativeAnisotropicSliceLabels
open NativeSquaredGrainQueries SelfUniform

lemma menu_width_window (m f : ℕ) (hm6 : 6 ≤ m) (hf : f ≤ phaseDepth m) :
    (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ) := by
  rw [←squared_scale_identity m hm6]
  have hpow : ((2^f:ℕ):ℝ) ≤ ((2^(phaseDepth m):ℕ):ℝ) := by
    gcongr
    norm_num
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow

/-- Decode the fixed finite caller menu on the actual reference E2. The
global cross-ratio lower is ready for retained-incidence refinement, while
the local bounds are ready for the grid-to-ball conversion. The original
population and original-source multiplicity profiles produce the exponent. -/
theorem caller_reference_menu_counts {n K : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m : ℕ) (hm6 : 6 ≤ m) (hbL : phaseDepth m ≤ level)
    (depths : Fin K → ℕ) (hlo : ∀j,m ≤ depths j) (hhi : ∀j,depths j ≤ phaseDepth m)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty)
    (population : ℝ) (hpopulation : 0 < population)
    (hret : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (profileLower profileUpper : ℝ) (hL : 0 < profileLower) (hU : 0 < profileUpper)
    (Hbase : HasColumnPowerProfile D a m (phaseDepth m) E p profileLower profileUpper)
    (Hmenu : ∀j,HasColumnPowerProfile D a m (depths j) E p profileLower profileUpper)
    (Q : ℕ)
    (Hcaller : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depths j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depths j) E y) :
    let L := lowerCountCoefficient D.thickness zeta population profileUpper
    let U := upperCountCoefficient D.thickness zeta profileLower
    HasUniformFibers (parentEdges D a (2^m) E p) Q (fun z => slicePoint D a m p z.2) ∧
    ∀j,
      let T : ℝ := ((2^(phaseDepth m-depths j):ℕ):ℝ)
      ((L/U)*T^(3-extremalExponent)*(points D a m (depths j) E p).card ≤
          (points D a m (phaseDepth m) E p).card ∧
        ((points D a m (phaseDepth m) E p).card:ℝ) ≤
          (U/L)*T^(3-extremalExponent)*(points D a m (depths j) E p).card) ∧
      ∀x∈points D a m (phaseDepth m) E p,
        (L/((Q:ℝ)^4*U))*T^(3-extremalExponent) ≤
          ((points D a m (phaseDepth m) E p).filter
            (fun z => sliceClass m (depths j) z=sliceClass m (depths j) x)).card ∧
        (((points D a m (phaseDepth m) E p).filter
            (fun z => sliceClass m (depths j) z=sliceClass m (depths j) x)).card:ℝ) ≤
          (((Q:ℝ)^4*U)/L)*T^(3-extremalExponent) := by
  have HU := caller_column_uniformities D a m depths hhi E Q Hcaller p
  refine ⟨HU.1,?_⟩
  intro j
  exact reference_class_power_bounds h original R level Hbackbone m (phaseDepth m) (depths j)
    hm6 (hlo j) (hhi j) hbL (menu_width_window m (phaseDepth m) hm6 le_rfl)
    (menu_width_window m (depths j) hm6 (hhi j)) E hE p hp population hpopulation hret
    profileLower profileUpper hL hU Hbase (Hmenu j) Q HU.1 (HU.2 j)

end NativeReferenceHorizontalMenu
