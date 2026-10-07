import Theorems.Thm_StickyKakeya4_native_reference_horizontal_menu
import Theorems.Thm_StickyKakeya4_native_slice_menu_ball_join

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeReferenceSliceAllRadii
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeSliceCountComparison NativeColumnPopulationBounds
open NativeReferenceColumnExponents NativeReferenceSliceClassBounds NativeAnisotropicSliceLabels
open NativeSquaredGrainQueries NativeReferenceHorizontalMenu NativeSliceMenuBallJoin SelfUniform
open NativeSliceClassBalls NativeSliceRadiusInterpolation NativeParentSliceHeightGeometry

/-- The actual finest horizontal cell width in the fixed parent chart. -/
def horizontalMesh (m : ℕ) : ℝ := (64/((2^m:ℕ):ℝ))/8

lemma horizontalMesh_pos (m : ℕ) : 0 < horizontalMesh m := by unfold horizontalMesh; positivity

lemma horizontalMesh_readback (m : ℕ) (hm6 : 6 ≤ m) :
    horizontalMesh m=((2^m:ℕ):ℝ)*(64/((2^(phaseDepth m):ℕ):ℝ))/512 := by
  rw [squared_scale_identity m hm6]
  unfold horizontalMesh
  field_simp
  ring

lemma horizontalMesh_outer (m : ℕ) (hm6 : 6 ≤ m) :
    horizontalMesh m*radius (phaseDepth m) m=1/8 := by
  have hmb : m ≤ phaseDepth m := by unfold phaseDepth; omega
  have hh := NativeAnisotropicColumnCapacity.dyadic_height_eq m (phaseDepth m) hmb
  rw [squared_scale_identity m hm6] at hh
  have hR : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  have hcancel : (1:ℝ)=((2^(phaseDepth m-m):ℕ):ℝ)*(64/((2^m:ℕ):ℝ)) :=
    (mul_left_cancel₀ hR.ne') (calc
      (64/((2^m:ℕ):ℝ))*1=64/((2^m:ℕ):ℝ) := mul_one _
      _ = ((2^(phaseDepth m-m):ℕ):ℝ)*(64/((2^m:ℕ):ℝ))^2 := hh
      _ = (64/((2^m:ℕ):ℝ))*(((2^(phaseDepth m-m):ℕ):ℝ)*(64/((2^m:ℕ):ℝ))) := by ring)
  unfold horizontalMesh radius
  calc
    _ = (((2^(phaseDepth m-m):ℕ):ℝ)*(64/((2^m:ℕ):ℝ)))/8 := by ring
    _ = _ := by rw [←hcancel]

/-- All-radius AD counting for each actual reference height slice. The
population exponent, prepared class counts, endpoint cardinal bound, and
mesh normalization are derived here from the unchanged original source.
Only the actual source profile and installed finite relations are consumed. -/
theorem caller_reference_all_radius_bounds {n J : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m G : ℕ) (hm6 : 6 ≤ m) (hbL : phaseDepth m ≤ level) (hJ : 0 < J)
    (depth : Fin (J+1) → ℕ) (hfirst : depth 0=m) (hlast : depth (Fin.last J)=phaseDepth m)
    (hdepth : ∀j,depth j ≤ phaseDepth m) (hmono : Monotone depth)
    (hgap : ∀i : Fin J,depth i.succ-depth i.castSucc ≤ G)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty)
    (population : ℝ) (hpopulation : 0 < population)
    (hret : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (profileLower profileUpper : ℝ) (hL : 0 < profileLower) (hU : 0 < profileUpper)
    (Hprofile : ∀j,HasColumnPowerProfile D a m (depth j) E p profileLower profileUpper)
    (Q : ℕ)
    (Hcaller : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depth j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depth j) E y)
    (u : Index) (hu : u∈points D a m (phaseDepth m) E p)
    (r : ℝ) (hr : horizontalMesh m ≤ r) (hr1 : r ≤ 1) :
    let L := lowerCountCoefficient D.thickness zeta population profileUpper
    let U := upperCountCoefficient D.thickness zeta profileLower
    let B : ℝ := max 8 ((2^G:ℕ):ℝ)
    let P := realizedSlice (points D a m (phaseDepth m) E p) (horizontalMesh m) (u (3:Fin 4))
    (L/((Q:ℝ)^4*U))*(r/horizontalMesh m)^(3-extremalExponent) ≤
        B^(3-extremalExponent)*ballCount P (realized (horizontalMesh m) u) r ∧
      ballCount P (realized (horizontalMesh m) u) r ≤
        (729*((Q:ℝ)^4*U/L))*B^(3-extremalExponent)*(r/horizontalMesh m)^(3-extremalExponent) := by
  have hlo (j : Fin (J+1)) : m ≤ depth j := by
    simpa only [hfirst] using hmono (Fin.zero_le j)
  have Hbase : HasColumnPowerProfile D a m (phaseDepth m) E p profileLower profileUpper := by
    simpa only [hlast] using Hprofile (Fin.last J)
  have Hcounts := caller_reference_menu_counts h original R level Hbackbone m hm6 hbL
    depth hlo hdepth E hE p hp population hpopulation hret profileLower profileUpper hL hU
    Hbase Hprofile Q Hcaller
  have hQ := NativePaidParentScaleBudget.uniform_radix_pos _ hp _ Q Hcounts.1
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hd : 0 < D.thickness := by rw [Hbackbone.2.1]; positivity
  obtain ⟨hcoefL,hcoefU⟩ := count_coefficients_pos (zeta:=zeta) hd hpopulation hL hU
  have hmb : m ≤ phaseDepth m := by unfold phaseDepth; omega
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale Hbackbone.2.1 (hmb.trans hbL)]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have Hcap (z : ℤ) : (((points D a m (phaseDepth m) E p).image
      (horizontalCoarsen (phaseDepth m) m)).filter (fun q => q (3:Fin 4)=z)).card ≤ 27 := by
    rw [points_coarsen D a m (phaseDepth m) m hmb E p]
    exact endpoint_height_card_le h original Hbackbone.1 Hbackbone.2.2.1 (2^m)
      (by positivity) hscale E (hE.trans (filter_subset _ _)) p _ z
  exact menu_classes_all_radius (points D a m (phaseDepth m) E p) J (phaseDepth m) m G hJ
    depth hfirst hlast hdepth hmono hgap (horizontalMesh m)
    (lowerCountCoefficient D.thickness zeta population profileUpper/
      ((Q:ℝ)^4*upperCountCoefficient D.thickness zeta profileLower))
    (((Q:ℝ)^4*upperCountCoefficient D.thickness zeta profileLower)/
      lowerCountCoefficient D.thickness zeta population profileUpper)
    (3-extremalExponent) (horizontalMesh_pos m) (by positivity) (by positivity)
    (sub_nonneg.mpr extremalExponent_le_three) (horizontalMesh_outer m hm6)
    (fun j v hv => (Hcounts.2 j).2 v hv |>.1)
    (fun j v hv => (Hcounts.2 j).2 v hv |>.2) Hcap u hu r hr hr1

end NativeReferenceSliceAllRadii
