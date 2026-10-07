import Theorems.Thm_StickyKakeya4_native_retained_slice_count_transfer
import Theorems.Thm_StickyKakeya4_native_reference_slice_all_radii
import Theorems.Thm_StickyKakeya4_native_fixed_horizontal_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

noncomputable section
namespace NativeRetainedSliceAllRadii
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeAnisotropicSliceLabels NativeSliceCountComparison
open NativeReferenceColumnExponents NativeReferenceSliceClassBounds NativeReferenceHorizontalMenu
open NativeReferenceSliceAllRadii NativeSliceMenuBallJoin NativeSliceClassBalls NativeSliceRadiusInterpolation
open NativeParentSliceHeightGeometry NativeSquaredGrainQueries NativeRetainedSliceCountTransfer SelfUniform

/-- All-radius counts on the SAME original-incidence third core. Its local
lower is reconstructed from retained incidence mass and reference count
ratios; its upper and endpoint geometry are inherited by actual inclusion.
This theorem makes no selection and hence preserves every other T-field. -/
theorem retained_all_radius_bounds {n J : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m gap : ℕ) (hm6 : 6 ≤ m) (hbL : phaseDepth m ≤ level) (hJ : 0 < J)
    (depth : Fin (J+1) → ℕ) (hfirst : depth 0=m) (hlast : depth (Fin.last J)=phaseDepth m)
    (hdepth : ∀j,depth j ≤ phaseDepth m) (hmono : Monotone depth)
    (hgap : ∀i : Fin J,depth i.succ-depth i.castSucc ≤ gap)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (p : Parent)
    (population : ℝ) (hpopulation : 0 < population)
    (hpop : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (profileLower profileUpper : ℝ) (hL : 0 < profileLower) (hU : 0 < profileUpper)
    (Hprofile : ∀j,HasColumnPowerProfile D a m (depth j) E p profileLower profileUpper)
    (Qref : ℕ)
    (Hcaller : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depth j) E x ≤
        Qref^2*degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depth j) E y)
    (T : Finset (Fin n × Index)) (hT : T⊆parentEdges D a (2^m) E p) (hTn : T.Nonempty)
    (Qnew : ℕ) (HTP : HasUniformFibers T Qnew (fun z => slicePoint D a m p z.2))
    (HTC : ∀j,HasUniformFibers T Qnew
      (fun z => sliceClass m (depth j) (slicePoint D a m p z.2)))
    (lambda loss : ℝ) (hlambda : 0 < lambda) (hloss : 0 < loss)
    (hret : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ loss*T.card)
    (u : Index) (hu : u∈T.image (fun z => slicePoint D a m p z.2))
    (r : ℝ) (hr : horizontalMesh m ≤ r) (hr1 : r ≤ 1) :
    let L := lowerCountCoefficient D.thickness zeta population profileUpper
    let U := upperCountCoefficient D.thickness zeta profileLower
    let B : ℝ := max 8 ((2^gap:ℕ):ℝ)
    let P := realizedSlice (T.image (fun z => slicePoint D a m p z.2)) (horizontalMesh m) (u (3:Fin 4))
    (lambda*(L/U)/(loss*(Qref:ℝ)^2*(Qnew:ℝ)^4))*(r/horizontalMesh m)^(3-extremalExponent) ≤
        B^(3-extremalExponent)*ballCount P (realized (horizontalMesh m) u) r ∧
      ballCount P (realized (horizontalMesh m) u) r ≤
        (729*((Qref:ℝ)^4*U/L))*B^(3-extremalExponent)*(r/horizontalMesh m)^(3-extremalExponent) := by
  have hp := hTn.mono hT
  have hlo (j : Fin (J+1)) : m ≤ depth j := by simpa only [hfirst] using hmono (Fin.zero_le j)
  have Hbase : HasColumnPowerProfile D a m (phaseDepth m) E p profileLower profileUpper := by
    simpa only [hlast] using Hprofile (Fin.last J)
  have Hcounts := caller_reference_menu_counts h original R level Hbackbone m hm6 hbL
    depth hlo hdepth E hE p hp population hpopulation hpop profileLower profileUpper hL hU
    Hbase Hprofile Qref Hcaller
  let point := fun z : Fin n × Index => slicePoint D a m p z.2
  let P := T.image point
  let L := lowerCountCoefficient D.thickness zeta population profileUpper
  let U := upperCountCoefficient D.thickness zeta profileLower
  let C := loss*(Qref:ℝ)^2*(Qnew:ℝ)^4
  have hQR : (0:ℝ)<Qref := by
    exact_mod_cast NativePaidParentScaleBudget.uniform_radix_pos _ hp _ Qref Hcounts.1
  have hQT : (0:ℝ)<Qnew := by
    exact_mod_cast NativePaidParentScaleBudget.uniform_radix_pos _ hTn _ Qnew HTP
  have hC : 0<C := by dsimp [C]; positivity
  obtain ⟨hLp,hUp⟩ := count_coefficients_pos (zeta:=zeta) h.1.2.1 hpopulation hL hU
  have hPsub : P⊆points D a m (phaseDepth m) E p := image_subset_image hT
  have Hlo (j : Fin (J+1)) (v : Index) (hv : v∈P) :
      (lambda*(L/U)/C)*(radius (phaseDepth m) (depth j))^(3-extremalExponent) ≤
        (preparedClass P (phaseDepth m) (depth j) v).card := by
    have hRatio : ((L/U)*(radius (phaseDepth m) (depth j))^(3-extremalExponent))*
        ((((parentEdges D a (2^m) E p).image point).image (sliceClass m (depth j))).card) ≤
        ((parentEdges D a (2^m) E p).image point).card := by
      change ((L/U)*(radius (phaseDepth m) (depth j))^(3-extremalExponent))*
        (((points D a m (phaseDepth m) E p).image (horizontalCoarsen (phaseDepth m) (depth j))).card) ≤
        (points D a m (phaseDepth m) E p).card
      rw [points_coarsen D a m (phaseDepth m) (depth j) (hdepth j) E p]
      exact (Hcounts.2 j).1.1
    have hh := retained_class_count_lower (parentEdges D a (2^m) E p) T hT hp point
      (sliceClass m (depth j)) Qref Qnew Hcounts.1 HTP (HTC j) lambda loss
      ((L/U)*(radius (phaseDepth m) (depth j))^(3-extremalExponent)) hlambda.le hloss.le hret hRatio
      (sliceClass m (depth j) v) (mem_image_of_mem _ hv)
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hC).mpr
    simp only [preparedClass,sliceClass,C,P,mul_assoc,mul_comm] at hh ⊢
    convert hh using 1
    all_goals congr
  have Hhi (j : Fin (J+1)) (v : Index) (hv : v∈P) :
      ((preparedClass P (phaseDepth m) (depth j) v).card:ℝ) ≤
        (((Qref:ℝ)^4*U)/L)*(radius (phaseDepth m) (depth j))^(3-extremalExponent) := by
    have hh := ((Hcounts.2 j).2 v (hPsub hv)).2
    exact (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hPsub))).trans hh
  have hmb : m ≤ phaseDepth m := by unfold phaseDepth; omega
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale Hbackbone.2.1 (hmb.trans hbL)]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have Hcap (z : ℤ) : ((P.image (horizontalCoarsen (phaseDepth m) m)).filter
      (fun q => q (3:Fin 4)=z)).card ≤ 27 := by
    apply (card_le_card (filter_subset_filter _ (image_subset_image hPsub))).trans
    rw [points_coarsen D a m (phaseDepth m) m hmb E p]
    exact endpoint_height_card_le h original Hbackbone.1 Hbackbone.2.2.1 (2^m)
      (by positivity) hscale E (hE.trans (filter_subset _ _)) p _ z
  exact menu_classes_all_radius P J (phaseDepth m) m gap hJ depth hfirst hlast hdepth hmono hgap
    (horizontalMesh m) (lambda*(L/U)/C) (((Qref:ℝ)^4*U)/L) (3-extremalExponent)
    (horizontalMesh_pos m) (by positivity) (by positivity)
    (sub_nonneg.mpr extremalExponent_le_three) (horizontalMesh_outer m hm6)
    Hlo Hhi Hcap u hu r hr hr1

end NativeRetainedSliceAllRadii
