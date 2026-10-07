import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_actual_caps
import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_ad
import Theorems.Thm_StickyKakeya4_native_reference_slice_all_radii
import Theorems.Thm_StickyKakeya4_native_fixed_horizontal_menu
import Theorems.Thm_StickyKakeya4_native_slice_ad_constant

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000

noncomputable section
namespace NativeTwoMapRetainedSliceActualAD
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeTwoMapRetainedSliceActualCaps NativeAnisotropicSliceLabels NativeSliceCountComparison
open NativeReferenceColumnExponents NativeReferenceSliceClassBounds NativeReferenceHorizontalMenu
open NativeReferenceSliceAllRadii NativeSliceClassBalls NativeSliceRadiusInterpolation
open NativeParentSliceHeightGeometry NativeSquaredGrainQueries SelfUniform
open scoped Matrix.Norms.Elementwise

/-- Actual XY all-radius bounds on the prescribed third core T. The
reference point map is the old anisotropic map; all forward/inverse XY
capacities are DERIVED here from one total bounded height field. -/
theorem actual_all_radius_bounds {n J : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m ell : ℕ) (hm6 : 6 ≤ m) (hbL : phaseDepth m ≤ level) (hJ : 0 < J)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (p : Parent)
    (population : ℝ) (hpopulation : 0 < population)
    (hpop : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (profileLower profileUpper : ℝ) (hL : 0 < profileLower) (hU : 0 < profileUpper)
    (Hprofile : ∀j,HasColumnPowerProfile D a m (NativeFixedHorizontalMenu.depths J m j) E p
      profileLower profileUpper)
    (Qref : ℕ)
    (Hcaller : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1)
        (sliceRelations D a m (NativeFixedHorizontalMenu.depths J m) j) E x ≤
      Qref^2*degree (fun _ : Fin n × Index => 1)
        (sliceRelations D a m (NativeFixedHorizontalMenu.depths J m) j) E y)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (T : Finset (Fin n × Index)) (hT : T⊆parentEdges D a (2^m) E p) (hTn : T.Nonempty)
    (Qnew : ℕ) (HT : HasUniformFibers T Qnew
      (fun z => encodedPoint D a m ell p P hP hell hell4 hd F z.2))
    (HC : ∀j,HasUniformFibers T Qnew (fun z => horizontalCoarsen (phaseDepth m)
      (NativeFixedHorizontalMenu.depths J m j) (encodedPoint D a m ell p P hP hell hell4 hd F z.2)))
    (lambda loss : ℝ) (hlambda : 0 < lambda) (hloss : 0 < loss)
    (hret : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ loss*T.card)
    (u : Index) (hu : u∈T.image (fun z => encodedPoint D a m ell p P hP hell hell4 hd F z.2))
    (r : ℝ) (hr : NativeReferenceXYGridPoints.mu m ≤ r) (hr1 : r ≤ 1) :
    let L := lowerCountCoefficient D.thickness zeta population profileUpper
    let U := upperCountCoefficient D.thickness zeta profileLower
    let Ci : ℝ := ((201^3:ℕ):ℝ)
    let Cf : ℝ := ((1201^3:ℕ):ℝ)
    let B : ℝ := max 64 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
    let points := T.image (fun z => encodedPoint D a m ell p P hP hell hell4 hd F z.2)
    let W := realizedSlice points (NativeReferenceXYGridPoints.mu m) (u (3:Fin 4))
    (lambda*(L/U)/(loss*(Qref:ℝ)^2*Ci*Cf*(Qnew:ℝ)^4))*(r/NativeReferenceXYGridPoints.mu m)^(3-extremalExponent) ≤
        B^(3-extremalExponent)*ballCount W (realized (NativeReferenceXYGridPoints.mu m) u) r ∧
      ballCount W (realized (NativeReferenceXYGridPoints.mu m) u) r ≤
        729*((27*Cf)*(Cf*Ci*((Qref:ℝ)^4*U/L)))*B^(3-extremalExponent)*
          (r/NativeReferenceXYGridPoints.mu m)^(3-extremalExponent) := by
  let I := parentEdges D a (2^m) E p
  let ref := fun z : Fin n × Index => pref D a m p z.2
  let xy := fun z : Fin n × Index => encodedPoint D a m ell p P hP hell hell4 hd F z.2
  let depth := NativeFixedHorizontalMenu.depths J m
  have hdepth (j : Fin (J+1)) := NativeFixedHorizontalMenu.depths_bounds J m hm6 j
  have hp := hTn.mono hT
  have Hbase : HasColumnPowerProfile D a m (phaseDepth m) E p profileLower profileUpper := by
    simpa only [NativeFixedHorizontalMenu.depths_last J m hJ hm6] using Hprofile (Fin.last J)
  have Hcounts := caller_reference_menu_counts h original R level Hbackbone m hm6 hbL
    depth (fun j => (hdepth j).1) (fun j => (hdepth j).2) E hE p hp population hpopulation hpop
    profileLower profileUpper hL hU Hbase Hprofile Qref Hcaller
  have hWitness : T.Nonempty := hTn
  obtain ⟨z,hz⟩ := hWitness
  have hzp := (mem_filter.mp (hT hz)).2
  have Hcaps := encoded_capacities h m ell hm6 p z.1 hzp P hP hell hell4 hd F hF I
  let L := lowerCountCoefficient D.thickness zeta population profileUpper
  let U := upperCountCoefficient D.thickness zeta profileLower
  obtain ⟨hLp,hUp⟩ := count_coefficients_pos (zeta:=zeta) h.1.2.1 hpopulation hL hU
  have Hratio (j : Fin (J+1)) : ((L/U)*(radius (phaseDepth m) (depth j))^(3-extremalExponent))*
      ((I.image ref).image (horizontalCoarsen (phaseDepth m) (depth j))).card ≤ (I.image ref).card := by
    change ((L/U)*(radius (phaseDepth m) (depth j))^(3-extremalExponent))*
      ((points D a m (phaseDepth m) E p).image (horizontalCoarsen (phaseDepth m) (depth j))).card ≤
      (points D a m (phaseDepth m) E p).card
    rw [points_coarsen D a m (phaseDepth m) (depth j) (hdepth j).2 E p]
    exact (Hcounts.2 j).1.1
  have Hupper (j : Fin (J+1)) (v : Index) (hv : v∈I.image ref) :
      ((preparedClass (I.image ref) (phaseDepth m) (depth j) v).card:ℝ) ≤
        ((Qref:ℝ)^4*U/L)*(radius (phaseDepth m) (depth j))^(3-extremalExponent) :=
    ((Hcounts.2 j).2 v hv).2
  have hmb : m ≤ phaseDepth m := by unfold phaseDepth; omega
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale Hbackbone.2.1 (hmb.trans hbL)]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have Hcap (t : ℤ) : (((I.image ref).image (horizontalCoarsen (phaseDepth m) m)).filter
      (fun q => q (3:Fin 4)=t)).card ≤ 27 := by
    change (((points D a m (phaseDepth m) E p).image (horizontalCoarsen (phaseDepth m) m)).filter
      (fun q => q (3:Fin 4)=t)).card ≤ 27
    rw [points_coarsen D a m (phaseDepth m) m hmb E p]
    exact endpoint_height_card_le h original Hbackbone.1 Hbackbone.2.2.1 (2^m)
      (by positivity) hscale E (hE.trans (filter_subset _ _)) p _ t
  have hmesh : NativeReferenceXYGridPoints.mu m=horizontalMesh m/8 := by unfold mu rho horizontalMesh; ring
  have houter : NativeReferenceXYGridPoints.mu m*radius (phaseDepth m) m=1/64 := by
    rw [hmesh,div_mul_eq_mul_div,horizontalMesh_outer m hm6]
    norm_num
  have hh := NativeTwoMapRetainedSliceAD.all_radius_bounds I T hT hTn ref xy Qref Qnew (201^3) (1201^3)
    (by positivity) (by positivity) Hcounts.1 HT J (phaseDepth m) m ((phaseDepth m-m)/J+1) hJ depth
    (NativeFixedHorizontalMenu.depths_zero J m) (NativeFixedHorizontalMenu.depths_last J m hJ hm6)
    (fun j => (hdepth j).2) (NativeFixedHorizontalMenu.depths_monotone J m)
    (NativeFixedHorizontalMenu.depths_gap J m hJ) HC Hcaps.1 Hcaps.2.1
    (fun j => (Hcaps.2.2 (phaseDepth m) (depth j)).1)
    (fun j => (Hcaps.2.2 (phaseDepth m) (depth j)).2)
    (fun x _hx => encodedPoint_height D a m ell p P hP hell hell4 hd F x.2) Hcap
    (NativeReferenceXYGridPoints.mu m) (L/U) ((Qref:ℝ)^4*U/L) (3-extremalExponent) lambda loss
    (mu_pos m) (by positivity) (by positivity) (sub_nonneg.mpr extremalExponent_le_three)
    hlambda.le hloss houter hret Hratio Hupper u hu r hr hr1
  exact hh

/-- The actual two-map counts give the standard AD predicate on every XY slice. -/
theorem actual_ADBounds {n J : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m ell : ℕ) (hm6 : 6 ≤ m) (hbL : phaseDepth m ≤ level) (hJ : 0 < J)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (p : Parent)
    (population : ℝ) (hpopulation : 0 < population)
    (hpop : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (profileLower profileUpper : ℝ) (hL : 0 < profileLower) (hU : 0 < profileUpper)
    (Hprofile : ∀j,HasColumnPowerProfile D a m (NativeFixedHorizontalMenu.depths J m j) E p
      profileLower profileUpper)
    (Qref : ℕ)
    (Hcaller : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1)
        (sliceRelations D a m (NativeFixedHorizontalMenu.depths J m) j) E x ≤
      Qref^2*degree (fun _ : Fin n × Index => 1)
        (sliceRelations D a m (NativeFixedHorizontalMenu.depths J m) j) E y)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (T : Finset (Fin n × Index)) (hT : T⊆parentEdges D a (2^m) E p) (hTn : T.Nonempty)
    (Qnew : ℕ) (HT : HasUniformFibers T Qnew
      (fun z => encodedPoint D a m ell p P hP hell hell4 hd F z.2))
    (HC : ∀j,HasUniformFibers T Qnew (fun z => horizontalCoarsen (phaseDepth m)
      (NativeFixedHorizontalMenu.depths J m j) (encodedPoint D a m ell p P hP hell hell4 hd F z.2)))
    (lambda loss : ℝ) (hlambda : 0 < lambda) (hloss : 0 < loss)
    (hret : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ loss*T.card)
    :
    let L := lowerCountCoefficient D.thickness zeta population profileUpper
    let U := upperCountCoefficient D.thickness zeta profileLower
    let Ci : ℝ := ((201^3:ℕ):ℝ)
    let Cf : ℝ := ((1201^3:ℕ):ℝ)
    let B : ℝ := max 64 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
    ∀height : ℤ,
      FiniteVoronoiRealADCoarsening.ADBounds
        (realizedSlice (T.image (fun z => encodedPoint D a m ell p P hP hell hell4 hd F z.2))
          (NativeReferenceXYGridPoints.mu m) height)
        (NativeReferenceXYGridPoints.mu m)
        (NativeSliceADConstant.constant
          (lambda*(L/U)/(loss*(Qref:ℝ)^2*Ci*Cf*(Qnew:ℝ)^4))
          ((27*Cf)*(Cf*Ci*((Qref:ℝ)^4*U/L))) B (3-extremalExponent))
        (3-extremalExponent) := by
  intro L U Ci Cf B height
  have hp := hTn.mono hT
  have HRef := (caller_column_uniformities D a m (NativeFixedHorizontalMenu.depths J m)
    (fun j => (NativeFixedHorizontalMenu.depths_bounds J m hm6 j).2) E Qref Hcaller p).1
  have hQR : (0:ℝ)<Qref := by
    exact_mod_cast NativePaidParentScaleBudget.uniform_radix_pos _ hp _ Qref HRef
  have hQT : (0:ℝ)<Qnew := by
    exact_mod_cast NativePaidParentScaleBudget.uniform_radix_pos _ hTn _ Qnew HT
  have hCi : 0<Ci := by dsimp [Ci]; positivity
  have hCf : 0<Cf := by dsimp [Cf]; positivity
  obtain ⟨hLp,hUp⟩ := count_coefficients_pos (zeta:=zeta) h.1.2.1 hpopulation hL hU
  apply NativeSliceADConstant.ADBounds_of_asymmetric_counts _ (NativeReferenceXYGridPoints.mu m)
    (lambda*(L/U)/(loss*(Qref:ℝ)^2*Ci*Cf*(Qnew:ℝ)^4))
    ((27*Cf)*(Cf*Ci*((Qref:ℝ)^4*U/L))) B (3-extremalExponent) (mu_pos m) (by positivity)
  intro x hx r hr hr1
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
  obtain ⟨huP,hheight⟩ := mem_filter.mp hu
  have hh := actual_all_radius_bounds h original R level Hbackbone m ell hm6 hbL hJ
    E hE p population hpopulation hpop profileLower profileUpper hL hU Hprofile Qref Hcaller
    P hP hell hell4 hd F hF T hT hTn Qnew HT HC lambda loss hlambda hloss hret u huP r hr hr1
  simpa only [hheight] using hh

end NativeTwoMapRetainedSliceActualAD
