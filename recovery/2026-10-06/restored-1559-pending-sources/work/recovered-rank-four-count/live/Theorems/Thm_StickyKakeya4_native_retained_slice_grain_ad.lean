import Theorems.Thm_StickyKakeya4_native_retained_slice_all_radii
import Theorems.Thm_StickyKakeya4_native_retained_grain_density_core
import Theorems.Thm_StickyKakeya4_native_slice_ad_constant

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

noncomputable section
namespace NativeRetainedSliceGrainAD
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeAnisotropicSliceLabels NativeSliceCountComparison
open NativeReferenceColumnExponents NativeReferenceSliceClassBounds NativeReferenceHorizontalMenu
open NativeReferenceSliceAllRadii NativeSliceClassBalls NativeSliceRadiusInterpolation
open NativeSquaredGrainQueries NativeRetainedSliceAllRadii NativeSliceADConstant
open NativeRetainedGrainDensityCore NativeRetainedSliceCore FiniteVoronoiRealADCoarsening SelfUniform

/-- Package the derived asymmetric all-radius counts as the existing AD
predicate on each retained fixed-height slice, without selecting any set. -/
theorem retained_slice_ADBounds {n J : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
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
    :
    let L := lowerCountCoefficient D.thickness zeta population profileUpper
    let U := upperCountCoefficient D.thickness zeta profileLower
    let B : ℝ := max 8 ((2^gap:ℕ):ℝ)
    ∀height : ℤ,
      ADBounds (realizedSlice (T.image (fun z => slicePoint D a m p z.2)) (horizontalMesh m) height)
        (horizontalMesh m)
        (constant (lambda*(L/U)/(loss*(Qref:ℝ)^2*(Qnew:ℝ)^4))
          ((Qref:ℝ)^4*U/L) B (3-extremalExponent)) (3-extremalExponent) := by
  intro L U B height
  have hp := hTn.mono hT
  have Href := (caller_column_uniformities D a m depth hdepth E Qref Hcaller p).1
  have hQR : (0:ℝ)<Qref := by
    exact_mod_cast NativePaidParentScaleBudget.uniform_radix_pos _ hp _ Qref Href
  have hQT : (0:ℝ)<Qnew := by
    exact_mod_cast NativePaidParentScaleBudget.uniform_radix_pos _ hTn _ Qnew HTP
  obtain ⟨hLp,hUp⟩ := count_coefficients_pos (zeta:=zeta) h.1.2.1 hpopulation hL hU
  apply ADBounds_of_asymmetric_counts _ (horizontalMesh m)
    (lambda*(L/U)/(loss*(Qref:ℝ)^2*(Qnew:ℝ)^4)) ((Qref:ℝ)^4*U/L) B (3-extremalExponent)
    (horizontalMesh_pos m) (by positivity)
  intro x hx r hr hr1
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
  obtain ⟨huP,hheight⟩ := mem_filter.mp hu
  have hh := retained_all_radius_bounds h original R level Hbackbone m gap hm6 hbL hJ
    depth hfirst hlast hdepth hmono hgap E hE p population hpopulation hpop
    profileLower profileUpper hL hU Hprofile Qref Hcaller T hT hTn Qnew HTP HTC
    lambda loss hlambda hloss hret u huP r hr hr1
  simpa only [hheight] using hh

/-- The fixed menu, the actual reference profiles, the quotient-selected
original incidences and ONE third refinement produce the same T carrying
dense old grains and all-radius AD in every fixed translated-height slice. -/
theorem exists_actual_slice_grain_AD {n d J : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    {Y V : Type*} [DecidableEq Y]
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m : ℕ) (hm6 : 6 ≤ m) (hbL : phaseDepth m ≤ level) (hJ : 0 < J)
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
    (H S : Finset (Fin n × Index)) (hH : H⊆parentEdges D a (2^m) E p) (hSH : S⊆H) (hSn : S.Nonempty)
    (grain : (Fin n × Index) → Y) (quotient : (Fin n × Index) → V)
    (hquotient : ∀x y,x∈S → y∈S → grain x=grain y → quotient x=quotient y)
    (lambda G Cq t : ℝ) (hlambda : 0 < lambda) (hG : 0 < G) (hCq : 0 < Cq)
    (hret : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ G*H.card)
    (hquotientRet : (H.card:ℝ) ≤ Cq*S.card)
    (hgrain : ∀g∈H.image grain,t ≤ ((H.filter (fun z => grain z=g)).card:ℝ))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀j x,Rel j x x) (hsym : ∀j x y,Rel j x y → Rel j y x)
    (L3 : ℕ) (hL3 : 0 < L3) :
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let F3 := refinementCost (d+1) (J+1) L3
    let point := fun z : Fin n × Index => slicePoint D a m p z.2
    let L := lowerCountCoefficient D.thickness zeta population profileUpper
    let U := upperCountCoefficient D.thickness zeta profileLower
    let B : ℝ := max 8 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
    let KAD := constant (lambda*(L/U)/((G*Cq*(F3:ℝ))*(Qref:ℝ)^2*(Q3:ℝ)^4))
      ((Qref:ℝ)^4*U/L) B (3-extremalExponent)
    ∃T⊆S,T.Nonempty ∧ S.card ≤ F3*T.card ∧
      (∀j x y,x∈T → y∈T → degree (fun _ : Fin n × Index => 1) (Rel j) T x ≤
        Q3^2*degree (fun _ : Fin n × Index => 1) (Rel j) T y) ∧
      HasUniformFibers T Q3 point ∧
      (∀j,HasUniformFibers T Q3
        (fun z => sliceClass m (NativeFixedHorizontalMenu.depths J m j) (point z))) ∧
      HasUniformFibers T Q3 grain ∧
      (∀x y,x∈T → y∈T → grain x=grain y → quotient x=quotient y) ∧
      (∀g∈T.image grain,t ≤ Cq*(F3:ℝ)*(Q3:ℝ)^2*(T.filter (fun z => grain z=g)).card) ∧
      ∀height : ℤ,
        ADBounds (realizedSlice (T.image point) (horizontalMesh m) height)
          (horizontalMesh m) KAD (3-extremalExponent) := by
  intro Q3 F3 point L U B KAD
  let depth := NativeFixedHorizontalMenu.depths J m
  have hdepth (j : Fin (J+1)) := NativeFixedHorizontalMenu.depths_bounds J m hm6 j
  have hp : (parentEdges D a (2^m) E p).Nonempty := hSn.mono (hSH.trans hH)
  have Hbase : HasColumnPowerProfile D a m (phaseDepth m) E p profileLower profileUpper := by
    simpa only [NativeFixedHorizontalMenu.depths_last J m hJ hm6] using Hprofile (Fin.last J)
  have Hcounts := caller_reference_menu_counts h original R level Hbackbone m hm6 hbL
    depth (fun j => (hdepth j).1) (fun j => (hdepth j).2) E hE p hp population hpopulation hpop
    profileLower profileUpper hL hU Hbase Hprofile Qref Hcaller
  let lower := fun j : Fin (J+1) => (L/U)*(radius (phaseDepth m) (depth j))^(3-extremalExponent)
  have hRatio (j : Fin (J+1)) : lower j*
      ((((parentEdges D a (2^m) E p).image point).image (sliceClass m (depth j))).card) ≤
      ((parentEdges D a (2^m) E p).image point).card := by
    change lower j*((points D a m (phaseDepth m) E p).image
      (horizontalCoarsen (phaseDepth m) (depth j))).card ≤ (points D a m (phaseDepth m) E p).card
    rw [points_coarsen D a m (phaseDepth m) (depth j) (hdepth j).2 E p]
    exact (Hcounts.2 j).1.1
  obtain ⟨T,hTS,hTn,hcost,hExtra,hTP,hTC,hTG,hTquotient,hTgrain,_hPointRet,_hLocal⟩ :=
    exists_slice_grain_core (parentEdges D a (2^m) E p) H S hH hSH hSn point
      (fun j => sliceClass m (depth j)) grain quotient hquotient Qref Hcounts.1
      lambda G Cq t hlambda.le hG.le hCq.le hret hquotientRet hgrain lower hRatio Rel hrefl hsym L3 hL3
  refine ⟨T,hTS,hTn,hcost,hExtra,hTP,hTC,hTG,hTquotient,hTgrain,?_⟩
  have hF3 : (0:ℝ)<F3 := by exact_mod_cast refinementCost_pos (d+1) (J+1) L3
  have hcostR : (S.card:ℝ) ≤ (F3:ℝ)*T.card := by exact_mod_cast hcost
  have hretT : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ (G*Cq*(F3:ℝ))*T.card := by
    calc
      _ ≤ G*H.card := hret
      _ ≤ G*(Cq*S.card) := mul_le_mul_of_nonneg_left hquotientRet hG.le
      _ = (G*Cq)*(S.card:ℝ) := by ring
      _ ≤ (G*Cq)*((F3:ℝ)*T.card) := mul_le_mul_of_nonneg_left hcostR (mul_nonneg hG.le hCq.le)
      _ = _ := by ring
  exact retained_slice_ADBounds h original R level Hbackbone m ((phaseDepth m-m)/J+1)
    hm6 hbL hJ depth (NativeFixedHorizontalMenu.depths_zero J m)
    (NativeFixedHorizontalMenu.depths_last J m hJ hm6) (fun j => (hdepth j).2)
    (NativeFixedHorizontalMenu.depths_monotone J m) (NativeFixedHorizontalMenu.depths_gap J m hJ)
    E hE p population hpopulation hpop profileLower profileUpper hL hU Hprofile Qref Hcaller
    T (hTS.trans (hSH.trans hH)) hTn Q3 hTP hTC lambda (G*Cq*(F3:ℝ))
    hlambda (by positivity) hretT

end NativeRetainedSliceGrainAD
