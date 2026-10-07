import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_core
import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_actual_ad
import Theorems.Thm_StickyKakeya4_native_parent_slice_relation_readback

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section
namespace NativeActualXYGrainCore
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeAnisotropicSliceLabels NativeSliceCountComparison
open NativeReferenceColumnExponents NativeReferenceSliceClassBounds NativeReferenceHorizontalMenu
open NativeReferenceSliceAllRadii NativeSliceClassBalls NativeSliceRadiusInterpolation
open NativeSquaredGrainQueries NativeSliceADConstant NativeRetainedSliceCore
open NativeRetainedGrainDensityCore NativeRetainedGrainDensityTransfer NativeTwoMapRetainedSliceCore
open NativeTwoMapRetainedSliceActualCaps NativeTwoMapRetainedSliceActualAD
open NativeReferenceXYGridPoints FiniteVoronoiRealADCoarsening SelfUniform
open scoped Matrix.Norms.Elementwise

/-- A single third incidence core installs actual XY point/classes, old grain,
original point equality, and all caller relations before deriving XY AD. -/
theorem exists_actual_xy_grain_core {n d J : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
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
    (ell : ℕ) (P : Submodule ℝ E4) (hP : P≤NativeHorizontalGrainSlice.heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (field : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hfield : ∀height,‖field height‖ ≤ (1/4:ℝ))
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
    let F3 := refinementCost (d+2) (J+1) L3
    let xy := fun z : Fin n × Index => encodedPoint D a m ell p P hP hell hell4 hd field z.2
    let low := lowerCountCoefficient D.thickness zeta population profileUpper
    let up := upperCountCoefficient D.thickness zeta profileLower
    let Ci : ℝ := ((201^3:ℕ):ℝ)
    let Cf : ℝ := ((1201^3:ℕ):ℝ)
    let gap : ℝ := max 64 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
    let KXY := constant (lambda*(low/up)/((G*Cq*(F3:ℝ))*(Qref:ℝ)^2*Ci*Cf*(Q3:ℝ)^4))
      ((27*Cf)*(Cf*Ci*((Qref:ℝ)^4*up/low))) gap (3-extremalExponent)
    ∃T⊆S,T.Nonempty ∧ S.card ≤ F3*T.card ∧
      (∀j x y,x∈T → y∈T → degree (fun _ : Fin n × Index => 1) (Rel j) T x ≤
        Q3^2*degree (fun _ : Fin n × Index => 1) (Rel j) T y) ∧
      HasUniformFibers T Q3 Prod.snd ∧ HasUniformFibers T Q3 xy ∧
      (∀j,HasUniformFibers T Q3 (fun z => horizontalCoarsen (phaseDepth m)
        (NativeFixedHorizontalMenu.depths J m j) (xy z))) ∧
      HasUniformFibers T Q3 grain ∧
      (∀x y,x∈T → y∈T → grain x=grain y → quotient x=quotient y) ∧
      (∀g∈T.image grain,t ≤ Cq*(F3:ℝ)*(Q3:ℝ)^2*(T.filter (fun z => grain z=g)).card) ∧
      (lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ (G*Cq*(F3:ℝ))*T.card) ∧
      ∀height : ℤ,ADBounds (realizedSlice (T.image xy) (NativeReferenceXYGridPoints.mu m) height)
        (NativeReferenceXYGridPoints.mu m) KXY (3-extremalExponent) := by
  intro Q3 F3 xy low up Ci Cf gap KXY
  let I := parentEdges D a (2^m) E p
  let ref := fun z : Fin n × Index => pref D a m p z.2
  let depth := NativeFixedHorizontalMenu.depths J m
  have hdepth (j : Fin (J+1)) := NativeFixedHorizontalMenu.depths_bounds J m hm6 j
  have hp : I.Nonempty := hSn.mono (hSH.trans hH)
  have Hbase : HasColumnPowerProfile D a m (phaseDepth m) E p profileLower profileUpper := by
    simpa only [NativeFixedHorizontalMenu.depths_last J m hJ hm6] using Hprofile (Fin.last J)
  have Hcounts := caller_reference_menu_counts h original R level Hbackbone m hm6 hbL
    depth (fun j => (hdepth j).1) (fun j => (hdepth j).2) E hE p hp population hpopulation hpop
    profileLower profileUpper hL hU Hbase Hprofile Qref Hcaller
  have hWitness := hSn
  obtain ⟨z,hz⟩ := hWitness
  have hzp := (mem_filter.mp (hH (hSH hz))).2
  have Hcaps := encoded_capacities h m ell hm6 p z.1 hzp P hP hell hell4 hd field hfield I
  let lower := fun j : Fin (J+1) => (low/up)*(radius (phaseDepth m) (depth j))^(3-extremalExponent)
  have hRatio (j : Fin (J+1)) : lower j*
      (((I.image ref).image (horizontalCoarsen (phaseDepth m) (depth j))).card) ≤ (I.image ref).card := by
    change lower j*((points D a m (phaseDepth m) E p).image
      (horizontalCoarsen (phaseDepth m) (depth j))).card ≤ (points D a m (phaseDepth m) E p).card
    rw [points_coarsen D a m (phaseDepth m) (depth j) (hdepth j).2 E p]
    exact (Hcounts.2 j).1.1
  let extras := grainRelations (Prod.snd : Fin n × Index → Index) Rel
  obtain ⟨T,hTS,hTn,hcost,hExtra,hTP,hTC,hTG,hTquot,hTgrain,_hPointRet,_hLocal⟩ :=
    exists_two_map_slice_grain_core I H S hH hSH hSn ref
      (fun j => horizontalCoarsen (phaseDepth m) (depth j)) xy
      (fun j => horizontalCoarsen (phaseDepth m) (depth j)) grain quotient hquotient
      Qref (201^3) (fun _ => 1201^3) Hcounts.1 Hcaps.1
      (fun j => (Hcaps.2.2 (phaseDepth m) (depth j)).1)
      lambda G Cq t hlambda.le hG.le hCq.le hret hquotientRet hgrain lower hRatio
      extras (grainRelations_refl Prod.snd Rel hrefl) (grainRelations_symm Prod.snd Rel hsym) L3 hL3
  have hOld : HasUniformFibers T Q3 Prod.snd := by
    apply extra_relation_grain_uniformity T Q3 Prod.snd extras (Fin.natAdd d (0:Fin 1))
      (fun x y => ?_) (hExtra (Fin.natAdd d (0:Fin 1)))
    simp only [extras,grainRelations,Fin.addCases_right]
  have hF3 : (0:ℝ)<F3 := by exact_mod_cast refinementCost_pos (d+2) (J+1) L3
  have hcostR : (S.card:ℝ) ≤ (F3:ℝ)*T.card := by exact_mod_cast hcost
  have hretT : lambda*(I.card:ℝ) ≤ (G*Cq*(F3:ℝ))*T.card := by
    calc
      _ ≤ G*H.card := hret
      _ ≤ G*(Cq*S.card) := mul_le_mul_of_nonneg_left hquotientRet hG.le
      _ = (G*Cq)*(S.card:ℝ) := by ring
      _ ≤ (G*Cq)*((F3:ℝ)*T.card) := mul_le_mul_of_nonneg_left hcostR (mul_nonneg hG.le hCq.le)
      _ = _ := by ring
  refine ⟨T,hTS,hTn,hcost,?_,hOld,hTP,hTC,hTG,hTquot,hTgrain,hretT,?_⟩
  · intro j x y hx hy
    simpa only [extras,grainRelations,Fin.addCases_left] using hExtra (Fin.castAdd 1 j) x y hx hy
  · exact actual_ADBounds h original R level Hbackbone m ell hm6 hbL hJ E hE p
      population hpopulation hpop profileLower profileUpper hL hU Hprofile Qref Hcaller P hP hell hell4 hd
      field hfield T (hTS.trans (hSH.trans hH)) hTn Q3 hTP hTC lambda (G*Cq*(F3:ℝ))
      hlambda (by positivity) hretT

end NativeActualXYGrainCore
