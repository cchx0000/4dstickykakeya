/- UNVERIFIED actual same-T AD-to-cover reader for one old-height/phase
subset. Only the unchanged full reference T supplies AD lower bounds. -/
import Theorems.Thm_StickyKakeya4_native_remembered_phase_footprint
import Theorems.Thm_StickyKakeya4_native_third_XY_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeRememberedPhaseCover
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeNormalizedCellRelativeMenu NativeAnisotropicShortRowGeometry NativeTranslatedGrainHeightOverlap
open NativeRememberedPhaseFootprint NativeReferenceXYGridMaps NativeReferenceXYGridField
open NativeSquaredGrainQueries NativeThirdXYData NativeRetainedSliceCore NativeGrainQuotientFibers
open NativeJointLocalXYGeometry NativeLocalParentSource NativeRelativeParentLabels
open NativeFixedCompactKakeyaExponent
open scoped Matrix.Norms.Elementwise

/-- Literal physical labels, with a fixed dimensional menu derived from
the diameter of the actual original physical points. -/
lemma physical_image_card_of_diameter {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m depth : ℕ) (p : Parent) (A : Finset (Fin n × Index))
    (H : ∀z∈A,∀w∈A,dist (oldPoint D a m p z.2) (oldPoint D a m p w.2) ≤
      128*(64/((2^depth:ℕ):ℝ))) :
    (A.image (fun z => physicalCell D a (2^m) (2^depth) p z.2)).card ≤ 257^4 := by
  by_cases hA : A.Nonempty
  · obtain ⟨w,hw⟩ := hA
    have hsub : A.image (fun z => physicalCell D a (2^m) (2^depth) p z.2) ⊆
        columnHalo 128 128 (physicalCell D a (2^m) (2^depth) p w.2) := by
      intro q hq
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
      apply Fintype.mem_piFinset.mpr
      intro j
      simp only [ite_self]
      apply floor_neighbor (by positivity) 128
      have hh : |oldPoint D a m p z.2 j-oldPoint D a m p w.2 j| ≤
          dist (oldPoint D a m p z.2) (oldPoint D a m p w.2) := by
        simpa only [Real.dist_eq] using PiLp.dist_apply_le (oldPoint D a m p z.2) (oldPoint D a m p w.2) j
      exact hh.trans (H z hz w hw)
    exact (card_le_card hsub).trans_eq (by rw [columnHalo_card]; norm_num)
  · simp only [not_nonempty_iff_eq_empty.mp hA,image_empty,card_empty,Nat.zero_le]

/-- A later subset uses the SAME complete T's XY AD. All actual phase and
point geometry is derived here; the output coarse-cover count is not a premise.
The raw query mesh Rd*mu may be512d, independently of the baseline R0. -/
theorem rank_two_from_third {n d J : ℕ} {D : FiniteScaleSource n} {eta etaS a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (Eref : Finset (Fin n × Index))
    (m level : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : phaseDepth m ≤ level) (hscale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hRef : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaS)
    (hRefK : ∀i,(NativeLocalParentSource.source h backbone Eref a m p).line i∈fixedCompactClass)
    (levelS b0 c depth : ℕ) (hb0 : 8 ≤ b0) (hc : c ≤ b0) (hdepth : 6 ≤ depth)
    (hwidth : 64/((2^depth:ℕ):ℝ)=512*(64/((2^c:ℕ):ℝ)))
    (plane : Index → Submodule ℝ E4) (E Hgraph S T : Finset (Fin n × Index))
    (hT : T⊆incidences original)
    (hparent : ∀z∈T,z.1∈parentLabels D backbone a (2^m) p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (Fraw Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (population PL PU : ℝ) (Qref : ℕ) (lambda G Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hdata : HasThirdXYData (J:=J) (ell:=2) D zeta a m plane E Hgraph S T P hP
      (by norm_num) (by norm_num) hd Fraw p population PL PU Qref lambda G Cpre threshold L3 Rel)
    (R0 Rd : ℕ) (hR0 : 0 < R0) (hRd : 0 < Rd)
    (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b0:ℕ):ℝ))
    (hsmall : 512*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (hquery : (Rd:ℝ)*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (hkappa : extremalExponent ≤ 3)
    (A : Finset (Fin n × Index)) (hAT : A⊆T) (height : ℤ) (q : Parent)
    (hHeight : ∀z∈A,translatedHeight D a m z.2=height)
    (hPhase : ∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=q) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 2 plane Sq Fraw
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let F3 := refinementCost (d+2) (J+1) L3
    let K := xyConstant D.thickness zeta population PL PU lambda (G*Cpre*(F3:ℝ)) Qref Q3 J m
    ((A.image (fun z => coarseXY 2 Rd (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F z.2))).card:ℝ) ≤
      (257^4:ℝ)*(9^3:ℝ)*(13^3:ℝ)^2*K^2*6^(3-extremalExponent)*
        ((6*(64/((2^depth:ℕ):ℝ)))/((Rd:ℝ)*mu m))^(3-extremalExponent) := by
  intro Sq F Q3 F3 K
  have Hcopy := Hdata
  rcases Hcopy with ⟨_hTS,_hTn,_hCost,_hTH,_hFinal,_hExtra,_hOld,_hXY,_hClass,
    _hGrain,_hKey,_hThreshold,_hRet,Hxy,_hRead,hNorm⟩
  have hF : ∀t i j,|F t i j| ≤ 1/4 := by
    intro t i j
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp (hNorm t) i j
  let physical := fun z : Fin n × Index => physicalCell D a (2^m) (2^depth) p z.2
  let xy := fun z : Fin n × Index => coarseXY 2 Rd (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F z.2)
  let C : ℝ := (9^3:ℝ)*(13^3:ℝ)^2*K^2*6^(3-extremalExponent)*
    ((6*(64/((2^depth:ℕ):ℝ)))/((Rd:ℝ)*mu m))^(3-extremalExponent)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 1 ≤ K := xyConstant_one_le _ _ _ _ _ _ _ _ _ _ _
  have hCard : (A.image physical).card ≤ 257^4 := by
    apply physical_image_card_of_diameter D a m depth p A
    intro z hz w hw
    have hcfg := actual_configured_diameter h original horiginal ha backbone Eref T m (by omega)
      hscale p hRef hRefK levelS b0 c hb0 hc .oneTwo P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
      z w (hT (hAT hz)) (hT (hAT hw)) (hparent z (hAT hz)) (hparent w (hAT hw))
      ((hHeight z hz).trans (hHeight w hw).symm) ((hPhase z hz).trans (hPhase w hw).symm)
    have hcw : 64/((2^b0:ℕ):ℝ) ≤ 64/((2^c:ℕ):ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hc
    have hbasew : mu m*(R0:ℝ) ≤ 64*(64/((2^c:ℕ):ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left hcw (by norm_num : (0:ℝ) ≤ 64)
      have he : 4096/((2^b0:ℕ):ℝ)=64*(64/((2^b0:ℕ):ℝ)) := by ring
      rw [he] at hmatch
      exact hmatch.trans hh
    have hmuw : mu m ≤ 64/((2^c:ℕ):ℝ) := by rw [hwidth] at hsmall; linarith only [hsmall]
    have ho := oldPoint_dist_of_configured h m (by omega) p z.1
      ((mem_parentLabels D backbone a (2^m) p _).mp (hparent z (hAT hz))).2
      .oneTwo P hP hd F Fcfg hF hCfg R0 hR0 hbase (by positivity) hmuw hbasew z.2 w.2 hcfg
    simpa only [hwidth] using ho
  have hLocal (v : Index) (_hv : v∈A.image physical) :
      (((A.filter (fun z => physical z=v)).image xy).card:ℝ) ≤ C := by
    let U := A.filter (fun z => physical z=v)
    by_cases hU : U.Nonempty
    · obtain ⟨anchor,hanchor⟩ := hU
      have hUT : U⊆T := (filter_subset _ _).trans hAT
      have hh := source_height_cell_base_keys h original horiginal ha m level 2 hm hdy hf p U T hUT
        hT (fun z hz => ((mem_parentLabels D backbone a (2^m) p _).mp (hparent z hz)).2)
        P hP (by norm_num) (by norm_num) hd F hNorm Rd depth hRd hdepth hsmall hquery
        anchor hanchor
        (fun z hz => (hHeight z (mem_filter.mp hz).1).trans (hHeight anchor (mem_filter.mp hanchor).1).symm)
        (fun z hz => (mem_filter.mp hz).2.trans (mem_filter.mp hanchor).2.symm)
        hK (by linarith only [hkappa]) (Hxy (translatedHeight D a m anchor.2))
      simpa only [U,xy,C,Nat.cast_pow,Nat.cast_ofNat] using hh
    · simp only [U,not_nonempty_iff_eq_empty.mp hU,image_empty,card_empty,Nat.cast_zero]
      exact hC
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images A xy physical C hLocal
  have hreal : ((A.image physical).card:ℝ) ≤ (257^4:ℝ) := by exact_mod_cast hCard
  have hbound := mul_le_mul_of_nonneg_left hreal hC
  exact hh.trans (by dsimp [C] at hbound; simpa only [mul_assoc,mul_left_comm,mul_comm] using hbound)

end NativeRememberedPhaseCover
