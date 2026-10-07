import Theorems.Thm_StickyKakeya4_native_generic_XY_rank
import Theorems.Thm_StickyKakeya4_native_parent_original_point_menu

/- The actual rank-two branch of the same stored source.
Originally drafted without verification; consult current receipts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeActualRankTwoEntry
open Classical Finset StickyKakeya4 NativeGenericReferenceData NativeGenericXYRank
open NativeFixedCompactKakeyaExponent NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeRankExponentHierarchy NativeActualMesoscopicRankConfiguration NativeRankRadiusMenu
open NativeMiddleGrainParentBudget NativeSquaredGrainQueries NativeRetainedGrainHistory
open NativePostGraphXYHookStage

/-- Under the contradiction hypothesis kappa>1 the actual rank-three
alternative is impossible by the already proved dimension range. The
mandatory original-parent/point relation is instantiated before E2. -/
theorem from_source_rank {n L g L2 L3 dOld dExtra Jhorizontal Khalf : ℕ}
    {D : FiniteScaleSource n} {eta tau seed e zeta eta0 c c2 epsilon : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau}
    (ref : Reference h tau htau seed e zeta L g)
    (hk : 1 < extremalExponent) (hK : 3 ≤ Khalf)
    (H : HasXYRankSelection ref (dOld+1) (2*Khalf) Jhorizontal (dExtra+3) Khalf L2 L3 eta0 c c2 epsilon) :
    extremalExponent ≤ 2 ∧
    ∃j : Fin (g+1),
      j∈NativeRankMesoscopicRadiusMenu.menu (rankWindow tau) (rankWindow_pos htau).le g ref.level ∧
      18 ≤ (ref.schedule j).val ∧ (ref.schedule j).val ≤ ref.level/4 ∧
      let r := radius (rankWindow tau) (rankWindow_pos htau).le g ref.level j
      0 < r ∧ r ≤ 1 ∧ r ≤ D.thickness^(cutoff c (1:Fin 4)) ∧
      48*((2^(ref.schedule j).val:ℕ):ℝ)*r=1 ∧ 64*D.thickness ≤ r^2 ∧
      ∃F : Finset (Fin n × Index),F⊆ref.E1 ∧ F.Nonempty ∧
      ∃plane : Index → Submodule ℝ E4,
        (∀z∈F,Metric.infDist (slopeVector D z.1) (plane z.2:Set E4) ≤ r) ∧
      ∃selected : Fin (2*Khalf),
        historyDepth (2*Khalf) (ref.schedule j).val selected=middleDepth (ref.schedule j).val ∧
      ∀RelOld : Fin dOld → (Fin n × Index) → (Fin n × Index) → Prop,
        (∀i x,RelOld i x x) → (∀i x y,RelOld i x y → RelOld i y x) →
      HasXYStage (J:=2*Khalf) h ref.original ref.R ref.E1 F plane ref.a ref.level
        ref.schedule ref.dimension L L2 eta0 c tau seed zeta htau c2 (1:Fin 4) j selected
        Jhorizontal (dExtra+3) L3 Khalf epsilon
        (NativeParentOriginalPointMenu.relations D ref.a (middleDepth (ref.schedule j).val) RelOld) := by
  obtain ⟨ell,j,_hell,hRanks,hRange,hMenu,hcut,hdelta,hrquarter,hidentity,_hscale,hrsquare,
    F,hF,hFn,_hRet,plane,hNear,_hPoint,hstop,_hQueries,selected,hmid,Hstage⟩ := H
  have hellOne : ell=(1:Fin 4) := by
    apply Fin.ext
    rcases hRanks with hrank | hrank
    · simpa using (show ell.val=1 by omega)
    · rw [hrank] at hRange
      norm_num at hRange
      linarith
  subst ell
  have hk2 : extremalExponent ≤ 2 := by norm_num at hRange; linarith
  have hstop18 : 18 ≤ (ref.schedule j).val := by
    dsimp only [NativeGenericCompatibleStage.pairedCount] at hstop
    omega
  have hcap := stopping_depth_cap htau g ref.level ref.schedule ref.schedule_eq j hMenu
  refine ⟨hk2,j,hMenu,hstop18,hcap,h.1.2.1.trans_le hdelta,by linarith only [hrquarter],
    hcut,hidentity,hrsquare,F,hF,hFn,plane,hNear,selected,hmid,?_⟩
  intro RelOld hRefl hSymm
  exact Hstage (NativeParentOriginalPointMenu.relations D ref.a (middleDepth (ref.schedule j).val) RelOld)
    (NativeParentOriginalPointMenu.relations_refl _ _ _ _ hRefl)
    (NativeParentOriginalPointMenu.relations_symm _ _ _ _ hSymm)

end NativeActualRankTwoEntry
