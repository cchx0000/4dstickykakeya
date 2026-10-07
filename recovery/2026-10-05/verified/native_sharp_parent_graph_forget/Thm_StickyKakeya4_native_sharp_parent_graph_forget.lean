import Theorems.Thm_StickyKakeya4_native_sharp_parent_graph_configuration
import Theorems.Thm_StickyKakeya4_native_parent_graph_forget
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeSharpParentGraphForget
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativePrescribedParentGraphData NativePrescribedParentGraphConfiguration
open NativeSharpParentGraphData NativeSharpParentGraphConfiguration

theorem curve_parent_profiles_forget {n K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {original : Fin n → Finset Index}
    {R : Finset (Fin n)} {E1 E2 : Finset (Fin n × Index)} {a : ℝ} {level m : ℕ}
    {plane : Index → Submodule ℝ E4} {points : Finset Index} {q : ℝ} {ell Q2 F1 G Lgrain : ℕ}
    {lambda zeta tau seed c2 : ℝ} {depths : Fin K → ℕ}
    {stop Khalf : ℕ} {tuple : Index → Fin ell → (Fin n × Index)} {r epsilon : ℝ}
    (H : HasSharpCurveParentProfiles h original R E1 E2 a level m plane points q ell Q2 F1 G Lgrain
      lambda zeta tau seed c2 depths stop Khalf tuple r epsilon) :
    HasCurveParentProfiles h original R E1 E2 a level m plane points q ell Q2 F1 G Lgrain
      lambda zeta tau seed c2 depths stop Khalf tuple r epsilon := by
  obtain ⟨ht,hmu,hretain,E,hEK,hEn,hhalf,p,hp,hEpn,hpop,href,hgrain,_hmin,hprofiles,hcleaned,
    hheightL,hheightU,hdescendant,hplane,hmetric,hgraph⟩ := H
  exact ⟨ht,hmu,hretain,E,hEK,hEn,hhalf,p,hp,hEpn,hpop,href,hgrain,hprofiles,hcleaned,
    hheightL,hheightU,hdescendant,hplane,hmetric,hgraph⟩

/-- Forget only the additional graph cut/metric fields. The original final
point core, population-rich parent and every reference profile remain exact. -/
theorem curve_cleanup_forget {n J Kmenu : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {E : Finset (Fin n × Index)}
    {m : Fin J → ℕ} {q : ℝ} {ell Q : ℕ} {S0 : Finset Index} {r etaRank : ℝ}
    {point : Fin J → Index → Index} {tuple : Fin J → Index → Fin ell → (Fin n × Index)}
    {anchor : Fin J → Index → Fin ell → Fin n} {original : Fin n → Finset Index}
    {R : Finset (Fin n)} {E1 : Finset (Fin n × Index)} {level F1 G stop Khalf : ℕ}
    {lambda zeta tau seed c2 epsilon : ℝ} {selected : Fin J} {depths : Fin Kmenu → ℕ}
    (H : SharpCurveParentFinalCleanupData h a E m q ell Q S0 r etaRank point tuple anchor
      original R E1 level F1 G stop lambda zeta tau seed c2 selected depths Khalf epsilon) :
    CurveParentFinalCleanupData h a E m q ell Q S0 r etaRank point tuple anchor
      original R E1 level F1 G stop lambda zeta tau seed c2 selected depths Khalf epsilon := by
  obtain ⟨K,hKF,hKn,hhalf,htotal,hfinal,hcounts,hdense,HsysK,hTrace,Hcurve⟩ := H
  exact ⟨K,hKF,hKn,hhalf,htotal,hfinal,hcounts,hdense,HsysK,hTrace,curve_parent_profiles_forget Hcurve⟩

theorem curve_retained_forget {n Kmenu J ell stop Q2 Khalf : ℕ} {D : FiniteScaleSource n}
    {eta a q r etaRank lambda c1 c2 epsilon : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {E : Finset (Fin n × Index)} {original : Fin n → Finset Index} {R : Finset (Fin n)}
    {E1 : Finset (Fin n × Index)} {level F1 G : ℕ} {zeta tau seed : ℝ}
    {selected : Fin J} {depths : Fin Kmenu → ℕ}
    (H : HasSharpCurveParentRetainedHistory h a stop E q ell J Q2 r etaRank lambda c1 c2
      original R E1 level F1 G zeta tau seed selected depths Khalf epsilon) :
    HasCurveParentRetainedHistory h a stop E q ell J Q2 r etaRank lambda c1 c2
      original R E1 level F1 G zeta tau seed selected depths Khalf epsilon := by
  obtain ⟨C,hC,S0,hS0,hS,hinj,hmass,hretain,hcompat,hwitness,htrace,
    point,tuple,anchor,Hsys,Hword,Hsame,Hhistory,hHistRet,Hcleanup⟩ := H
  exact ⟨C,hC,S0,hS0,hS,hinj,hmass,hretain,hcompat,hwitness,htrace,
    point,tuple,anchor,Hsys,Hword,Hsame,Hhistory,hHistRet,curve_cleanup_forget Hcleanup⟩

/-- Every prior source/count/profile consumer receives the same E2, words,
history, final K and population-rich parent through this projection. -/
theorem curve_stage_forget {n d J g K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index)) (P : Index → Submodule ℝ E4)
    (a : ℝ) (level : ℕ) (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau seed zeta : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (selected : Fin J) (depths : Fin K → ℕ) (Khalf : ℕ) (epsilon : ℝ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : HasSharpCurveParentStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed zeta htau c2 ell j selected depths Khalf epsilon Rel) :
    HasCurveParentStage (J:=J) h original R E1 F P a level schedule L L2
      eta0 c tau seed zeta htau c2 ell j selected depths Khalf epsilon Rel := by
  obtain ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,hFinal,hQueries,hParent,hCounts⟩ := H
  exact ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,hFamily,
    curve_retained_forget hFinal,hQueries,hParent,hCounts⟩

end NativeSharpParentGraphForget
