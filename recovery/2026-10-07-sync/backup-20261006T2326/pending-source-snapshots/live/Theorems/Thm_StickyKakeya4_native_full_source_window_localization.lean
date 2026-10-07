import Theorems.Thm_StickyKakeya4_native_full_chart_cell_visits
import Theorems.Thm_StickyKakeya4_native_graph_height_localization
import Theorems.Thm_StickyKakeya4_native_graph_physical_localization

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
noncomputable section
namespace NativeFullSourceWindowLocalization
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeFullCoarseShadow OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open NativeGraphPhysicalLocalization NativeGraphHeightLocalization NativeFullChartCellVisits

/-- One actual fullSource graph is restricted first to a quantitatively
populated height window, then to a physical cell. Both cuts retain every
tube at each surviving point. The normalized height-density loss is the
fixed factor 2*17^4; the original tube labels, actual times and ambient
reference stay fixed. The explicit height-window vertex loss still depends
on the number of height bins. This is a scalar-window input, not a claim of
subpower raw-edge retention or native admission of the restricted graph. -/
theorem exists_same_source_window {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level b : ℕ) (hb : 8 ≤ b) (E : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4, O x (3:Fin 4)=x (3:Fin 4))
    (I : Finset (E4 × Fin (R.image (parentLabel D a (2^b))).card)) (hIne : I.Nonempty)
    {rho cellWidth lambda : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hscale : 8*(64/((2^b:ℕ):ℝ)) ≤ rho^2)
    (hWidth : rho/2 ≤ cellWidth) (hlambda : 0 ≤ lambda)
    (hI : ∀x i, (x,i)∈I → x∈markedUnitTube
      (MarkedIsometricChart.line O 0 ((fullSource h R a level b E).line i))
      (64/((2^b:ℕ):ℝ)))
    (hmass : lambda*((I.image (fun e => e.1 (3:Fin 4))).card:ℝ)*
      (TwoTubePathCollisionCount.tubes I).card ≤ (vertices I (fun p => p 3)).card) :
    let Z := I.image (fun e => e.1 (3:Fin 4))
    let bins := Z.image (fun z => ⌊z/rho⌋)
    ∃k∈bins,
      let Irho := cut I (fun p => ⌊p 3/rho⌋) k
      let Zrho := Z.filter (fun z => ⌊z/rho⌋=k)
      ∃c∈Irho.image (fun e => wzDyadicCellIndex cellWidth e.1),
        let J := cut Irho (wzDyadicCellIndex cellWidth) c
        J.Nonempty ∧ J⊆I ∧
        (∀p∈TwoTubePathCollisionCount.points J, tubesAt J p=tubesAt I p) ∧
        ((vertices I (fun p => p 3)).card:ℝ) ≤
          2*(bins.card:ℝ)*(vertices Irho (fun p => p 3)).card ∧
        lambda*(Zrho.card:ℝ)*(TwoTubePathCollisionCount.tubes J).card ≤
          (2*17^4:ℝ)*(vertices J (fun p => p 3)).card ∧
        rho*lambda*(Z.card:ℝ) ≤ 8*(Zrho.card:ℝ) ∧
        (∀p∈TwoTubePathCollisionCount.points J, p 3∈Zrho ∧
          wzDyadicCellIndex cellWidth p=c) ∧
        Zrho.Nonempty ∧ (∀s∈Zrho, ∀t∈Zrho, |s-t| ≤ rho) ∧
        ∀p∈TwoTubePathCollisionCount.points J, ∀q∈TwoTubePathCollisionCount.points J,
          |p 3-q 3| ≤ rho := by
  intro Z bins
  have hbox : ∀z∈Z, |z| ≤ 1 := by
    intro z hz
    obtain ⟨e,he,rfl⟩ := mem_image.mp hz
    exact (NativeFullChartTubeGraph.full_source_graph_bounds h R a level b hb E O hO e.2 e.1
      (hI e.1 e.2 he)).1
  obtain ⟨k,hk,hRhoNe,hRhoSub,hRhoFiber,hRet,hRhoDensity,hHeight,hRhoDiam⟩ :=
    exists_massive_height_window I hIne (fun p => p 3) hrho hrho1 hlambda hbox hmass
  let Irho := cut I (fun p => ⌊p 3/rho⌋) k
  let Zrho := Z.filter (fun z => ⌊z/rho⌋=k)
  have hRhoMass : (lambda/2)*(Zrho.card:ℝ)*(TwoTubePathCollisionCount.tubes Irho).card ≤
      (vertices Irho (fun p => p 3)).card := by nlinarith only [hRhoDensity]
  have hVisit : ∀i∈Irho.image Prod.snd,
      ((Irho.filter (fun e => e.2=i)).image (fun e => wzDyadicCellIndex cellWidth e.1)).card ≤ 17^4 := by
    intro i hi
    exact actual_full_source_visits h R a level b hb E O hO Irho hrho hrho1 hscale hWidth
      (fun x j hxj => hI x j (hRhoSub hxj)) hRhoDiam i hi
  obtain ⟨c,hc,hJne,hJsub,hJFiber,hDensity⟩ :=
    exists_cell_with_height_density Irho hRhoNe (fun p => p 3) Zrho
      (wzDyadicCellIndex cellWidth) (17^4) (show 0 ≤ lambda/2 by positivity) hRhoMass hVisit
  let J := cut Irho (wzDyadicCellIndex cellWidth) c
  have hPointSub : TwoTubePathCollisionCount.points J⊆TwoTubePathCollisionCount.points Irho :=
    image_subset_image hJsub
  refine ⟨k,hk,c,hc,hJne,hJsub.trans hRhoSub,?_,hRet,?_,hHeight,?_,?_,?_,?_⟩
  · intro p hp
    exact (hJFiber p hp).trans (hRhoFiber p (hPointSub hp))
  · have hh := hDensity
    norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hh
    nlinarith only [hh]
  · intro p hp
    have hpRho := hPointSub hp
    have hpI : p∈TwoTubePathCollisionCount.points I := image_subset_image hRhoSub hpRho
    obtain ⟨e,he,hep⟩ := mem_image.mp hpI
    exact ⟨mem_filter.mpr ⟨mem_image.mpr ⟨e,he,congrArg (fun p : E4 => p 3) hep⟩,
      cut_point_cell I (fun p => ⌊p 3/rho⌋) k p hpRho⟩,
      cut_point_cell Irho (wzDyadicCellIndex cellWidth) c p hp⟩
  · obtain ⟨e,he⟩ := hRhoNe
    exact ⟨e.1 3,mem_filter.mpr ⟨mem_image_of_mem _ (hRhoSub he),
      (mem_filter.mp he).2⟩⟩
  · intro s hs t ht
    exact floor_window_diameter hrho s t
      ((mem_filter.mp hs).2.trans (mem_filter.mp ht).2.symm)
  · intro p hp q hq
    exact hRhoDiam p (hPointSub hp) q (hPointSub hq)

end NativeFullSourceWindowLocalization
