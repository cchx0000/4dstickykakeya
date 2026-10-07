import Theorems.Thm_StickyKakeya4_native_actual_baseline_graph_mass
import Theorems.Thm_StickyKakeya4_native_whole_Y_graph_retention
import Theorems.Thm_StickyKakeya4_native_configured_third_relation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6500000
noncomputable section
namespace NativeActualCommonYGraphMass
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeLocalParentSource NativeMiddleWindowBalance CanonicalConfiguredE4Bridge
open NativeConfiguredIncidenceFibers NativeActualSparseReferenceAdmission NativeActualBaselineGraphMass
open NativeConfiguredThirdRelation NativeJointUniformCoarseRelations NativeWholeYGraphRetention
open NativeLiteralYHeightAlignment SelfUniform

/-- Decode the installed original relations into the actual point-first
fine output graph. The output-index realization adds no fiber loss. -/
theorem caller_uniformities {n d : ℕ} {D : FiniteScaleSource n} {eta etaRef a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (m u : ℕ) (p : Parent)
    (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef)
    (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (R0 Q : ℕ)
    (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hrel : ∀j x y,x∈T → y∈T →
      degree (fun _ : Fin n × Index => 1)
        (completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra j) T x ≤
      Q^2*degree (fun _ : Fin n × Index => 1)
        (completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra j) T y) :
    let key:=fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2
    let cfg:=NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0
    let graph:=fun z : Fin n × Index => (cfg z.2,outputTube h R Eref a m (u+12) p href z.1)
    HasUniformFibers T Q key ∧ HasUniformFibers T Q graph := by
  intro key cfg graph
  have HP:=caller_geometricPair_uniformity D a m p .oneTwo P hP hd F Fcfg R0 u extra T Q Hrel
  constructor
  · intro x hx y hy
    have hh:=Hrel 0 x y hx hy
    change degree (fun _ : Fin n × Index => 1) (fun x y => key x=key y) T x ≤
      Q^2*degree (fun _ : Fin n × Index => 1) (fun x y => key x=key y) T y at hh
    simpa only [unit_degree_eq_fiber] using hh
  · intro x hx y hy
    rw [←outputPair_fiber_eq h R Eref a m (u+12) p href cfg T hparent x hx,
      ←outputPair_fiber_eq h R Eref a m (u+12) p href cfg T hparent y hy]
    exact HP x hx y hy

/-- Genuine sparse admission supplies the baseline mass, and the actual
planar alignment family supplies the common Y choice. Their unchanged
third-core relations produce the fine-graph total on that SAME Y cut.
The local-source thickness is sigma=32768rho/tau throughout. -/
theorem exists_actual_common_mass (e window : ℝ) (he : 0 < e) (hw : 0 < window) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta)
      (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
      (a zeta : ℝ), 0 ≤ zeta → HasOriginalBackbone D original R a level zeta →
      ∀ (Eref H T : Finset (Fin n × Index)) (m : ℕ), 6 ≤ m →
      ∀ (p : Parent) (etaRef : ℝ)
        (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef),
      T ⊆ Eref → Eref ⊆ incidences original →
      (∀ z ∈ T, z.1 ∈ parentLabels D R a (2 ^ m) p) →
      (source h R Eref a m p).thickness ≤ eps0 → etaRef ≤ window * e / 256 →
      (64 : ℝ) ^ 3 * (source h R Eref a m p).thickness ^ (window * e / 16) ≤ D.thickness ^ zeta →
      ∀ population cost : ℝ, 0 < population → 0 < cost →
        population * (parentLabels D R a (2 ^ m) p).card ≤ D.thickness * H.card →
        (H.card : ℝ) ≤ cost * T.card →
      ∀ u : ℕ, m + (u+12) ≤ level →
        64 / ((2 ^ (u+12) : ℕ) : ℝ) ≤ (source h R Eref a m p).thickness ^ window →
        retentionFactor cost population ≤ (64 / ((2 ^ (u+12) : ℕ) : ℝ)) ^ (-(e / 32)) →
      ∀ (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
        (hd : Module.finrank ℝ P = 1)
        (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ),
      (∀ t u v, |F t u v| ≤ 1 / 4) → (∀ t u v, |Fcfg t u v| ≤ 1 / 4) →
      ∀ (R0 : ℕ), 0 < R0 → rho m ≤ mu m * (R0 : ℝ) →
        mu m * (R0 : ℝ) = 4096 / ((2 ^ (u+12) : ℕ) : ℝ) →
      ∀(d bins Q : ℕ)
        (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
      (∀j x y,x∈T → y∈T →
        degree (fun _ : Fin n × Index => 1)
          (completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra j) T x ≤
        Q^2*degree (fun _ : Fin n × Index => 1)
          (completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra j) T y) →
      let key:=fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2
      let cfg:=NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0
      let graph:=fun z : Fin n × Index => (cfg z.2,outputTube h R Eref a m (u+12) p href z.1)
      ∀t zeta53 chi : ℝ,
      ∀(W : ∀height : {height : ℤ // height∈(T.image key).image Prod.fst},
        HeightAlignment (T.image key) u t zeta53 chi height.val)
        (bin : ℝ → Fin (bins+1)),
      ∃c : NativeYCommonScaleSelection.Menu u bins,∃selected : Finset Key,
        selected⊆T.image key ∧ selected.Nonempty ∧
        let eps:=64/((2^(u+12):ℕ):ℝ)
        let N:ℝ:=2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ)
        let Ycut:=T.filter (fun z => key z∈selected)
        (16/(5:ℝ)^4)*(localSigma c/32768)^zeta53*eps^(5*e/16) ≤
          N*(Q:ℝ)^4*eps^4*((Ycut.image graph).card:ℝ) ∧
        ∀height∈selected.image Prod.fst,∃hh : height∈(T.image key).image Prod.fst,
          (W ⟨height,hh⟩).chart=c.1 ∧ (W ⟨height,hh⟩).rhoDepth=c.2.1 ∧
          (W ⟨height,hh⟩).tauDepth=c.2.2.1 ∧ bin (W ⟨height,hh⟩).exponent=c.2.2.2 ∧
          heightPoints selected ((2:ℝ)⁻¹^u/512) height=(W ⟨height,hh⟩).selected := by
  obtain ⟨eps0,heps0,Hbase⟩:=exists_actual_baseline_mass e window he hw
  refine ⟨eps0,heps0,?_⟩
  intro n D eta h original R level a zeta hzeta HB Eref H T m hm p etaRef href
    hTE hEorig hparent hsmall heta hprofile population cost hpop hcost hpopulation hretain
    u hmb hwindow hpaid P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
    d bins Q extra Hrel key cfg graph t zeta53 chi W bin
  have hMass:=Hbase n D eta h original R level a zeta hzeta HB Eref H T m hm p etaRef href
    hTE hEorig hparent hsmall heta hprofile population cost hpop hcost hpopulation hretain
    (u+12) (by omega) hmb hwindow hpaid .oneTwo P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
  have hT : T.Nonempty := by
    by_contra hn
    have heT : T=∅ := not_nonempty_iff_eq_empty.mp hn
    have hpos : 0 < (16/(5:ℝ)^4)*(64/((2^(u+12):ℕ):ℝ))^(5*e/16) := by positivity
    simp only [heT,image_empty,card_empty,Nat.cast_zero,mul_zero] at hMass
    exact (not_le_of_gt hpos) hMass
  obtain ⟨HY,HG⟩:=caller_uniformities h R Eref T m u p href hparent P hP hd F Fcfg R0 Q extra Hrel
  obtain ⟨c,selected,hsel,hsn,_hY,hgraph,hwhole⟩:=
    select_actual_common_graph T hT key graph Q HY HG u bins t zeta53 chi W bin
  let eps:ℝ:=64/((2^(u+12):ℕ):ℝ)
  let N:ℝ:=2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ)
  let Ycut:=T.filter (fun z => key z∈selected)
  have hN : 0 < N := by dsimp [N]; positivity
  have hf : 0 ≤ menuFraction zeta53 c := by unfold menuFraction; positivity
  have hgraph' : menuFraction zeta53 c*((T.image graph).card:ℝ) ≤
      N*(Q:ℝ)^4*((Ycut.image graph).card:ℝ) := by
    have hh:=mul_le_mul_of_nonneg_left hgraph hN.le
    convert hh using 1 <;> field_simp <;> ring
  refine ⟨c,selected,hsel,hsn,?_,hwhole⟩
  calc
    _ = menuFraction zeta53 c*((16/(5:ℝ)^4)*eps^(5*e/16)) := by
      rw [fraction_eq_localSigma]
      ring
    _ ≤ menuFraction zeta53 c*(eps^4*((T.image graph).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hMass hf
    _ = eps^4*(menuFraction zeta53 c*((T.image graph).card:ℝ)) := by ring
    _ ≤ eps^4*(N*(Q:ℝ)^4*((Ycut.image graph).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hgraph' (by positivity)
    _ = _ := by ring

end NativeActualCommonYGraphMass
