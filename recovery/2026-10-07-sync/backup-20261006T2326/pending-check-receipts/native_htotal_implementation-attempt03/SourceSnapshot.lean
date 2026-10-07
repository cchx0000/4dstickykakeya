/- UNVERIFIED combined frozen htotal implementation. Original modules remain unchanged. No strict check has run. -/
import Theorems.Thm_StickyKakeya4_native_configured_Y_weighted_retention
import Theorems.Thm_StickyKakeya4_native_retained_slice_count_transfer
import Theorems.Thm_StickyKakeya4_native_literal_Y_height_alignment
import Theorems.Thm_StickyKakeya4_native_actual_baseline_graph_mass
import Theorems.Thm_StickyKakeya4_native_configured_third_relation
import Theorems.Thm_StickyKakeya4_native_output_alignment_menu_budget
import Theorems.Thm_StickyKakeya4_native_same_Q_fine_graph
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data
import Theorems.Thm_StickyKakeya4_native_parent_height_graph_core
import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_extra
import Theorems.Thm_StickyKakeya4_native_retention_output_power
import Theorems.Thm_StickyKakeya4_native_actual_sparse_reference_admission
import Theorems.Thm_StickyKakeya4_native_paid_third_budget
import Theorems.Thm_StickyKakeya4_native_rank_exponent_hierarchy
import Theorems.Thm_StickyKakeya4_native_configured_output_pairs
import Theorems.Thm_StickyKakeya4_native_full_coarse_shadow
import Theorems.Thm_StickyKakeya4_native_original_parent_density_core
import Theorems.Thm_StickyKakeya4_native_reference_parent_population
import Theorems.Thm_StickyKakeya4_native_reference_parent_admission_budget
import Theorems.Thm_StickyKakeya4_native_actual_relative_coarse_admission
import Theorems.Thm_StickyKakeya4_native_actual_new_cut_budget

open NativeCubicalIncidenceCounts NativeHorizontalGrainSlice NativeFixedCompactKakeyaExponent
open NativeDyadicTubeStopping CanonicalConfiguredE4Bridge

/- Frozen origin: Thm_StickyKakeya4_native_whole_Y_graph_retention.lean; SHA256 6de64dc53fb0bad0d3664c51d9682bbe6c0492b948d4b07ae2de4162da248b67. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeWholeYGraphRetention
open Classical Finset NativeJointUniformCoarseRelations
open NativeConfiguredYWeightedRetention NativeRetainedSliceCountTransfer
open FiniteCoarseYThresholdSelection NativeLiteralYHeightAlignment
open scoped BigOperators

/-- The actual Y-key and graph-fiber comparisons transfer ORIGINAL Y-key
retention to distinct graph pairs, with exactly Q^4 and no mesh-power tax. -/
theorem graph_retention {A Y G : Type*}
    [DecidableEq A] [DecidableEq Y] [DecidableEq G]
    (T : Finset A) (key : A → Y) (graph : A → G) (Q : ℕ)
    (HY : HasUniformFibers T Q key) (HG : HasUniformFibers T Q graph)
    (selected : Finset Y) (hselected : selected⊆T.image key)
    (theta : ℝ) (htheta : 0 ≤ theta)
    (hret : theta*((T.image key).card:ℝ) ≤ (selected.card:ℝ)) :
    theta*((T.image graph).card:ℝ) ≤
      (Q:ℝ)^4*(((T.filter (fun z => key z∈selected)).image graph).card:ℝ) := by
  let U:=T.filter (fun z => key z∈selected)
  have hU : U⊆T := filter_subset _ _
  have hm : theta*(T.card:ℝ) ≤ (Q:ℝ)^2*(U.card:ℝ) :=
    uniform_subset_retention T key Q HY selected hselected theta htheta hret
  by_cases hT : T.Nonempty
  · have hh := point_image_retention T U hU hT graph Q HG theta ((Q:ℝ)^2) (sq_nonneg _) hm
    convert hh using 1
    ring
  · have he : T=∅ := not_nonempty_iff_eq_empty.mp hT
    simp only [he,image_empty,filter_empty,card_empty,Nat.cast_zero,mul_zero,le_refl]

/-- The genuine common-scale selector is called here. The common class is
weighted by ORIGINAL Y cardinality, and its own relative fraction is kept. -/
theorem select_actual_common_graph {A G : Type*} [DecidableEq A] [DecidableEq G]
    (T : Finset A) (hT : T.Nonempty) (key : A → Key) (graph : A → G) (Q : ℕ)
    (HY : HasUniformFibers T Q key) (HG : HasUniformFibers T Q graph)
    (u bins : ℕ) (t zeta chi : ℝ)
    (W : ∀h : {h : ℤ // h∈(T.image key).image Prod.fst},
      HeightAlignment (T.image key) u t zeta chi h.val)
    (bin : ℝ → Fin (bins+1)) :
    ∃c : NativeYCommonScaleSelection.Menu u bins,∃selected : Finset Key,
      selected⊆T.image key ∧ selected.Nonempty ∧
      menuFraction zeta c*((T.image key).card:ℝ) ≤
        (2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ))*(selected.card:ℝ) ∧
      let U:=T.filter (fun z => key z∈selected)
      (menuFraction zeta c/(2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ)))*((T.image graph).card:ℝ) ≤
        (Q:ℝ)^4*((U.image graph).card:ℝ) ∧
      ∀h∈selected.image Prod.fst,∃hh : h∈(T.image key).image Prod.fst,
        (W ⟨h,hh⟩).chart=c.1 ∧ (W ⟨h,hh⟩).rhoDepth=c.2.1 ∧
        (W ⟨h,hh⟩).tauDepth=c.2.2.1 ∧ bin (W ⟨h,hh⟩).exponent=c.2.2.2 ∧
        heightPoints selected ((2:ℝ)⁻¹^u/512) h=(W ⟨h,hh⟩).selected := by
  obtain ⟨c,selected,hsel,hsn,hret,hwhole⟩ :=
    select_aligned_common (T.image key) (hT.image key) u bins t zeta chi W bin
  let N:ℝ:=2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hf : 0 < menuFraction zeta c := by unfold menuFraction; positivity
  have hret' : menuFraction zeta c*((T.image key).card:ℝ) ≤ N*(selected.card:ℝ) := by
    convert hret using 1
  have hfrac : menuFraction zeta c/N*((T.image key).card:ℝ) ≤ (selected.card:ℝ) := by
    have hh : (menuFraction zeta c*((T.image key).card:ℝ))/N ≤ (selected.card:ℝ) :=
      (div_le_iff₀ hN).mpr (by simpa only [mul_comm] using hret')
    convert hh using 1 <;> ring
  have hg := graph_retention T key graph Q HY HG selected hsel
    (menuFraction zeta c/N) (div_nonneg hf.le hN.le) hfrac
  exact ⟨c,selected,hsel,hsn,hret,hg,hwhole⟩

/-- Literal final local-source thickness: d=8rho and w=tau/4096. -/
def localSigma {u bins : ℕ} (c : NativeYCommonScaleSelection.Menu u bins) : ℝ :=
  32768*(((2:ℝ)^c.2.1.val)/((2:ℝ)^c.2.2.1.val))

lemma localSigma_pos {u bins : ℕ} (c : NativeYCommonScaleSelection.Menu u bins) :
    0 < localSigma c := by unfold localSigma; positivity

lemma fraction_eq_localSigma {u bins : ℕ} (zeta : ℝ)
    (c : NativeYCommonScaleSelection.Menu u bins) :
    menuFraction zeta c=(localSigma c/32768)^zeta := by
  unfold menuFraction localSigma
  congr 1
  ring

/-- Fine-pair weights are actual fiber cardinalities of a partition of
the fine graph. Their total is exactly the fine graph cardinality. -/
theorem total_fiber_weight {G P : Type*} [DecidableEq P]
    (graph : Finset G) (parents : Finset P) (cls : G → P)
    (hcls : ∀v∈graph,cls v∈parents) :
    (∑q∈parents,((graph.filter (fun v => cls v=q)).card:ℝ))=(graph.card:ℝ) := by
  have hh := card_eq_sum_card_fiberwise hcls
  exact_mod_cast hh.symm

end NativeWholeYGraphRetention
end -- original anonymous noncomputable section for NativeWholeYGraphRetention

/- Frozen origin: Thm_StickyKakeya4_native_actual_common_Y_graph_mass.lean; SHA256 d99a9140f9bba2f68f582c42f070907fd40dd748f7a70c9527171b2a2e2a0eb2. -/

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
    have heq : N*(menuFraction zeta53 c/N*((T.image graph).card:ℝ))=
        menuFraction zeta53 c*((T.image graph).card:ℝ) := by field_simp
    rw [heq] at hh
    simpa only [mul_assoc] using hh
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
end -- original anonymous noncomputable section for NativeActualCommonYGraphMass

/- Frozen origin: Thm_StickyKakeya4_native_common_Y_total_budget.lean; SHA256 5ccfd1ab1d7dec1a4082144fe8bbddc004d455f2d1210cf545ed7efcb2edd4a5. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeCommonYTotalBudget
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeQuarterScaleParameters NativeWholeYGraphRetention NativeLiteralYHeightAlignment
open NativeOutputAlignmentMenuBudget

lemma fine_mesh_eq (u : ℕ) :
    64/((2^(u+12):ℕ):ℝ)=(2:ℝ)⁻¹^(u+6) := by
  push_cast
  simp only [pow_add,inv_pow]
  norm_num
  field_simp
  norm_num

lemma input_mesh_eq (u : ℕ) :
    (2:ℝ)⁻¹^u/512=(64/((2^(u+12):ℕ):ℝ))/8 := by
  rw [fine_mesh_eq,pow_add]
  norm_num
  ring

/-- The initial physical scale guard suffices; no stronger depth window
is introduced. The same reference has r=deltaOriginal/rho(m). -/
theorem source_thickness_sq_le_original {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (m : ℕ) (p : Parent)
    (hscale : D.thickness ≤ (rho m)^2) :
    (source h R Eref a m p).thickness^2 ≤ D.thickness := by
  have hrho:=rho_pos m
  have hd:=h.1.2.1
  have hid : (source h R Eref a m p).thickness*rho m=D.thickness := by
    rw [source_thickness]
    unfold rho
    field_simp
  apply (mul_le_mul_iff_right₀ (show 0 < (rho m)^2 by positivity)).mp
  have hh:=mul_le_mul_of_nonneg_left hscale hd.le
  have he : (source h R Eref a m p).thickness^2*(rho m)^2=D.thickness^2 := by
    rw [←mul_pow,hid]
  nlinarith only [hh,he]

/-- The actual natural third factor is at least one. This step explicitly
pays the Q^4 appearing in the new graph-retention inequality. -/
lemma radix_cost_from_raw {delta r c3 : ℝ} (F3 Q3 : ℕ)
    (hF3 : 1 ≤ F3) (hr : 0 < r) (hc3 : 0 ≤ c3)
    (hscale : r^2 ≤ delta)
    (H3 : (F3:ℝ)*(Q3:ℝ)^4 ≤ delta^(-c3)) :
    (Q3:ℝ)^4 ≤ r^(-(2*c3)) := by
  have hF : (1:ℝ) ≤ F3 := by exact_mod_cast hF3
  have hQ : (Q3:ℝ)^4 ≤ delta^(-c3) :=
    (le_mul_of_one_le_left (by positivity) hF).trans H3
  have hh:=Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ)<r^2) hscale (neg_nonpos.mpr hc3)
  have he : (r^2)^(-c3)=r^(-(2*c3)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  exact hQ.trans (hh.trans_eq he)

/-- The literal planar gap gives sigma<=32768*(eps/8)^chi. The fixed
32768 is paid after chi and the baseline window are chosen. -/
lemma local_sigma_from_gap {r eps rho tau chi window : ℝ}
    (hr : 0 < r) (heps : 0 < eps) (_hrho : 0 < rho) (_htau : 0 < tau)
    (hchi : 0 < chi)
    (hgap : (eps/8)^(-chi) ≤ tau/rho) (hepsUpper : eps ≤ r^window)
    (hfixed : 32768*r^(window*chi/2) ≤ 1) :
    32768*rho/tau ≤ r^(window*chi/2) := by
  have hh:=one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity : (0:ℝ)<eps/8) _) hgap
  have hratio : rho/tau ≤ (eps/8)^chi := by
    simpa only [one_div_div,Real.rpow_neg (by positivity : (0:ℝ)≤eps/8),one_div,inv_inv,inv_div] using hh
  have hdiv : eps/8 ≤ eps := by linarith only [heps]
  have hpow := (Real.rpow_le_rpow (by positivity : (0:ℝ)≤eps/8) hdiv hchi.le).trans
    (Real.rpow_le_rpow heps.le hepsUpper hchi.le)
  have hdouble : (r^window)^chi = r^(window*chi/2)*r^(window*chi/2) := by
    rw [←Real.rpow_mul hr.le,←Real.rpow_add hr]
    congr 1
    ring
  calc
    32768*rho/tau = 32768*(rho/tau) := by ring
    _ ≤ 32768*((r^window)^chi) := mul_le_mul_of_nonneg_left (hratio.trans hpow) (by norm_num)
    _ = (32768*r^(window*chi/2))*r^(window*chi/2) := by rw [hdouble]; ring
    _ ≤ 1*r^(window*chi/2) := mul_le_mul_of_nonneg_right hfixed (Real.rpow_nonneg hr.le _)
    _ = _ := one_mul _

/-- Genuine pre-source cutoffs pay the actual common menu, the32768 gap
constant, and the fixed graph/Y conversion constant. Both actual fine-scale
guards r<=eps and eps<=r^window remain explicit. -/
theorem exists_total_cutoff (E zeta53 chi window menuTax : ℝ)
    (hE : 0 < E) (hchi : 0 < chi) (hwindow : 0 < window)
    (hmenuTax : 0 < menuTax) (bins : ℕ) :
    ∃r0 : ℝ,0 < r0 ∧ r0 ≤ 1 ∧
      ∀r : ℝ,0 < r → r ≤ r0 →
      32768*r^(window*chi/2) ≤ 1 ∧
      ((5:ℝ)^4*(32768:ℝ)^zeta53/16)*r^((window*chi/2)*(E/8192)) ≤ 1 ∧
      ∀u : ℕ,r ≤ (2:ℝ)⁻¹^(u+6) → (2:ℝ)⁻¹^(u+6) ≤ r^window →
        2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ) ≤ r^(-menuTax) := by
  let a:ℝ:=window*chi/2
  let B:ℝ:=(5:ℝ)^4*(32768:ℝ)^zeta53/16
  have ha : 0 < a := by dsimp [a]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨dm,hdm,_hdm1,Hmenu⟩:=exists_menu_cutoff menuTax hmenuTax bins
  obtain ⟨dw,hdw,hdw1,Hwindow⟩:=exists_small_power_cutoff hwindow hdm
  obtain ⟨dg,hdg,_hdg1,Hgap⟩:=exists_small_power_cutoff ha (by norm_num : (0:ℝ)<1/32768)
  obtain ⟨dc,hdc,_hdc1,Hconstant⟩:=exists_small_power_cutoff
    (show 0 < a*(E/8192) by positivity) (div_pos (by norm_num : (0:ℝ)<1) hB)
  refine ⟨min dw (min dg dc),lt_min hdw (lt_min hdg hdc),(min_le_left _ _).trans hdw1,?_⟩
  intro r hr hsmall
  have hg:=Hgap r hr (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc:=Hconstant r hr (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨by linarith only [hg],?_,?_⟩
  · have hh:=(le_div_iff₀ hB).mp hc
    simpa only [a,B,mul_comm] using hh
  · intro u hLower hUpper
    have hsmallEps:=hUpper.trans (Hwindow r hr (hsmall.trans (min_le_left _ _)))
    have hm:=Hmenu u hsmallEps
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using
      hm.trans (Real.rpow_le_rpow_of_nonpos hr hLower (neg_nonpos.mpr hmenuTax.le))

/-- The actual source graph lower and its raw costs supply htotal. The
only lower input is the conclusion of exists_actual_common_mass, before
any small-power payment; the desired htotal is not a premise. -/
theorem pay_actual_graph_mass {r eps sigma E zeta53 eB c3 menuTax aGap N total : ℝ}
    (Q3 : ℕ) (hr : 0 < r) (hr1 : r ≤ 1) (hrEps : r ≤ eps)
    (hs : 0 < sigma) (hE : 0 < E)
    (hzetaSmall : zeta53 ≤ E/16384) (heB : 0 ≤ eB) (ha : 0 < aGap)
    (htax : 5*eB/16+2*c3+menuTax ≤ aGap*(E/16384))
    (hMenu : N ≤ r^(-menuTax))
    (hQ : (Q3:ℝ)^4 ≤ r^(-(2*c3))) (hSigma : sigma ≤ r^aGap)
    (hfixed : ((5:ℝ)^4*(32768:ℝ)^zeta53/16)*r^(aGap*(E/8192)) ≤ 1)
    (htotal : 0 ≤ total)
    (Hsource : (16/(5:ℝ)^4)*(sigma/32768)^zeta53*eps^(5*eB/16) ≤
      N*(Q3:ℝ)^4*eps^4*total) :
    sigma^(E/4096) ≤ eps^4*total := by
  let tax:ℝ:=5*eB/16+2*c3+menuTax
  let B:ℝ:=(5:ℝ)^4*(32768:ℝ)^zeta53/16
  have hB : 0 < B := by dsimp [B]; positivity
  have hs1 : sigma ≤ 1 := hSigma.trans (by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hr hr1 ha.le)
  have hFixedSigma : B*sigma^(E/8192) ≤ 1 := by
    have hh:=Real.rpow_le_rpow hs.le hSigma (by positivity : 0 ≤ E/8192)
    rw [←Real.rpow_mul hr.le] at hh
    exact (mul_le_mul_of_nonneg_left hh hB.le).trans hfixed
  have hCost : N*(Q3:ℝ)^4 ≤ r^(-(2*c3+menuTax)) := by
    have hh:=mul_le_mul hMenu hQ (by positivity) (by positivity)
    apply hh.trans_eq
    rw [←Real.rpow_add hr]
    congr 1
    ring
  have hBase : (16/(5:ℝ)^4)*(sigma/32768)^zeta53*r^(5*eB/16) ≤
      r^(-(2*c3+menuTax))*(eps^4*total) := by
    calc
      _ ≤ (16/(5:ℝ)^4)*(sigma/32768)^zeta53*eps^(5*eB/16) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hrEps (by positivity)) (by positivity)
      _ ≤ N*(Q3:ℝ)^4*eps^4*total := Hsource
      _ = (N*(Q3:ℝ)^4)*(eps^4*total) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCost (by positivity)
  have hpaid : sigma^zeta53*r^tax ≤ B*(eps^4*total) := by
    have hh:=mul_le_mul_of_nonneg_left hBase
      (show 0 ≤ B*r^(2*c3+menuTax) by positivity)
    have hl : (B*r^(2*c3+menuTax))*
        ((16/(5:ℝ)^4)*(sigma/32768)^zeta53*r^(5*eB/16))=sigma^zeta53*r^tax := by
      rw [Real.div_rpow hs.le (by norm_num)]
      have hp : r^(2*c3+menuTax)*r^(5*eB/16)=r^tax := by
        rw [←Real.rpow_add hr]
        congr 1
        dsimp [tax]
        ring
      calc
        _ = sigma^zeta53*(r^(2*c3+menuTax)*r^(5*eB/16)) := by
          dsimp [B]
          field_simp [(Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<32768) zeta53).ne']
        _ = _ := by rw [hp]
    have hrhs : (B*r^(2*c3+menuTax))*(r^(-(2*c3+menuTax))*(eps^4*total))=B*(eps^4*total) := by
      rw [Real.rpow_neg hr.le]
      field_simp [(Real.rpow_pos_of_pos hr (2*c3+menuTax)).ne']
    rwa [hl,hrhs] at hh
  have hSmallTax : sigma^(E/16384) ≤ r^tax := by
    have hh:=Real.rpow_le_rpow hs.le hSigma (by positivity : 0 ≤ E/16384)
    rw [←Real.rpow_mul hr.le] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_ge hr hr1 htax)
  have hZ : sigma^(E/16384) ≤ sigma^zeta53 :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 hzetaSmall
  have hLow : sigma^(E/8192) ≤ B*(eps^4*total) := by
    have hh:=mul_le_mul hZ hSmallTax (by positivity) (by positivity)
    have he : sigma^(E/16384)*sigma^(E/16384)=sigma^(E/8192) := by
      rw [←Real.rpow_add hs]
      congr 1
      ring
    rw [he] at hh
    exact hh.trans hpaid
  have hSquare : sigma^(E/4096)=sigma^(E/8192)*sigma^(E/8192) := by
    rw [←Real.rpow_add hs]
    congr 1
    ring
  rw [hSquare]
  calc
    _ ≤ (B*(eps^4*total))*sigma^(E/8192) := mul_le_mul_of_nonneg_right hLow (by positivity)
    _ = (B*sigma^(E/8192))*(eps^4*total) := by ring
    _ ≤ 1*(eps^4*total) := mul_le_mul_of_nonneg_right hFixedSigma (by positivity)
    _ = _ := one_mul _

end NativeCommonYTotalBudget
end -- original anonymous noncomputable section for NativeCommonYTotalBudget

/- Frozen origin: Thm_StickyKakeya4_native_actual_Y_total_mass.lean; SHA256 faf8d1a1a3bcf832286edc633274af1276cd0875f3fadd58d822cc8e2d8acd9d. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeActualYTotalMass
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeLocalParentSource NativeMiddleWindowBalance CanonicalConfiguredE4Bridge
open NativeConfiguredIncidenceFibers NativeActualSparseReferenceAdmission NativeActualBaselineGraphMass
open NativeConfiguredThirdRelation NativeJointUniformCoarseRelations NativeWholeYGraphRetention
open NativeLiteralYHeightAlignment NativeAlignmentTauRange SelfUniform
open NativeActualCommonYGraphMass NativeCommonYTotalBudget NativeSameReferenceChartBounds
open scoped BigOperators

/-- Pre-source source entrance for htotal. The same baseline sparse
admission, actual planar witnesses, actual third slots and raw F3*Q3^4
allowance are consumed internally. It constructs the whole-Y fine graph
and proves its normalized total; no desired total/profile is an input.
The old cost/population trace is retained in the baseline admission fields. -/
theorem exists_actual_total_mass (E zeta53 chi window eB c3 menuTax : ℝ)
    (hE : 0 < E) (_hzeta53 : 0 < zeta53) (hzetaSmall : zeta53 ≤ E/16384)
    (hchi : 0 < chi) (hw : 0 < window) (heB : 0 < eB) (hc3 : 0 ≤ c3)
    (hmenuTax : 0 < menuTax)
    (htax : 5*eB/16+2*c3+menuTax ≤ (window*chi/2)*(E/16384)) (bins : ℕ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta)
      (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
      (a zeta : ℝ), 0 ≤ zeta → HasOriginalBackbone D original R a level zeta →
      ∀ (Eref H T : Finset (Fin n × Index)) (m : ℕ), 6 ≤ m → D.thickness ≤ (rho m)^2 →
      ∀ (p : Parent) (etaRef : ℝ)
        (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef),
      T ⊆ Eref → Eref ⊆ incidences original →
      (∀ z ∈ T, z.1 ∈ parentLabels D R a (2 ^ m) p) →
      (source h R Eref a m p).thickness ≤ eps0 → etaRef ≤ window * eB / 256 →
      (64 : ℝ) ^ 3 * (source h R Eref a m p).thickness ^ (window * eB / 16) ≤ D.thickness ^ zeta →
      ∀ population cost : ℝ, 0 < population → 0 < cost →
        population * (parentLabels D R a (2 ^ m) p).card ≤ D.thickness * H.card →
        (H.card : ℝ) ≤ cost * T.card →
      ∀ u : ℕ, m + (u+12) ≤ level →
        64 / ((2 ^ (u+12) : ℕ) : ℝ) ≤ (source h R Eref a m p).thickness ^ window →
        retentionFactor cost population ≤ (64 / ((2 ^ (u+12) : ℕ) : ℝ)) ^ (-(eB / 32)) →
      ∀ (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
        (hd : Module.finrank ℝ P = 1)
        (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ),
      (∀ t u v, |F t u v| ≤ 1 / 4) → (∀ t u v, |Fcfg t u v| ≤ 1 / 4) →
      ∀ (R0 : ℕ), 0 < R0 → rho m ≤ mu m * (R0 : ℝ) →
        mu m * (R0 : ℝ) = 4096 / ((2 ^ (u+12) : ℕ) : ℝ) →
      ∀(d Q F3 : ℕ)
        (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
      1 ≤ F3 → (F3:ℝ)*(Q:ℝ)^4 ≤ D.thickness^(-c3) →
      (∀j x y,x∈T → y∈T →
        degree (fun _ : Fin n × Index => 1)
          (completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra j) T x ≤
        Q^2*degree (fun _ : Fin n × Index => 1)
          (completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra j) T y) →
      let key:=fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2
      let cfg:=NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0
      let graph:=fun z : Fin n × Index => (cfg z.2,outputTube h R Eref a m (u+12) p href z.1)
      ∀t : ℝ,
      ∀(W : ∀height : {height : ℤ // height∈(T.image key).image Prod.fst},
        HeightAlignment (T.image key) u t zeta53 chi height.val)
        (bin : ℝ → Fin (bins+1)),
      ∃c : NativeYCommonScaleSelection.Menu u bins,∃selected : Finset Key,
        selected⊆T.image key ∧ selected.Nonempty ∧
        let eps:=64/((2^(u+12):ℕ):ℝ)
        let Ycut:=T.filter (fun z => key z∈selected)
        0 < localSigma c ∧
        localSigma c ≤ (source h R Eref a m p).thickness^(window*chi/2) ∧
        (localSigma c)^(E/4096) ≤ eps^4*((Ycut.image graph).card:ℝ) ∧
        (∀b : ℕ,b ≤ u+12 →
          (localSigma c)^(E/4096) ≤ eps^4*
            (∑q∈(univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
              (parentLabel (source h R Eref a m p) 0 (2^b)),
                NativeSameQFineGraph.weight h R Eref a m (u+12) b p href cfg Ycut q)) ∧
        ∀height∈selected.image Prod.fst,∃hh : height∈(T.image key).image Prod.fst,
          (W ⟨height,hh⟩).chart=c.1 ∧ (W ⟨height,hh⟩).rhoDepth=c.2.1 ∧
          (W ⟨height,hh⟩).tauDepth=c.2.2.1 ∧ bin (W ⟨height,hh⟩).exponent=c.2.2.2 ∧
          heightPoints selected ((2:ℝ)⁻¹^u/512) height=(W ⟨height,hh⟩).selected := by
  obtain ⟨rCut,hrCut,hrCut1,Hcut⟩:=exists_total_cutoff E zeta53 chi window menuTax hE hchi hw hmenuTax bins
  obtain ⟨baseCut,hbaseCut,Hsource⟩:=exists_actual_common_mass eB window heB hw
  refine ⟨min rCut baseCut,lt_min hrCut hbaseCut,?_⟩
  intro n D eta h original R level a zeta hzeta HB Eref H T m hm hscale p etaRef href
    hTE hEorig hparent hsmall heta hprofile population cost hpop hcost hpopulation hretain
    u hmb hwindow hpaid P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
    d Q F3 extra hF3 H3 Hrel key cfg graph t W bin
  have hsBase:=(hsmall.trans (min_le_right rCut baseCut))
  obtain ⟨c,selected,hsel,hsn,hMass,hwhole⟩:=
    Hsource n D eta h original R level a zeta hzeta HB Eref H T m hm p etaRef href
      hTE hEorig hparent hsBase heta hprofile population cost hpop hcost hpopulation hretain
      u hmb hwindow hpaid P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
      d bins Q extra Hrel t zeta53 chi W bin
  let r:ℝ:=(source h R Eref a m p).thickness
  let eps:ℝ:=64/((2^(u+12):ℕ):ℝ)
  let N:ℝ:=2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ)
  let Ycut:=T.filter (fun z => key z∈selected)
  let deltaY:ℝ:=(2:ℝ)⁻¹^u/512
  have hr : 0 < r:=href.1.2.1
  have hrSmall : r ≤ rCut:=hsmall.trans (min_le_left _ _)
  have hr1 : r ≤ 1:=hrSmall.trans hrCut1
  have heps : 0 < eps:=by dsimp [eps]; positivity
  have hFine:=source_scale_guard (a:=a) h R Eref level m (u+12) p HB.2.1 hmb
  have hrEps : r ≤ eps := by
    have hh : r ≤ 1/((2^(u+12):ℕ):ℝ) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hFine)
    exact hh.trans (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤64) (by positivity))
  have hCut:=Hcut r hr hrSmall
  have hMenu : N ≤ r^(-menuTax) := by
    apply hCut.2.2 u
    · simpa only [eps,fine_mesh_eq] using hrEps
    · simpa only [eps,fine_mesh_eq] using hwindow
  have hQ:=radix_cost_from_raw F3 Q hF3 hr hc3
    (source_thickness_sq_le_original (a:=a) h R Eref m p hscale) H3
  have hsnSaved := hsn
  obtain ⟨z,hz⟩:=hsn
  obtain ⟨hh,_hchart,hRho,hTau,_hbin,_hPoints⟩:=hwhole z.1 (mem_image_of_mem Prod.fst hz)
  let V:=W ⟨z.1,hh⟩
  have hgap:=V.gap
  change V.rhoDepth=c.2.1 at hRho
  change V.tauDepth=c.2.2.1 at hTau
  change deltaY^(-chi) ≤ scale deltaY V.tauDepth.val/scale deltaY V.rhoDepth.val at hgap
  rw [hRho,hTau] at hgap
  have hdelta : deltaY=eps/8:=input_mesh_eq u
  have hSigma : localSigma c ≤ r^(window*chi/2) := by
    have hg:=local_sigma_from_gap hr heps
      (by dsimp [scale,deltaY]; positivity : 0 < scale deltaY c.2.1.val)
      (by dsimp [scale,deltaY]; positivity : 0 < scale deltaY c.2.2.1.val)
      hchi (by rwa [←hdelta]) hwindow hCut.1
    have heq : localSigma c=32768*scale deltaY c.2.1.val/scale deltaY c.2.2.1.val := by
      unfold localSigma
      rw [show 32768*scale deltaY c.2.1.val/scale deltaY c.2.2.1.val=
        32768*(scale deltaY c.2.1.val/scale deltaY c.2.2.1.val) by ring,
        NativeLiteralYHeightAlignment.scale_ratio (by dsimp [deltaY]; positivity) c.2.1.val c.2.2.1.val]
    rwa [←heq] at hg
  have hsigma:=localSigma_pos c
  have hTotal:=pay_actual_graph_mass Q hr hr1 hrEps hsigma hE hzetaSmall heB.le
    (by positivity : 0 < window*chi/2) htax hMenu hQ hSigma hCut.2.1
    (Nat.cast_nonneg ((Ycut.image graph).card)) hMass
  refine ⟨c,selected,hsel,hsnSaved,hsigma,hSigma,hTotal,?_,hwhole⟩
  intro b hb
  have hYP : ∀z∈Ycut,z.1∈parentLabels D R a (2^m) p :=
    fun z hz => hparent z (mem_filter.mp hz).1
  rw [NativeSameQFineGraph.total_weight_eq_graph h R Eref Ycut a m (u+12) b hb p href cfg hYP]
  exact hTotal

end NativeActualYTotalMass
end -- original anonymous noncomputable section for NativeActualYTotalMass

/- Frozen origin: Thm_StickyKakeya4_native_baseline_third_retention_trace.lean; SHA256 4db0eb21b978f27cb0254a369c7212d29989530b5aac045473511e3d3fe169eb. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeBaselineThirdRetentionTrace
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeThirdXYSourceData NativeParentHeightGraphCore NativeRetainedSliceCore

/-- The actual D3 record yields the baseline ORIGINAL-edge retention.
Its full relation dimension and its actual Cpre (including newCutCharge)
are kept. No Y-cut Q^4 has been inserted into this baseline factor. -/
theorem from_third_source {n d J ell : ℕ} (D : FiniteScaleSource n) (zeta a : ℝ) (m : ℕ)
    (plane : Index → Submodule ℝ E4) (E Hp Hgraph S T : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (p : Parent)
    (population PL PU : ℝ) (Qref : ℕ) (lambda G Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (CX : ℝ)
    (Hdata : HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP
      hell hell4 hd Fraw p population PL PU Qref lambda G Cpre threshold L3 Rel CX)
    (Khalf : ℕ) (hgraph : Hp.card ≤ selectionCost Khalf*Hgraph.card) :
    let F3:=refinementCost (d+2) (J+1) L3
    1 ≤ F3 ∧ (Hp.card:ℝ) ≤ ((selectionCost Khalf:ℝ)*Cpre*(F3:ℝ))*(T.card:ℝ) := by
  intro F3
  have hF3 : 0 < F3 := refinementCost_pos (d+2) (J+1) L3
  refine ⟨by omega,?_⟩
  have hg : (Hp.card:ℝ) ≤ (selectionCost Khalf:ℝ)*(Hgraph.card:ℝ) := by exact_mod_cast hgraph
  have ht : (Hgraph.card:ℝ) ≤ Cpre*(F3:ℝ)*(T.card:ℝ) := Hdata.1.2.2.2.2.1
  calc
    _ ≤ (selectionCost Khalf:ℝ)*(Hgraph.card:ℝ) := hg
    _ ≤ (selectionCost Khalf:ℝ)*(Cpre*(F3:ℝ)*(T.card:ℝ)) :=
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
    _ = _ := by ring

end NativeBaselineThirdRetentionTrace
end -- original anonymous noncomputable section for NativeBaselineThirdRetentionTrace

/- Frozen origin: Thm_StickyKakeya4_native_Y_total_parameter_order.lean; SHA256 f64c63810c848c0bff65fddf824449f58f063bdacbb7ccbb5786e8f22bb31979. -/
/- UNVERIFIED source draft. No strict Lean check has run on this file. -/

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace NativeYTotalParameterOrder

/-- The planar retention loss is chosen before the planar gap exponent,
the baseline window, or any native source. -/
theorem exists_planar_loss (E : ℝ) (hE : 0 < E) :
    ∃zeta53 : ℝ,0 < zeta53 ∧ zeta53 ≤ E/16384 := by
  refine ⟨E/32768,by positivity,?_⟩
  linarith only [hE]

/-- Once the actual planar gap chi and baseline window have been chosen,
all three additional taxes can be selected below arbitrary positive source
ceilings. Thus the source budget introduces no circular exponent order. -/
theorem exists_source_taxes (E chi window eCeiling cCeiling menuCeiling : ℝ)
    (hE : 0 < E) (hchi : 0 < chi) (hw : 0 < window)
    (he : 0 < eCeiling) (hc : 0 < cCeiling) (hm : 0 < menuCeiling) :
    ∃eB c3 menuTax : ℝ,
      0 < eB ∧ eB ≤ eCeiling ∧ 0 < c3 ∧ c3 ≤ cCeiling ∧
      0 < menuTax ∧ menuTax ≤ menuCeiling ∧
      5*eB/16+2*c3+menuTax ≤ (window*chi/2)*(E/16384) := by
  let A : ℝ := (window*chi/2)*(E/16384)
  let budget : ℝ := min A (min (4*eCeiling) (min (8*cCeiling) (4*menuCeiling)))
  have hA : 0 < A := by dsimp [A]; positivity
  have hbudget : 0 < budget := by dsimp [budget]; positivity
  have hbA : budget ≤ A := min_le_left _ _
  have hbe : budget ≤ 4*eCeiling :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hbc : budget ≤ 8*cCeiling :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbm : budget ≤ 4*menuCeiling :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨budget/4,budget/8,budget/4,by positivity,?_,by positivity,?_,by positivity,?_,?_⟩
  · linarith only [hbe]
  · linarith only [hbc]
  · linarith only [hbm]
  · change 5*(budget/4)/16+2*(budget/8)+budget/4 ≤ A
    linarith only [hbA,hbudget]

end NativeYTotalParameterOrder
end -- original anonymous noncomputable section for NativeYTotalParameterOrder

/- Frozen origin: Thm_StickyKakeya4_native_actual_baseline_retention_payment.lean; SHA256 ec808efaa1d31686f216cc754d1bfa5adbc6af5132f5bab98fffce69fdd48be1. -/
/- UNVERIFIED source draft. No strict Lean check has run on this file. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeActualBaselineRetentionPayment
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeActualSparseReferenceAdmission NativeRetainedSliceBudgetExtra
open NativeRetainedSliceBudgetAlgebra NativeRetainedSliceBudgetCosts
open NativeReferenceSliceBudgetAlgebra NativeActivePhasePopulation NativeOriginalPrunedMass
open NativeActualNewCutBudget NativeRetentionOutputPower NativeRetainedSliceCore
open NativePaidThirdBudget NativeRankExponentHierarchy

/-- Read the exact pre-third continuation product using its existing
source_total_charge identity. The original quotient occurs once. -/
lemma continuation_cost_readback (q : ℝ) (Kcoh Ksupport normal g R0 Khalf F3 : ℕ)
    (meshConstant row rStop loss rankLoss metric kappa : ℝ) (mesh : Fin Kcoh → ℝ) :
    (NativeParentHeightGraphCore.selectionCost Khalf:ℝ)*
      ((quotientCost q*(coherenceCharge Kcoh normal g meshConstant row rStop
        loss rankLoss metric kappa mesh:ℝ))*
        ((((8*R0)*53^(4*Ksupport))*8^4:ℕ):ℝ))*(F3:ℝ) =
    (NativeParentHeightGraphCore.selectionCost Khalf:ℝ)*quotientCost q*
      (newCutCharge Kcoh Ksupport normal g R0 meshConstant row rStop
        loss rankLoss metric kappa mesh:ℝ)*(F3:ℝ) := by
  simp only [NativeActualNewCutBudget.newCutCharge, Nat.cast_mul]
  ring

/-- This reads the universal raw allowance at the FINAL third-core input
Snext and its full relation dimension d. It never substitutes an older
second-core radix or a smaller relation count. -/
theorem final_third_allowance {n : ℕ} (D : FiniteScaleSource n) (eta : ℝ)
    (h : IsWangZakharovNativeFiniteInput D eta)
    (epsilon eta0 c : ℝ) (g K d J L3 : ℕ) (delta0 : ℝ)
    (Hbudget : HasBudget epsilon eta0 c g K d J L3 delta0)
    (hsmall : D.thickness ≤ delta0) (heta : 0 ≤ eta)
    (hetaSmall : eta ≤ commonBudget eta0 c/32)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (Snext : Finset (Fin n × Index)) (hS : Snext⊆incidences original)
    (hSn : Snext.Nonempty) :
    let F3 := refinementCost (d+2) (J+1) L3
    let Q3 := NativeSourceSizeBounds.radix Snext.card L3
    1 ≤ F3 ∧ 1 ≤ Q3 ∧
      (F3:ℝ)*(Q3:ℝ)^4 ≤ D.thickness^(-(commonBudget eta0 c/4)) := by
  intro F3 Q3
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (refinementCost_pos _ _ _)),?_,?_⟩
  · exact (by norm_num : 1 ≤ (4:ℕ)).trans (NativeSourceSizeBounds.radix_four_le _ _)
  · exact Hbudget.1 n D eta h hsmall heta hetaSmall original horiginal Snext hS hSn

/-- The baseline retention contains only the original graph/quotient/core
cost. The additional Q3 fourth power displayed on the left is retained
explicitly: it is not silently inserted into the baseline Cpre. -/
lemma baseline_factor_identity (delta eta lambda b F1 G F3 Q3 q Ccuts : ℝ)
    (Khalf : ℕ) :
    retentionFactor ((NativeParentHeightGraphCore.selectionCost Khalf:ℝ)*
      quotientCost q*Ccuts*F3) (population delta eta lambda b F1 G)*Q3^4 =
      (64*175616:ℝ)*Ccuts*extraCoefficient delta eta lambda b F1 G F3 Q3 q Khalf := by
  unfold retentionFactor extraCoefficient rowConstant
  simp only [div_div_eq_mul_div]
  ring

/-- The original scalar mass budget, the actual new-cut charge, and the
actual base shape give the baseline admission payment. The cutoff depends
only on fixed parameters and g, before D and before the chosen Snext. -/
theorem exists_actual_retention_cutoff (eB : ℝ) (heB : 0 < eB)
    (Kcoh Ksupport g Khalf : ℕ) (meshConstant row : ℝ)
    (hC : 0 ≤ meshConstant) (hrow : 0 ≤ row) :
    ∃eps0 : ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀(delta eta lambda b tau seed t c2 rStop a rankLoss q epsilonQ
        loss metric epsilonGeom kappa eps : ℝ)
        (F1 F2 G Q1 Q2 F3 Q3 m R0 normal : ℕ) (depths : Fin Kcoh → ℕ),
      0 < delta → delta ≤ 1 → 0 ≤ eta →
      0 < F1 → 0 < G → 1 ≤ Q1 → 1 ≤ Q2 → 1 ≤ Q3 → G ≤ F2 →
      (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)) →
      (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤ delta^(-c2) →
      (F3:ℝ)*(Q3:ℝ)^4 ≤ delta^(-(t/4)) →
      0 ≤ t → tau ≤ t/1024 → seed ≤ tau/16384 → c2=t/4 →
      0 < rStop → rStop ≤ 1 → 0 ≤ rankLoss → rankLoss ≤ 1 →
      rStop ≤ delta^a → t=a*rankLoss →
      lambda=rStop^rankLoss/(4*((g:ℝ)+1)) →
      rStop^(7*rankLoss) ≤ b →
      0 < q → q ≤ 1 → 0 ≤ epsilonQ → epsilonQ ≤ 1 →
      rStop^(epsilonQ/6)/2 ≤ q →
      normal ≤ 4 → 0 ≤ loss → 0 ≤ metric → 0 ≤ epsilonGeom → epsilonGeom ≤ 1/4 →
      metric ≤ rStop^(-2*epsilonGeom) →
      let Rho := (64:ℝ)/((2^m:ℕ):ℝ)
      Rho ≤ 1 → 3072*rStop ≤ Rho^2 → Rho^2 ≤ 6144*rStop →
      ((8*R0:ℕ):ℝ) ≤ 1280*(Rho/64)^(-2*epsilonGeom) →
      0 < eps → eps ≤ eps0 →
      64*eps ≤ 2*max ((5/4:ℝ)*Rho^(1-2*epsilonGeom)) Rho →
      let nu := newExponent Kcoh epsilonGeom loss rankLoss
      nu ≤ 1 → 4*nu+2*(18*rankLoss+4*epsilonQ/3) ≤ eB/64 →
      let Ccuts := (newCutCharge Kcoh Ksupport normal g R0 meshConstant row
        rStop loss rankLoss metric kappa (fun j => 64/((2^(depths j):ℕ):ℝ)):ℝ)
      retentionFactor ((NativeParentHeightGraphCore.selectionCost Khalf:ℝ)*
        quotientCost q*Ccuts*(F3:ℝ)) (population delta eta lambda b F1 G) ≤ eps^(-(eB/32)) := by
  let C : ℝ := (64*175616:ℝ)*fixedFactor Kcoh Ksupport g meshConstant row*extraConstant g Khalf
  have hCpos : 0 < C := by
    have hextra := extraConstant_one_le g Khalf
    have hfixed : 0 < fixedFactor Kcoh Ksupport g meshConstant row := by
      unfold fixedFactor offsetCoefficient
      positivity
    dsimp [C]
    positivity
  obtain ⟨eps0,heps0,heps01,Hpay⟩ := exists_uniform_retention_cutoff eB (6144*C) heB (by positivity)
  refine ⟨eps0,heps0,heps01,?_⟩
  intro delta eta lambda b tau seed t c2 rStop a rankLoss q epsilonQ
    loss metric epsilonGeom kappa eps F1 F2 G Q1 Q2 F3 Q3 m R0 normal depths
    hd hd1 heta hF1 hG hQ1 hQ2 hQ3 hGF H1 H2 H3 ht htau hseed hc2
    hr hr1 hloss hloss1 hrdelta hteq hlambda hb hq hq1 heQ heQ1 hqlow
    hnormal hLoss hmetric heGeom heGeom4 hLip Rho hRho1 hstopLo hstopHi hHeight
    heps hepsSmall hshapeBound nu hnu1 hmargin Ccuts
  have hRho : 0 < Rho := by dsimp [Rho]; positivity
  have hpop : 0 < population delta eta lambda b F1 G := by
    have hlambdaPos : 0 < lambda := by rw [hlambda]; positivity
    have hbPos := (Real.rpow_pos_of_pos hr (7*rankLoss)).trans_le hb
    unfold population
    positivity
  have hquot := quotientCost_pos hq
  have hbase : 0 ≤ retentionFactor
      ((NativeParentHeightGraphCore.selectionCost Khalf:ℝ)*quotientCost q*Ccuts*(F3:ℝ))
      (population delta eta lambda b F1 G) := by
    unfold retentionFactor
    have hvolume := volumeConstant_pos
    have hcuts : 0 ≤ Ccuts := Nat.cast_nonneg _
    positivity
  have hq4 : (1:ℝ) ≤ (Q3:ℝ)^4 := by
    have hh : (1:ℝ) ≤ Q3 := by exact_mod_cast hQ3
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hh 4
  have hfactor := (le_mul_of_one_le_right hbase hq4).trans_eq
    (baseline_factor_identity delta eta lambda b F1 G F3 Q3 q Ccuts Khalf)
  have hExtra := extra_coefficient_bound hd hd1 heta F1 F2 G Q1 Q2 F3 Q3 g 3 Khalf
    hF1 hG hQ1 hQ2 hGF H1 H2 H3 ht htau hseed hc2
    hr hr1 hloss hloss1 (by norm_num) hrdelta hteq hlambda
    (by convert hb using 1 <;> norm_num)
    hRho hRho1 hstopHi hq hq1 heQ heQ1 hqlow
  have hExtra' := (le_max_right 1 _).trans hExtra
  have hCuts := source_new_cut_cost Kcoh Ksupport normal g R0 m hnormal
    meshConstant row rStop loss rankLoss metric epsilonGeom kappa depths
    hC hrow hr hr1 hLoss hloss hmetric heGeom hLip hRho1 hstopLo hHeight
  have hRaw : retentionFactor
      ((NativeParentHeightGraphCore.selectionCost Khalf:ℝ)*quotientCost q*Ccuts*(F3:ℝ))
      (population delta eta lambda b F1 G) ≤
      C*rStop^(-nu)*Rho^(-(18*rankLoss+4*epsilonQ/3))*eps^(-(0:ℝ)) := by
    apply hfactor.trans
    calc
      _ ≤ (64*175616:ℝ)*
          (fixedFactor Kcoh Ksupport g meshConstant row*rStop^(-nu))*
          (extraConstant g Khalf*Rho^(-(18*rankLoss+4*epsilonQ/3))) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hCuts (by norm_num)
            · exact hExtra'
            · unfold extraCoefficient
              have hrowPos := rowConstant_pos
              positivity
            · unfold fixedFactor offsetCoefficient
              positivity
      _ = _ := by simp only [neg_zero,Real.rpow_zero,mul_one]; dsimp [C]; ring
  have hshape := configured_square_le_reference hRho hRho1 heps.le heGeom heGeom4 hshapeBound
  have hbound := total_retention_at_output hCpos.le heps hRho.le
    (show 0 ≤ nu by dsimp [nu,newExponent]; positivity) hnu1
    (show 0 ≤ 18*rankLoss+4*epsilonQ/3 by positivity) hshape hstopHi hRaw
  simp only [add_zero] at hbound
  exact Hpay eps _ _ heps hepsSmall hmargin hbound

end NativeActualBaselineRetentionPayment
end -- original anonymous noncomputable section for NativeActualBaselineRetentionPayment

/- Frozen origin: Thm_StickyKakeya4_native_Y_total_epsilon_budget.lean; SHA256 de50faad4fad27fcd6d713454325bc08627824c26a316c3e8ab05e79cda86689. -/
/- UNVERIFIED source draft. No strict Lean check has run on this file. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeYTotalEpsilonBudget
open NativeCommonYTotalBudget NativeQuarterScaleParameters NativeOutputAlignmentMenuBudget

/-- Keep the baseline power at eps. Using eps<=r^window converts only the
independent raw third allowance, not eB, to this scale. -/
lemma radix_cost_at_epsilon {r eps window c3 : ℝ} (Q3 : ℕ)
    (hr : 0 < r) (heps : 0 < eps) (hw : 0 < window) (hc3 : 0 ≤ c3)
    (hwindow : eps ≤ r^window) (hQ : (Q3:ℝ)^4 ≤ r^(-(2*c3))) :
    (Q3:ℝ)^4 ≤ eps^(-(2*c3/window)) := by
  have hh := Real.rpow_le_rpow_of_nonpos heps hwindow
    (show -(2*c3/window) ≤ 0 from neg_nonpos.mpr (by positivity))
  have he : (r^window)^(-(2*c3/window))=r^(-(2*c3)) := by
    rw [←Real.rpow_mul hr.le]
    congr 1
    field_simp [hw.ne']
  rw [he] at hh
  exact hQ.trans hh

/-- All constants and the actual polynomial common-scale menu are paid
at eps, before the native source. No rank window is spent on eB. -/
theorem exists_epsilon_cutoff (E zeta53 chi menuTax : ℝ)
    (hE : 0 < E) (hchi : 0 < chi) (hmenuTax : 0 < menuTax) (bins : ℕ) :
    ∃eps0 : ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀eps : ℝ,0 < eps → eps ≤ eps0 →
        32768*eps^(chi/2) ≤ 1 ∧
        ((5:ℝ)^4*(32768:ℝ)^zeta53/16)*eps^((chi/2)*(E/8192)) ≤ 1 ∧
        ∀u : ℕ,eps=(2:ℝ)⁻¹^(u+6) →
          2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ) ≤ eps^(-menuTax) := by
  let B : ℝ := (5:ℝ)^4*(32768:ℝ)^zeta53/16
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨dm,hdm,hdm1,Hmenu⟩ := exists_menu_cutoff menuTax hmenuTax bins
  obtain ⟨dg,hdg,_hdg1,Hgap⟩ := exists_small_power_cutoff
    (show 0 < chi/2 by positivity) (by norm_num : (0:ℝ)<1/32768)
  obtain ⟨dc,hdc,_hdc1,Hconstant⟩ := exists_small_power_cutoff
    (show 0 < (chi/2)*(E/8192) by positivity) (div_pos (by norm_num : (0:ℝ)<1) hB)
  refine ⟨min dm (min dg dc),lt_min hdm (lt_min hdg hdc),(min_le_left _ _).trans hdm1,?_⟩
  intro eps heps hsmall
  have hg := Hgap eps heps (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc := Hconstant eps heps (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨by linarith only [hg],?_,?_⟩
  · have hh := (le_div_iff₀ hB).mp hc
    simpa only [mul_comm] using hh
  · intro u heq
    subst eps
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using Hmenu u (hsmall.trans (min_le_left _ _))

/-- The actual common graph lower pays htotal using only eps exponents.
This removes the artificial requirement eB << c^3 that would result from
first weakening eps^(5eB/16) to r^(5eB/16). -/
theorem pay_actual_graph_mass_at_epsilon
    {eps sigma E zeta53 eB c3 window menuTax N total : ℝ}
    (Q3 : ℕ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hs : 0 < sigma) (hE : 0 < E) (hzeta : zeta53 ≤ E/16384)
    (heB : 0 ≤ eB) (hchi : ℝ) (hchiPos : 0 < hchi)
    (htax : 5*eB/16+2*c3/window+menuTax ≤ (hchi/2)*(E/16384))
    (hMenu : N ≤ eps^(-menuTax)) (hQ : (Q3:ℝ)^4 ≤ eps^(-(2*c3/window)))
    (hSigma : sigma ≤ eps^(hchi/2))
    (hfixed : ((5:ℝ)^4*(32768:ℝ)^zeta53/16)*eps^((hchi/2)*(E/8192)) ≤ 1)
    (htotal : 0 ≤ total)
    (Hsource : (16/(5:ℝ)^4)*(sigma/32768)^zeta53*eps^(5*eB/16) ≤
      N*(Q3:ℝ)^4*eps^4*total) :
    sigma^(E/4096) ≤ eps^4*total := by
  have htax' : 5*eB/16+2*(c3/window)+menuTax ≤ (hchi/2)*(E/16384) := by
    convert htax using 1
    ring
  have hQ' : (Q3:ℝ)^4 ≤ eps^(-(2*(c3/window))) := by
    convert hQ using 1
    ring
  exact pay_actual_graph_mass Q3 heps heps1 le_rfl hs hE hzeta heB
    (by positivity : 0 < hchi/2) htax' hMenu hQ' hSigma hfixed htotal Hsource

/-- For the actual hierarchy, the only divided third tax is independent
of c. The baseline window here is the conservative amin/8=c^3/64. -/
lemma actual_third_tax (eta0 c : ℝ) (hc : 0 < c) :
    2*(NativeRankExponentHierarchy.commonBudget eta0 c/4)/(c^3/64)=4*eta0 := by
  unfold NativeRankExponentHierarchy.commonBudget
  field_simp [hc.ne']
  ring

end NativeYTotalEpsilonBudget
end -- original anonymous noncomputable section for NativeYTotalEpsilonBudget

/- Frozen origin: Thm_StickyKakeya4_native_actual_Y_epsilon_total_mass.lean; SHA256 c8ca1f2d15f23c856298ba3012d02846be469c000d8112654f7252ded65fd51b. -/
/- UNVERIFIED sharper source draft. No strict Lean check has run. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeActualYEpsilonTotalMass
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeLocalParentSource NativeMiddleWindowBalance CanonicalConfiguredE4Bridge
open NativeConfiguredIncidenceFibers NativeActualSparseReferenceAdmission NativeActualBaselineGraphMass
open NativeConfiguredThirdRelation NativeJointUniformCoarseRelations NativeWholeYGraphRetention
open NativeLiteralYHeightAlignment NativeAlignmentTauRange SelfUniform
open NativeActualCommonYGraphMass NativeCommonYTotalBudget NativeSameReferenceChartBounds
open NativeYTotalEpsilonBudget
open scoped BigOperators

/-- Pre-source source entrance for htotal. The same baseline sparse
admission, actual planar witnesses, actual third slots and raw F3*Q3^4
allowance are consumed internally. It constructs the whole-Y fine graph
and proves its normalized total; no desired total/profile is an input.
The old cost/population trace is retained in the baseline admission fields. -/
theorem exists_actual_total_mass (E zeta53 chi window eB c3 menuTax : ℝ)
    (hE : 0 < E) (_hzeta53 : 0 < zeta53) (hzetaSmall : zeta53 ≤ E/16384)
    (hchi : 0 < chi) (hw : 0 < window) (heB : 0 < eB) (hc3 : 0 ≤ c3)
    (hmenuTax : 0 < menuTax)
    (htax : 5*eB/16+2*c3/window+menuTax ≤ (chi/2)*(E/16384)) (bins : ℕ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta)
      (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
      (a zeta : ℝ), 0 ≤ zeta → HasOriginalBackbone D original R a level zeta →
      ∀ (Eref H T : Finset (Fin n × Index)) (m : ℕ), 6 ≤ m → D.thickness ≤ (rho m)^2 →
      ∀ (p : Parent) (etaRef : ℝ)
        (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef),
      T ⊆ Eref → Eref ⊆ incidences original →
      (∀ z ∈ T, z.1 ∈ parentLabels D R a (2 ^ m) p) →
      (source h R Eref a m p).thickness ≤ eps0 → etaRef ≤ window * eB / 256 →
      (64 : ℝ) ^ 3 * (source h R Eref a m p).thickness ^ (window * eB / 16) ≤ D.thickness ^ zeta →
      ∀ population cost : ℝ, 0 < population → 0 < cost →
        population * (parentLabels D R a (2 ^ m) p).card ≤ D.thickness * H.card →
        (H.card : ℝ) ≤ cost * T.card →
      ∀ u : ℕ, m + (u+12) ≤ level →
        64 / ((2 ^ (u+12) : ℕ) : ℝ) ≤ (source h R Eref a m p).thickness ^ window →
        retentionFactor cost population ≤ (64 / ((2 ^ (u+12) : ℕ) : ℝ)) ^ (-(eB / 32)) →
      ∀ (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
        (hd : Module.finrank ℝ P = 1)
        (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ),
      (∀ t u v, |F t u v| ≤ 1 / 4) → (∀ t u v, |Fcfg t u v| ≤ 1 / 4) →
      ∀ (R0 : ℕ), 0 < R0 → rho m ≤ mu m * (R0 : ℝ) →
        mu m * (R0 : ℝ) = 4096 / ((2 ^ (u+12) : ℕ) : ℝ) →
      ∀(d Q F3 : ℕ)
        (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
      1 ≤ F3 → (F3:ℝ)*(Q:ℝ)^4 ≤ D.thickness^(-c3) →
      (∀j x y,x∈T → y∈T →
        degree (fun _ : Fin n × Index => 1)
          (completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra j) T x ≤
        Q^2*degree (fun _ : Fin n × Index => 1)
          (completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra j) T y) →
      let key:=fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2
      let cfg:=NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0
      let graph:=fun z : Fin n × Index => (cfg z.2,outputTube h R Eref a m (u+12) p href z.1)
      ∀t : ℝ,
      ∀(W : ∀height : {height : ℤ // height∈(T.image key).image Prod.fst},
        HeightAlignment (T.image key) u t zeta53 chi height.val)
        (bin : ℝ → Fin (bins+1)),
      ∃c : NativeYCommonScaleSelection.Menu u bins,∃selected : Finset Key,
        selected⊆T.image key ∧ selected.Nonempty ∧
        let eps:=64/((2^(u+12):ℕ):ℝ)
        let Ycut:=T.filter (fun z => key z∈selected)
        0 < localSigma c ∧
        localSigma c ≤ (source h R Eref a m p).thickness^(window*chi/2) ∧
        (localSigma c)^(E/4096) ≤ eps^4*((Ycut.image graph).card:ℝ) ∧
        (∀b : ℕ,b ≤ u+12 →
          (localSigma c)^(E/4096) ≤ eps^4*
            (∑q∈(univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
              (parentLabel (source h R Eref a m p) 0 (2^b)),
                NativeSameQFineGraph.weight h R Eref a m (u+12) b p href cfg Ycut q)) ∧
        ∀height∈selected.image Prod.fst,∃hh : height∈(T.image key).image Prod.fst,
          (W ⟨height,hh⟩).chart=c.1 ∧ (W ⟨height,hh⟩).rhoDepth=c.2.1 ∧
          (W ⟨height,hh⟩).tauDepth=c.2.2.1 ∧ bin (W ⟨height,hh⟩).exponent=c.2.2.2 ∧
          heightPoints selected ((2:ℝ)⁻¹^u/512) height=(W ⟨height,hh⟩).selected := by
  obtain ⟨epsCut,hepsCut,hepsCut1,Hcut⟩:=exists_epsilon_cutoff E zeta53 chi menuTax hE hchi hmenuTax bins
  obtain ⟨rCut,hrCut,_hrCut1,Hpull⟩:=NativeQuarterScaleParameters.exists_small_power_cutoff hw hepsCut
  obtain ⟨baseCut,hbaseCut,Hsource⟩:=exists_actual_common_mass eB window heB hw
  refine ⟨min rCut baseCut,lt_min hrCut hbaseCut,?_⟩
  intro n D eta h original R level a zeta hzeta HB Eref H T m hm hscale p etaRef href
    hTE hEorig hparent hsmall heta hprofile population cost hpop hcost hpopulation hretain
    u hmb hwindow hpaid P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
    d Q F3 extra hF3 H3 Hrel key cfg graph t W bin
  have hsBase:=(hsmall.trans (min_le_right rCut baseCut))
  obtain ⟨c,selected,hsel,hsn,hMass,hwhole⟩:=
    Hsource n D eta h original R level a zeta hzeta HB Eref H T m hm p etaRef href
      hTE hEorig hparent hsBase heta hprofile population cost hpop hcost hpopulation hretain
      u hmb hwindow hpaid P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
      d bins Q extra Hrel t zeta53 chi W bin
  let r:ℝ:=(source h R Eref a m p).thickness
  let eps:ℝ:=64/((2^(u+12):ℕ):ℝ)
  let N:ℝ:=2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ)
  let Ycut:=T.filter (fun z => key z∈selected)
  let deltaY:ℝ:=(2:ℝ)⁻¹^u/512
  have hr : 0 < r:=href.1.2.1
  have hrSmall : r ≤ rCut:=hsmall.trans (min_le_left _ _)
  have heps : 0 < eps:=by dsimp [eps]; positivity
  have hepsSmall : eps ≤ epsCut:=hwindow.trans (Hpull r hr hrSmall)
  have heps1 : eps ≤ 1:=hepsSmall.trans hepsCut1
  have hCut:=Hcut eps heps hepsSmall
  have hMenu : N ≤ eps^(-menuTax) := hCut.2.2 u (fine_mesh_eq u)
  have hQr:=radix_cost_from_raw F3 Q hF3 hr hc3
    (source_thickness_sq_le_original (a:=a) h R Eref m p hscale) H3
  have hQ:=radix_cost_at_epsilon Q hr heps hw hc3 hwindow hQr
  have hsnSaved := hsn
  obtain ⟨z,hz⟩:=hsn
  obtain ⟨hh,_hchart,hRho,hTau,_hbin,_hPoints⟩:=hwhole z.1 (mem_image_of_mem Prod.fst hz)
  let V:=W ⟨z.1,hh⟩
  have hgap:=V.gap
  change V.rhoDepth=c.2.1 at hRho
  change V.tauDepth=c.2.2.1 at hTau
  change deltaY^(-chi) ≤ scale deltaY V.tauDepth.val/scale deltaY V.rhoDepth.val at hgap
  rw [hRho,hTau] at hgap
  have hdelta : deltaY=eps/8:=input_mesh_eq u
  have hSigmaEps : localSigma c ≤ eps^(chi/2) := by
    have hg:=local_sigma_from_gap (r:=eps) (window:=1) heps heps
      (by dsimp [scale,deltaY]; positivity : 0 < scale deltaY c.2.1.val)
      (by dsimp [scale,deltaY]; positivity : 0 < scale deltaY c.2.2.1.val)
      hchi (by rwa [←hdelta]) (by rw [Real.rpow_one])
      (by simpa only [one_mul] using hCut.1)
    have heq : localSigma c=32768*scale deltaY c.2.1.val/scale deltaY c.2.2.1.val := by
      unfold localSigma
      rw [show 32768*scale deltaY c.2.1.val/scale deltaY c.2.2.1.val=
        32768*(scale deltaY c.2.1.val/scale deltaY c.2.2.1.val) by ring,
        NativeLiteralYHeightAlignment.scale_ratio (by dsimp [deltaY]; positivity) c.2.1.val c.2.2.1.val]
    simpa only [←heq,one_mul] using hg
  have hSigma : localSigma c ≤ r^(window*chi/2) := by
    have hh:=Real.rpow_le_rpow heps.le hwindow (show 0 ≤ chi/2 by positivity)
    rw [←Real.rpow_mul hr.le] at hh
    have he : window*(chi/2)=window*chi/2 := by ring
    simpa only [he] using hSigmaEps.trans hh
  have hsigma:=localSigma_pos c
  have hTotal:=pay_actual_graph_mass_at_epsilon Q heps heps1 hsigma hE hzetaSmall heB.le
    chi hchi htax hMenu hQ hSigmaEps hCut.2.1
    (Nat.cast_nonneg ((Ycut.image graph).card)) hMass
  refine ⟨c,selected,hsel,hsnSaved,hsigma,hSigma,hTotal,?_,hwhole⟩
  intro b hb
  have hYP : ∀z∈Ycut,z.1∈parentLabels D R a (2^m) p :=
    fun z hz => hparent z (mem_filter.mp hz).1
  rw [NativeSameQFineGraph.total_weight_eq_graph h R Eref Ycut a m (u+12) b hb p href cfg hYP]
  exact hTotal

end NativeActualYEpsilonTotalMass
end -- original anonymous noncomputable section for NativeActualYEpsilonTotalMass

/- Frozen origin: Thm_StickyKakeya4_native_reference_admission_invariance.lean; SHA256 ef3a3ff6576df28ce3c3693b00c22d6039d77dae9c9bdc842cdc297fc13e12b9. -/
/- UNVERIFIED source draft. No strict Lean check has run on this file. -/

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace NativeReferenceAdmissionInvariance
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeConfiguredIncidenceFibers
open NativeOriginalParentDensityCore

/-- The parent restriction removes no original cells of any label in
the full R-parent. This is equality of the literal cell families. -/
theorem sourceCells_parent_eq {n : ℕ} (D : FiniteScaleSource n)
    (R : Finset (Fin n)) (Eref : Finset (Fin n × Index))
    (a : ℝ) (N : ℕ) (p : Parent) :
    sourceCells D R (parentEdges D a N Eref p) a N p = sourceCells D R Eref a N p := by
  funext i
  have hi := (mem_parentLabels D R a N p _).mp
    (NativePaddedCellSource.originalLabel_mem (parentLabels D R a N p) i)
  change outputCells D (parentEdges D a N Eref p) a N p _=outputCells D Eref a N p _
  ext k
  rw [mem_outputCells,mem_outputCells]
  simp only [parentEdges,mem_filter,hi.2,and_true]

/-- The engine's parent-filtered presentation and the consumer's full-E1
presentation are the identical FiniteScaleSource, including the shading. -/
theorem source_parent_eq {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent) :
    source h R (parentEdges D a (2^m) Eref p) a m p=source h R Eref a m p := by
  unfold source
  rw [sourceCells_parent_eq]

/-- The representative depends on the source and reference labels; the
native accuracy proof enters only the proof of a valid fallback index. -/
theorem representative_eq {n : ℕ} {D : FiniteScaleSource n} {etaA etaB : ℝ}
    (hA : IsWangZakharovNativeFiniteInput D etaA)
    (hB : IsWangZakharovNativeFiniteInput D etaB)
    (R : Finset (Fin n)) (a : ℝ) (N : ℕ) (p : Parent) :
    NativeCoarseDirectionThinning.representative hA R a N p =
      NativeCoarseDirectionThinning.representative hB R a N p := by
  rfl

/-- Re-admitting the SAME source does not alter any fullSource field,
including its literal representative lines and its original cell shading. -/
theorem fullSource_eq {n : ℕ} {D : FiniteScaleSource n} {etaA etaB : ℝ}
    (hA : IsWangZakharovNativeFiniteInput D etaA)
    (hB : IsWangZakharovNativeFiniteInput D etaB)
    (R : Finset (Fin n)) (a : ℝ) (level b : ℕ) (E : Finset (Fin n × Index)) :
    NativeFullCoarseShadow.fullSource hA R a level b E =
      NativeFullCoarseShadow.fullSource hB R a level b E := by
  rfl

/-- Both admission proofs below have exactly source(h,R,Eref,a,m,p) as
their datum. Eref is unchanged, rather than replaced by a new shading. -/
theorem outputTube_eq {n : ℕ} {D : FiniteScaleSource n} {eta etaA etaB : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (a : ℝ) (m b : ℕ) (p : Parent)
    (hA : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaA)
    (hB : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaB) (i : Fin n) :
    outputTube h R Eref a m b p hA i=outputTube h R Eref a m b p hB i := by
  rfl

/-- The deduplicated configured fine graph is literally unchanged by
the prescribed-accuracy admission proof, even before taking its cardinal. -/
theorem fine_graph_eq {n : ℕ} {D : FiniteScaleSource n} {eta etaA etaB : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (m b : ℕ) (p : Parent)
    (hA : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaA)
    (hB : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaB)
    (configured : Index → E4) :
    T.image (fun z => (configured z.2,outputTube h R Eref a m b p hA z.1)) =
      T.image (fun z => (configured z.2,outputTube h R Eref a m b p hB z.1)) := by
  rfl

end NativeReferenceAdmissionInvariance
end -- original anonymous noncomputable section for NativeReferenceAdmissionInvariance

/- Frozen origin: Thm_StickyKakeya4_native_prescribed_reference_admission.lean; SHA256 e58153f2789cde8459857b0c1a31943dc4645b38c48e9b860781e19704689255. -/
/- UNVERIFIED source draft. No strict Lean check has run on this file. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
noncomputable section
namespace NativePrescribedReferenceAdmission
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeLocalParentSource NativeMiddleWindowBalance
open NativeReferenceParentPopulation NativeReferenceParentAdmissionBudget
open NativeNormalizedCellSourceUpper NativeActualRelativeCoarseAdmission
open NativeReferenceAdmissionInvariance

/-- Native accuracy and the original-label population accuracy can both
be prescribed before tau/seed, below the final effective pruning threshold. -/
theorem exists_accuracy (zMin window eB : ℝ)
    (hz : 0 < zMin) (hw : 0 < window) (heB : 0 < eB) :
    ∃etaNative profileExp : ℝ,
      0 < etaNative ∧ etaNative ≤ zMin ∧ etaNative ≤ window*eB/256 ∧
      0 < profileExp ∧ profileExp ≤ zMin ∧ profileExp ≤ window*eB/16 := by
  refine ⟨min zMin (window*eB/256),min zMin (window*eB/16),
    lt_min hz (by positivity),min_le_left _ _,min_le_right _ _,
    lt_min hz (by positivity),min_le_left _ _,min_le_right _ _⟩

/-- Re-admit the SAME E1 parent with a prescribed accuracy. The first
core's actual enlarged factor F, its original parent equality, and H1 are
used internally. This changes no source datum, reference family, shading,
or representative; it does not rely on the opaque accuracy returned by
the earlier angular engine. The seed and cutoff restrictions precede D. -/
theorem exists_prescribed_parent_admission (etaNative profileExp sigma0 : ℝ)
    (hetaNative : 0 < etaNative) (hprofile : 0 < profileExp) (hsigma0 : 0 < sigma0) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/8 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
      0 ≤ zeta → eta ≤ seed/8 → zeta ≤ seed/256 →
      seed ≤ etaNative → seed ≤ profileExp → D.thickness ≤ delta0 →
      ∀(original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ),
      HasOriginalBackbone D original R a level zeta →
      ∀E1 : Finset (Fin n × Index),E1⊆retained original R →
      ∀F Q m : ℕ,m ≤ level → D.thickness ≤ (64/((2^m:ℕ):ℝ))^2 →
      (incidences original).card ≤ F*E1.card →
      (∀x y,x∈E1 → y∈E1 →
        (parentEdges D a (2^m) E1 (parentLabel D a (2^m) x.1)).card ≤
          Q^2*(parentEdges D a (2^m) E1 (parentLabel D a (2^m) y.1)).card) →
      (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)) →
      ∀p : Parent,(parentEdges D a (2^m) E1 p).Nonempty →
      let E := parentEdges D a (2^m) E1 p
      IsWangZakharovNativeFiniteInput (source h R E a m p) etaNative ∧
      (∀i,(source h R E a m p).line i∈fixedCompactClass) ∧
      (source h R E a m p).thickness ≤ sigma0 ∧
      (64:ℝ)^3*(source h R E a m p).thickness^profileExp ≤ D.thickness^zeta ∧
      OriginalPopulationLaw (source h R E a m p) univ 0 profileExp (level-m+6) ∧
      IsWangZakharovNativeFiniteInput (source h R E1 a m p) etaNative ∧
      OriginalPopulationLaw (source h R E1 a m p) univ 0 profileExp (level-m+6) := by
  obtain ⟨delta0,hd0,hd01,Hbudget⟩ :=
    exists_first_stage_admission_cutoff etaNative profileExp sigma0 hetaNative hprofile hsigma0
  refine ⟨delta0,hd0,hd01,?_⟩
  intro n D eta zeta seed a h hzeta heta hzseed hseedNative hseedProfile hsmall
    original R level HB E1 hE1 F Q m hm hsquare hret Hparent Hcost p hp E
  have hE : E⊆incidences original :=
    (filter_subset _ _).trans (hE1.trans (filter_subset _ _))
  have hlabels : ∀z∈E,z.1∈parentLabels D R a (2^m) p := by
    intro z hz
    obtain ⟨hzE,hzp⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨(mem_filter.mp (hE1 hzE)).2,hzp⟩
  have hParent : (parentLabels D R a (2^m) p).Nonempty :=
    ⟨hp.choose.1,hlabels hp.choose hp.choose_spec⟩
  have hpop := reference_parent_population h original R level HB (hsmall.trans hd01)
    E1 hE1 F Q m hm hret Hparent Hcost p hp
  have hDelta : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  obtain ⟨hSigma,had,hcw,hden,hprof⟩ := Hbudget D.thickness (64/((2^m:ℕ):ℝ))
    eta zeta seed h.1.2.1 hsmall hDelta hsquare heta hzseed hseedNative hseedProfile
  have hthick : (source h R E a m p).thickness=D.thickness/(64/((2^m:ℕ):ℝ)) := by
    rw [source_thickness]
    field_simp
  rw [←hthick] at hSigma had hcw hden hprof
  obtain ⟨hNative,hcompact⟩ := source_native_from_population h hzeta original R level HB
    m hm p E hE hlabels hParent (D.thickness^(seed/8+2*zeta))
    (Real.rpow_pos_of_pos h.1.2.1 _) hpop had hcw hden
  have hLaw := source_population_law h R E a zeta profileExp hzeta level HB.2.1
    HB.2.2.2.2.2.2.2.2 m hm p hNative hprof
  have hEq : source h R E a m p=source h R E1 a m p := source_parent_eq h R E1 a m p
  exact ⟨hNative,hcompact,hSigma,hprof,hLaw,hEq ▸ hNative,hEq ▸ hLaw⟩

end NativePrescribedReferenceAdmission
end -- original anonymous noncomputable section for NativePrescribedReferenceAdmission

/- Frozen origin: Thm_StickyKakeya4_native_Y_source_parameter_ledger.lean; SHA256 43efd4a7c954e2fb82fb4d316924bca21be007d786b65a7318a261206a2244b7. -/
/- UNVERIFIED source draft. No strict Lean check has run on this file. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeYSourceParameterLedger
open NativeActualNewCutBudget NativeRankExponentHierarchy NativeYTotalEpsilonBudget

/-- This choice follows chi and precedes c. In particular eB does not
depend on the later c^3 baseline window. -/
def baselineAccuracy (E chi : ℝ) : ℝ := min 1 (chi*E/65536)

/-- K is the fixed number of coherence rounds, not the source-dependent g. -/
def smallTax (eB : ℝ) (K : ℕ) : ℝ := eB/(8192*((K:ℝ)+1))

theorem baseline_accuracy_bounds {E chi : ℝ} (hE : 0 < E) (hchi : 0 < chi) :
    0 < baselineAccuracy E chi ∧ baselineAccuracy E chi ≤ 1 ∧
      baselineAccuracy E chi ≤ chi*E/65536 :=
  ⟨lt_min (by norm_num) (by positivity),min_le_left _ _,min_le_right _ _⟩

/-- All actual geometry/quotient/rank exponents can be kept below one
positive ceiling chosen after eB. The source's nu then pays the baseline
retention using the exact exponent from its actual newCutCharge. -/
theorem geometry_tax_bound {eB epsilonGeom loss rankLoss epsilonQ : ℝ} (K : ℕ)
    (heB : 0 < eB) (heB1 : eB ≤ 1)
    (_heGeom : 0 ≤ epsilonGeom) (_hLoss : 0 ≤ loss) (_hRank : 0 ≤ rankLoss) (_hQ : 0 ≤ epsilonQ)
    (heGeomSmall : epsilonGeom ≤ smallTax eB K) (hLossSmall : loss ≤ smallTax eB K)
    (hRankSmall : rankLoss ≤ smallTax eB K) (hQSmall : epsilonQ ≤ smallTax eB K) :
    newExponent K epsilonGeom loss rankLoss ≤ 1 ∧
      4*newExponent K epsilonGeom loss rankLoss+2*(18*rankLoss+4*epsilonQ/3) ≤ eB/64 := by
  let B := smallTax eB K
  have hB : 0 < B := by dsimp [B,smallTax]; positivity
  have hK : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hEq : ((K:ℝ)+1)*B=eB/8192 := by
    dsimp [B,smallTax]
    field_simp [show (K:ℝ)+1 ≠ 0 by positivity]
  have hnu : newExponent K epsilonGeom loss rankLoss ≤ 14*((K:ℝ)+1)*B := by
    unfold newExponent
    calc
      _ ≤ (4*(K:ℝ)+2)*B+(K:ℝ)*(B+9*B) := by gcongr
      _ ≤ _ := by nlinarith only [hB,hK]
  have hA : 18*rankLoss+4*epsilonQ/3 ≤ 20*B := by
    calc
      _ ≤ 18*B+4*B/3 := by gcongr
      _ ≤ _ := by linarith only [hB]
  constructor
  · calc
      _ ≤ 14*(((K:ℝ)+1)*B) := by simpa only [mul_assoc] using hnu
      _ = 14*(eB/8192) := by rw [hEq]
      _ ≤ 1 := by linarith only [heB1]
  · have hh : 4*newExponent K epsilonGeom loss rankLoss+2*(18*rankLoss+4*epsilonQ/3) ≤
        96*(((K:ℝ)+1)*B) := by nlinarith only [hnu,hA,hB,hK]
    rw [hEq] at hh
    linarith only [hh,heB]

/-- At the actual window=c^3/64 and third allowance commonBudget/4,
the eps-scale mass tax needs rankEta0 small independently of c. This is
the RANK hierarchy parameter, not Lemma 5.3's returned AD threshold.
Any further c-dependent ceiling, including c^6, may be imposed afterward. -/
theorem actual_total_tax {E chi rankEta0 c : ℝ} (K : ℕ)
    (hE : 0 < E) (hchi : 0 < chi) (hc : 0 < c)
    (_heta0 : 0 ≤ rankEta0)
    (hetaSmall : rankEta0 ≤ smallTax (baselineAccuracy E chi) K) :
    5*baselineAccuracy E chi/16+
      2*(commonBudget rankEta0 c/4)/(c^3/64)+baselineAccuracy E chi/16 ≤
      (chi/2)*(E/16384) := by
  rw [actual_third_tax rankEta0 c hc]
  obtain ⟨heB,_heB1,heBsmall⟩ := baseline_accuracy_bounds hE hchi
  have hB : smallTax (baselineAccuracy E chi) K ≤ baselineAccuracy E chi/8192 := by
    unfold smallTax
    apply div_le_div_of_nonneg_left heB.le (by norm_num : (0:ℝ)<8192)
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg _
    nlinarith only [hK]
  have heta := hetaSmall.trans hB
  nlinarith only [heBsmall,heta,heB]

end NativeYSourceParameterLedger
end -- original anonymous noncomputable section for NativeYSourceParameterLedger
