import Theorems.Thm_StickyKakeya4_native_configured_Y_weighted_retention
import Theorems.Thm_StickyKakeya4_native_retained_slice_count_transfer
import Theorems.Thm_StickyKakeya4_native_literal_Y_height_alignment

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
    convert hh using 1 <;> ring
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
  have hfrac : menuFraction zeta c/N*((T.image key).card:ℝ) ≤ (selected.card:ℝ) := by
    have hh : (menuFraction zeta c*((T.image key).card:ℝ))/N ≤ (selected.card:ℝ) :=
      (div_le_iff₀ hN).mpr (by simpa only [mul_comm] using hret)
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
