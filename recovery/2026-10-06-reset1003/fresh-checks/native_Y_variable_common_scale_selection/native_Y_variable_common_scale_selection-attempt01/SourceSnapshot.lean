import Theorems.Thm_StickyKakeya4_native_Y_common_scale_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeYCommonScaleSelection
open Classical Finset
open scoped BigOperators

/-- Choose the common class by ORIGINAL Y-key cardinality. Its own common
rho/tau fraction is then summed over that class. This keeps the strong
relative-scale power and never replaces it by deltaY^zeta. Every surviving
height keeps the complete subset already produced by planar alignment. -/
theorem variable_retention_select_common {l : ℕ} (u bins : ℕ)
    (Y selected : Finset (ℤ × (Fin l → ℤ))) (hselected : selected⊆Y)
    (menu : ℤ → Menu u bins) (fraction : Menu u bins → ℝ)
    (hfraction : ∀c,0 ≤ fraction c)
    (hheight : ∀h∈Y.image Prod.fst,
      fraction (menu h)*((Y.filter (fun z => z.1=h)).card:ℝ) ≤
        ((selected.filter (fun z => z.1=h)).card:ℝ)) :
    ∃c : Menu u bins,
      let reference := Y.filter (fun z => menu z.1=c)
      let kept := selected.filter (fun z => menu z.1=c)
      kept⊆Y ∧
      (Y.card:ℝ) ≤ (2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ))*(reference.card:ℝ) ∧
      fraction c*(reference.card:ℝ) ≤ (kept.card:ℝ) ∧
      fraction c*(Y.card:ℝ) ≤ (2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ))*(kept.card:ℝ) ∧
      (∀z∈kept,menu z.1=c) ∧
      (∀h∈kept.image Prod.fst,
        kept.filter (fun z => z.1=h)=selected.filter (fun z => z.1=h)) := by
  obtain ⟨c,_hcsub,hcard,_hcommon,_hwhole⟩ :=
    select_common u bins Y Y (Subset.refl Y) 1 (by intro h _hh; simp only [one_mul,le_refl]) menu
  let reference := Y.filter (fun z => menu z.1=c)
  let kept := selected.filter (fun z => menu z.1=c)
  have href : reference⊆Y := filter_subset _ _
  have hkeep : kept⊆Y := (filter_subset _ _).trans hselected
  have hyes (V : Finset (ℤ × (Fin l → ℤ))) (h : ℤ) (hh : menu h=c) :
      (V.filter (fun z => menu z.1=c)).filter (fun z => z.1=h)=V.filter (fun z => z.1=h) := by
    rw [filter_filter]
    apply filter_congr
    intro z _hz
    constructor
    · exact fun hz => hz.2
    · intro hz
      exact ⟨by simpa only [hz] using hh,hz⟩
  have hno (V : Finset (ℤ × (Fin l → ℤ))) (h : ℤ) (hh : menu h≠c) :
      (V.filter (fun z => menu z.1=c)).filter (fun z => z.1=h)=∅ := by
    rw [filter_filter]
    apply filter_eq_empty_iff.mpr
    intro z _hz hz
    exact hh (by simpa only [hz.2] using hz.1)
  have hlocal : fraction c*(reference.card:ℝ) ≤ (kept.card:ℝ) := by
    have hRefPart : reference.card=∑h∈Y.image Prod.fst,(reference.filter (fun z => z.1=h)).card :=
      card_eq_sum_card_fiberwise (fun z hz => mem_image_of_mem Prod.fst (href hz))
    have hKeepPart : kept.card=∑h∈Y.image Prod.fst,(kept.filter (fun z => z.1=h)).card :=
      card_eq_sum_card_fiberwise (fun z hz => mem_image_of_mem Prod.fst (hkeep hz))
    rw [hRefPart,hKeepPart,Nat.cast_sum,Nat.cast_sum,mul_sum]
    apply sum_le_sum
    intro h hh
    by_cases hmenu : menu h=c
    · rw [hyes Y h hmenu,hyes selected h hmenu]
      simpa only [hmenu] using hheight h hh
    · rw [hno Y h hmenu,hno selected h hmenu]
      simp only [card_empty,Nat.cast_zero,mul_zero,le_refl]
  have hrefmass : (Y.card:ℝ) ≤ (2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ))*(reference.card:ℝ) := by
    simpa only [one_mul] using hcard
  refine ⟨c,hkeep,hrefmass,hlocal,?_,fun _ hz => (mem_filter.mp hz).2,?_⟩
  · calc
      _ ≤ fraction c*((2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ))*(reference.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hrefmass (hfraction c)
      _ = (2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ))*(fraction c*(reference.card:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlocal (by positivity)
  · intro h hh
    obtain ⟨z,hz,hzh⟩ := mem_image.mp hh
    have hmenu : menu h=c := by simpa only [hzh] using (mem_filter.mp hz).2
    exact hyes selected h hmenu

end NativeYCommonScaleSelection
