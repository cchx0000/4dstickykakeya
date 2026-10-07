import Theorems.Thm_StickyKakeya4_separated_alignment_patches

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeYCommonScaleSelection
open Classical Finset
open scoped BigOperators

/-- The actual planar outputs: one of two coordinate charts, two bounded
dyadic depths, and one prechosen exponent bin. The final bin includes1. -/
abbrev Menu (u bins : ℕ) := Fin 2 × (Fin (u+10) × (Fin (u+10) × Fin (bins+1)))

lemma menu_card (u bins : ℕ) : Fintype.card (Menu u bins)=2*(u+10)^2*(bins+1) := by
  simp only [Menu,Fintype.card_prod,Fintype.card_fin]
  ring

/-- Select common planar parameters by their ACTUAL retained coarse-Y
key counts. Heights need not have comparable cardinalities. The resulting
literal subset keeps its height tag and needs only one Q-squared lift to
original edge weights from the already installed coarse-Y relation. -/
theorem select_common {l : ℕ} (u bins : ℕ)
    (Y selected : Finset (ℤ × (Fin l → ℤ))) (hselected : selected⊆Y)
    (theta : ℝ) (hheight : ∀h∈Y.image Prod.fst,
      theta*((Y.filter (fun z => z.1=h)).card:ℝ) ≤
        ((selected.filter (fun z => z.1=h)).card:ℝ))
    (menu : ℤ → Menu u bins) :
    ∃c : Menu u bins,
      let kept := selected.filter (fun z => menu z.1=c)
      kept⊆Y ∧
      theta*(Y.card:ℝ) ≤ (2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ))*(kept.card:ℝ) ∧
      (∀z∈kept,menu z.1=c) ∧
      (∀h∈kept.image Prod.fst,
        kept.filter (fun z => z.1=h)=selected.filter (fun z => z.1=h)) := by
  have hYpart : Y.card=∑h∈Y.image Prod.fst,(Y.filter (fun z => z.1=h)).card :=
    card_eq_sum_card_image Prod.fst Y
  have hSpart : selected.card=∑h∈Y.image Prod.fst,(selected.filter (fun z => z.1=h)).card :=
    card_eq_sum_card_fiberwise (fun z hz => mem_image_of_mem Prod.fst (hselected hz))
  have hmass : theta*(Y.card:ℝ) ≤ (selected.card:ℝ) := by
    rw [hYpart,hSpart,Nat.cast_sum,Nat.cast_sum,mul_sum]
    exact sum_le_sum (fun h hh => hheight h hh)
  obtain ⟨c,hc⟩ := SeparatedAlignmentPatches.maximum_weight_color selected
    (fun _ => 1) (fun z => menu z.1)
  have hcNat : selected.card ≤ (2*(u+10)^2*(bins+1))*
      (selected.filter (fun z => menu z.1=c)).card := by
    simpa only [sum_const,nsmul_eq_mul,mul_one,menu_card,Nat.cast_id] using hc
  refine ⟨c,(filter_subset _ _).trans hselected,?_,fun _ hz => (mem_filter.mp hz).2,?_⟩
  · have hh : (selected.card:ℝ) ≤ (2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ))*
        ((selected.filter (fun z => menu z.1=c)).card:ℝ) := by exact_mod_cast hcNat
    exact hmass.trans hh
  · intro h hh
    obtain ⟨z,hz,hzh⟩ := mem_image.mp hh
    have hmenu : menu h=c := by simpa only [hzh] using (mem_filter.mp hz).2
    ext w
    simp only [mem_filter]
    constructor
    · exact fun hw => ⟨hw.1.1,hw.2⟩
    · rintro ⟨hw,hwh⟩
      exact ⟨⟨hw,by simpa only [hwh] using hmenu⟩,hwh⟩

end NativeYCommonScaleSelection
