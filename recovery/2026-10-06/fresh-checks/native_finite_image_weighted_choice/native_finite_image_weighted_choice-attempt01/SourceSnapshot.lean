import Theorems.Thm_StickyKakeya4_native_matrix_height_wholepoint

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
noncomputable section

namespace NativeFiniteImageWeightedChoice
open Classical Finset NativeMatrixHeightWholePoint
open scoped BigOperators

/-- Maximize ORIGINAL weight over the actual occupied label image in each
cell. No finite ambient label type is required. Every occupied cell survives,
including when its original weights are all zero. -/
theorem select_per_cell {P C Q : Type*} [DecidableEq C] [DecidableEq Q] [Inhabited Q]
    (S : Finset P) (weight : P → ℕ) (physical : P → C) (label : P → Q)
    (N : ℕ) (hCard : ∀c,((S.filter (fun p => physical p=c)).image label).card ≤ N) :
    ∃B⊆S,mass S weight ≤ N*mass B weight ∧ B.image physical=S.image physical ∧
      (∀c,mass (S.filter (fun p => physical p=c)) weight ≤
        N*mass (B.filter (fun p => physical p=c)) weight) ∧
      ∀p∈B,∀q∈B,physical p=physical q → label p=label q := by
  have hchoose : ∀c∈S.image physical,
      ∃b∈(S.filter (fun p => physical p=c)).image label,
        mass (S.filter (fun p => physical p=c)) weight ≤
          N*mass ((S.filter (fun p => physical p=c)).filter (fun p => label p=b)) weight := by
    intro c hc
    obtain ⟨p,hp,hpc⟩ := mem_image.mp hc
    let fiber := S.filter (fun p => physical p=c)
    have hne : (fiber.image label).Nonempty :=
      ⟨label p,mem_image_of_mem label (mem_filter.mpr ⟨hp,hpc⟩)⟩
    obtain ⟨b,hb,hmax⟩ := exists_max_image (fiber.image label)
      (fun b => mass (fiber.filter (fun p => label p=b)) weight) hne
    refine ⟨b,hb,?_⟩
    calc
      mass fiber weight = ∑b∈fiber.image label,mass (fiber.filter (fun p => label p=b)) weight :=
        (sum_fiberwise_of_maps_to (fun p hp => mem_image_of_mem label hp) weight).symm
      _ ≤ ∑_b∈fiber.image label,mass (fiber.filter (fun p => label p=b)) weight :=
        sum_le_sum (fun b' hb' => hmax b' hb')
      _ = (fiber.image label).card*mass (fiber.filter (fun p => label p=b)) weight := by simp
      _ ≤ N*mass (fiber.filter (fun p => label p=b)) weight := Nat.mul_le_mul_right _ (hCard c)
  let chi : C → Q := fun c => if hc : c∈S.image physical then Classical.choose (hchoose c hc) else default
  have hchi (c : C) (hc : c∈S.image physical) :
      chi c∈(S.filter (fun p => physical p=c)).image label ∧
      mass (S.filter (fun p => physical p=c)) weight ≤
        N*mass ((S.filter (fun p => physical p=c)).filter (fun p => label p=chi c)) weight := by
    simpa only [chi,dif_pos hc] using Classical.choose_spec (hchoose c hc)
  let B := S.filter (fun p => label p=chi (physical p))
  have hBS : B⊆S := filter_subset _ _
  have hlocal (c : C) : B.filter (fun p => physical p=c)=
      (S.filter (fun p => physical p=c)).filter (fun p => label p=chi c) := by
    ext p
    simp only [B,mem_filter]
    constructor
    · rintro ⟨⟨hp,hl⟩,hc⟩
      exact ⟨⟨hp,hc⟩,by simpa only [hc] using hl⟩
    · rintro ⟨⟨hp,hc⟩,hl⟩
      exact ⟨⟨hp,by simpa only [hc] using hl⟩,hc⟩
  have hret (c : C) : mass (S.filter (fun p => physical p=c)) weight ≤
      N*mass (B.filter (fun p => physical p=c)) weight := by
    by_cases hc : c∈S.image physical
    · rw [hlocal]
      exact (hchi c hc).2
    · have hempty : S.filter (fun p => physical p=c)=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hpS,hpc⟩ := mem_filter.mp hp
        exact hc (mem_image.mpr ⟨p,hpS,hpc⟩)
      simp only [hempty,mass,sum_empty,Nat.zero_le]
  have hsumS : ∑c∈S.image physical,mass (S.filter (fun p => physical p=c)) weight=mass S weight :=
    sum_fiberwise_of_maps_to (fun p hp => mem_image_of_mem physical hp) weight
  have hsumB : ∑c∈S.image physical,mass (B.filter (fun p => physical p=c)) weight=mass B weight :=
    sum_fiberwise_of_maps_to (fun p hp => mem_image_of_mem physical (hBS hp)) weight
  refine ⟨B,hBS,?_,?_,hret,?_⟩
  · calc
      mass S weight = ∑c∈S.image physical,mass (S.filter (fun p => physical p=c)) weight := hsumS.symm
      _ ≤ ∑c∈S.image physical,N*mass (B.filter (fun p => physical p=c)) weight :=
        sum_le_sum (fun c _ => hret c)
      _ = N*mass B weight := by rw [←mul_sum,hsumB]
  · apply Subset.antisymm (image_subset_image hBS)
    intro c hc
    obtain ⟨p,hp,hpl⟩ := mem_image.mp (hchi c hc).1
    obtain ⟨hpS,hpc⟩ := mem_filter.mp hp
    exact mem_image.mpr ⟨p,mem_filter.mpr ⟨hpS,by simpa only [hpc] using hpl⟩,hpc⟩
  · intro p hp q hq heq
    exact (mem_filter.mp hp).2.trans (by rw [heq]; exact (mem_filter.mp hq).2.symm)

end NativeFiniteImageWeightedChoice
