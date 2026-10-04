import Theorems.Thm_StickyKakeya4_finite_common_point_tube_representatives
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace OriginalDisjointSupportSelection

/-- Reuse the original-support selector: constant-zero relation at cutoff
-1 means exactly disjointness, with no geometric distance assertion. -/
theorem exists_maximal_disjoint_original_supports
    {ι P : Type*} [DecidableEq ι] [DecidableEq P]
    (I : Finset ι) (A : ι→Finset P) (hne : ∀ i∈I, (A i).Nonempty) :
    ∃ F : Finset ι, F⊆I ∧ (F:Set ι).PairwiseDisjoint A ∧
      ∀ i∈I, ∃ j∈F, (A i∩A j).Nonempty := by
  classical
  obtain ⟨F,hFI,hpair,hcover⟩ :=
    FiniteCommonPointTubeRepresentatives.exists_original_representatives I A (fun _ _ => 0) (-1)
  refine ⟨F,hFI,?_,?_⟩
  · intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hp : p∈A i∩A j := Finset.mem_inter.mpr ⟨hpi,hpj⟩
    have hh := hpair hi hj hij p hp p hp
    norm_num at hh
  · intro i hi
    by_cases hiF : i∈F
    · obtain ⟨p,hp⟩ := hne i hi
      exact ⟨i,hiF,p,Finset.mem_inter.mpr ⟨hp,hp⟩⟩
    · obtain ⟨j,hj,p,hp,_q,_hq,_hd⟩ := hcover i hi hiF
      exact ⟨j,hj,p,hp⟩

/-- Exact mass charge to the original ambient points. -/
theorem exists_rich_disjoint_original_supports
    {ι P : Type*} [DecidableEq ι] [DecidableEq P]
    (I : Finset ι) (A : ι→Finset P) (Ambient : Finset P) (H : ℝ) (hH : 0<H)
    (hsub : ∀ i∈I, A i⊆Ambient)
    (hrich : ∀ i∈I, H≤((A i).card : ℝ)) :
    ∃ F : Finset ι, F⊆I ∧ (F:Set ι).PairwiseDisjoint A ∧
      H*(F.card : ℝ)≤Ambient.card ∧ ∀ i∈I, ∃ j∈F, (A i∩A j).Nonempty := by
  classical
  have hne (i : ι) (hi : i∈I) : (A i).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hH.trans_le (hrich i hi)
  obtain ⟨F,hFI,hdis,hcover⟩ := exists_maximal_disjoint_original_supports I A hne
  have hunion : F.biUnion A⊆Ambient := by
    intro p hp
    obtain ⟨i,hi,hpA⟩ := Finset.mem_biUnion.mp hp
    exact hsub i (hFI hi) hpA
  have hcard : ((F.biUnion A).card : ℝ)=∑ i∈F, ((A i).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion (fun i hi j hj hij => hdis hi hj hij)
  refine ⟨F,hFI,hdis,?_,hcover⟩
  calc
    _ = ∑ _i∈F, H := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ ∑ i∈F, ((A i).card : ℝ) := Finset.sum_le_sum (fun i hi => hrich i (hFI hi))
    _ = ((F.biUnion A).card : ℝ) := hcard.symm
    _ ≤ Ambient.card := Nat.cast_le.mpr (Finset.card_le_card hunion)
end OriginalDisjointSupportSelection
