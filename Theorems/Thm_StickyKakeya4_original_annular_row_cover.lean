import Theorems.Thm_StickyKakeya4_rooted_shared_annular_tube_transfer
import Theorems.Thm_StickyKakeya4_original_disjoint_support_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace OriginalAnnularRowCover
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open RootedSharedAnnularTubeTransfer OriginalDisjointSupportSelection

def annularSupport (Pts : Finset Point) (p a : Point) (w tau : ℝ) : Finset Point := by
  classical
  exact (physicalPairTube Pts w (p,a)).filter
    (fun q => tau≤euclideanDistance p q ∧ euclideanDistance p q≤2*tau)

def badPartners (Pts : Finset Point) (G : Finset Pair) (p : Point) (w tau H : ℝ) : Finset Point := by
  classical
  exact Pts.filter (fun a => (p,a)∈G ∧ H≤((annularSupport Pts p a w tau).card : ℝ))

/-- Select disjoint rich ORIGINAL annular supports. An actual shared point
then places each bad original partner in a selected original wider tube. -/
theorem exists_original_annular_row_cover
    (Pts : Finset Point) (G : Finset Pair) (p : Point) (w tau H : ℝ)
    (hw : 0≤w) (htau : 0<tau) (htau1 : tau≤1) (hH : 0<H)
    (hpP : p∈Pts) (hbox : ∀ z∈Pts, |z.1|≤1 ∧ |z.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2) :
    ∃ F : Finset Point, F⊆badPartners Pts G p w tau H ∧
      (F:Set Point).PairwiseDisjoint (fun a => annularSupport Pts p a w tau) ∧
      H*(F.card : ℝ)≤(Pts.filter (fun q => euclideanDistance p q≤2*tau)).card ∧
      badPartners Pts G p w tau H⊆F.biUnion (fun b => physicalPairTube Pts (38*w/tau) (p,b)) ∧
      (badPartners Pts G p w tau H).card≤
        ∑ b∈F, (physicalPairTube Pts (38*w/tau) (p,b)).card := by
  classical
  let I := badPartners Pts G p w tau H
  let A := fun a => annularSupport Pts p a w tau
  let B := Pts.filter (fun q => euclideanDistance p q≤2*tau)
  have hsub (a : Point) (_ha : a∈I) : A a⊆B := by
    intro q hq
    obtain ⟨hqT,_hsep,hqball⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hqT).1,hqball⟩
  have hrich (a : Point) (ha : a∈I) : H≤((A a).card : ℝ) :=
    (Finset.mem_filter.mp ha).2.2
  obtain ⟨F,hFI,hdis,hmass,hcommon⟩ :=
    exists_rich_disjoint_original_supports I A B H hH hsub hrich
  have hcover : I⊆F.biUnion (fun b => physicalPairTube Pts (38*w/tau) (p,b)) := by
    intro a ha
    obtain ⟨b,hb,q,hq⟩ := hcommon a ha
    have hdataA := Finset.mem_filter.mp ha
    have hdataB := Finset.mem_filter.mp (hFI hb)
    have hpa : p≠a := hdistinct (p,a) hdataA.2.1
    have hpb : p≠b := hdistinct (p,b) hdataB.2.1
    obtain ⟨hqA,hqB⟩ := Finset.mem_inter.mp hq
    obtain ⟨hqAT,hqsep,_hqmax⟩ := Finset.mem_filter.mp hqA
    have hqBT := (Finset.mem_filter.mp hqB).1
    have haT : a∈physicalPairTube Pts w (p,a) := by
      apply Finset.mem_filter.mpr
      refine ⟨hdataA.1,1,?_⟩
      have hline : linePoint (p,a) 1=a := by
        apply Prod.ext <;> dsimp [linePoint] <;> ring
      rw [hline]
      simpa only [euclideanDistance,sub_self,
        zero_pow (by decide : 2≠0),zero_add,Real.sqrt_zero] using hw
    exact Finset.mem_biUnion.mpr ⟨b,hb,rooted_original_shared_point_transfer
      Pts p a b q a w tau hw htau htau1 hpa hpb hpP hbox hqAT hqBT hqsep haT⟩
  exact ⟨F,hFI,hdis,hmass,hcover,(Finset.card_le_card hcover).trans Finset.card_biUnion_le⟩
end OriginalAnnularRowCover
