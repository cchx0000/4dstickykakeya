import Theorems.Thm_StickyKakeya4_original_three_dimensional_cap_distance
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalSeparatedNormals
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalHeavySliceGraph
open OriginalThreeDimensionalUnitNormals OriginalThreeDimensionalCapCount
open OriginalThreeDimensionalCapDistance OriginalThreeDimensionalTubeSlab

lemma distance3_comm (p q : Point3) : distance3 p q=distance3 q p := by
  unfold distance3
  rw [sub_sq_comm (p 0) (q 0),sub_sq_comm (p 1) (q 1),sub_sq_comm (p 2) (q 2)]

lemma distance3_self (p : Point3) : distance3 p p=0 := by simp [distance3]

lemma distance3_neg_right_comm (p q : Point3) : distance3 p (-q)=distance3 q (-p) := by
  simp only [distance3,Pi.neg_apply]
  congr 1
  ring

/-- Actual unoriented normal distance, without introducing a quotient or
assuming a projective metric instance. -/
def unorientedDistance (rho : ℝ) (a b : DirectionLabel) : ℝ :=
  min (distance3 (unitNormal rho a) (unitNormal rho b))
    (distance3 (unitNormal rho a) (-unitNormal rho b))

lemma unoriented_distance_comm (rho : ℝ) (a b : DirectionLabel) :
    unorientedDistance rho a b=unorientedDistance rho b a := by
  unfold unorientedDistance
  rw [distance3_comm (unitNormal rho a) (unitNormal rho b),distance3_neg_right_comm]

lemma unoriented_distance_self (rho : ℝ) (a : DirectionLabel) :
    unorientedDistance rho a a=0 := by
  have hn : 0≤distance3 (unitNormal rho a) (-unitNormal rho a) := Real.sqrt_nonneg _
  unfold unorientedDistance
  rw [distance3_self,min_eq_left hn]

def RelationSeparated {X : Type*} (C : Finset X) (R : X→X→Prop) : Prop :=
  ∀ a∈C, ∀ b∈C, a≠b → R a b

/-- A finite maximal symmetric relation supplies an actual covering
subfamily. No metric triangle inequality or external packing input is used. -/
lemma exists_symmetric_relation_net {X : Type*} [DecidableEq X]
    (S : Finset X) (R : X→X→Prop) (hirr : ∀ x, ¬R x x)
    (hsymm : ∀ x y, R x y → R y x) :
    ∃ C : Finset X, C⊆S ∧ (∀ a∈C, ∀ b∈C, a≠b → R a b) ∧
      ∀ p∈S, ∃ c∈C, ¬R p c := by
  classical
  let families := S.powerset.filter (fun C => RelationSeparated C R)
  have hempty : (∅ : Finset X)∈families := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.empty_subset S),?_⟩
    intro a ha
    exact (Finset.notMem_empty a ha).elim
  obtain ⟨C,hC,hmax⟩ := Finset.exists_max_image families (fun C => C.card) ⟨∅,hempty⟩
  obtain ⟨hCS,hsep⟩ := Finset.mem_filter.mp hC
  have hsub : C⊆S := Finset.mem_powerset.mp hCS
  refine ⟨C,hsub,hsep,?_⟩
  intro p hp
  by_contra hnot
  have hfar : ∀ c∈C, R p c := by
    intro c hc
    by_contra hn
    exact hnot ⟨c,hc,hn⟩
  have hpnot : p∉C := fun hpC => hirr p (hfar p hpC)
  have hinsert : insert p C∈families := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hp hsub),?_⟩
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact (hab rfl).elim
      · exact hfar b hb
    · rcases hb with rfl | hb
      · exact hsymm _ _ (hfar a ha)
      · exact hsep a ha b hb hab
  have hm := hmax (insert p C) hinsert
  have hlt : C.card<(insert p C).card := by simp [hpnot]
  exact (not_lt_of_ge hm) hlt

lemma actual_unoriented_net (S : Finset DirectionLabel) (rho w : ℝ) (hw : 0<w) :
    ∃ C : Finset DirectionLabel, C⊆S ∧
      (∀ a∈C, ∀ b∈C, a≠b → w≤unorientedDistance rho a b) ∧
      ∀ d∈S, ∃ c∈C,
        distance3 (unitNormal rho d) (unitNormal rho c)<w ∨
        distance3 (unitNormal rho d) (-unitNormal rho c)<w := by
  have hi : ∀ a, ¬w≤unorientedDistance rho a a := by
    intro a
    rw [unoriented_distance_self]
    exact not_le_of_gt hw
  have hs : ∀ a b, w≤unorientedDistance rho a b → w≤unorientedDistance rho b a := by
    intro a b hab
    rwa [unoriented_distance_comm]
  obtain ⟨C,hCS,hsep,hcov⟩ := exists_symmetric_relation_net S
    (fun a b => w≤unorientedDistance rho a b) hi hs
  refine ⟨C,hCS,hsep,?_⟩
  intro d hd
  obtain ⟨c,hc,hclose⟩ := hcov d hd
  exact ⟨c,hc,min_lt_iff.mp (lt_of_not_ge hclose)⟩

lemma weighted_cover_count {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (S : Finset X) (C : Finset Y) (F : Y→Finset X) (T M : ℝ) (hT : 0≤T)
    (hcover : S⊆C.biUnion F) (hF : ∀ c∈C, ((F c).card : ℝ)*T≤M) :
    (S.card : ℝ)*T≤M*C.card := by
  have hc : (S.card : ℝ)≤∑ c∈C, ((F c).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  calc
    _ ≤ (∑ c∈C, ((F c).card : ℝ))*T := mul_le_mul_of_nonneg_right hc hT
    _ = ∑ c∈C, ((F c).card : ℝ)*T := by rw [Finset.sum_mul]
    _ ≤ ∑ _c∈C, M := Finset.sum_le_sum hF
    _ = _ := by simp [mul_comm]

/-- The two genuine Euclidean caps corresponding to an unoriented slab. -/
def doubleCap (S : Finset DirectionLabel) (rho w : ℝ) (n : Point3) : Finset DirectionLabel :=
  S.filter (fun d => distance3 (unitNormal rho d) n≤w ∨ distance3 (unitNormal rho d) (-n)≤w)

lemma original_double_cap_count (S : Finset DirectionLabel) (rho w r : ℝ)
    (p q n : Point3) (hrho : 0<rho) (hrhow : rho≤w) (hwsmall : w≤1/10)
    (hr : 0<r) (hsep : r≤distance3 p q)
    (hp : ∀ i, |p i|≤1) (hq : ∀ i, |q i|≤1) (hunit : ∑ i, (n i)^2=1)
    (hS : S⊆pairBand rho p q) :
    ((doubleCap S rho w n).card : ℝ)*rho*r≤720000*w := by
  let P := S.filter (fun d => distance3 (unitNormal rho d) n≤w)
  let N := S.filter (fun d => distance3 (unitNormal rho d) (-n)≤w)
  have hgrid : S⊆normalGrid rho := fun d hd => (Finset.mem_filter.mp (hS hd)).1
  have hband : ∀ d∈S, |value rho d q-value rho d p|≤3*rho := by
    intro d hd
    have hh := (Finset.mem_filter.mp (hS hd)).2
    linarith only [hh,hrho]
  have hn := unit_center_components n hunit
  have hneg : ∀ i, |(-n) i|≤1 := by intro i; simpa only [Pi.neg_apply,abs_neg] using hn i
  have hP := original_separated_cap_count P rho w r p q n hrho hrhow hwsmall hr hsep hp hq hn
    (fun d hd => hgrid (Finset.mem_filter.mp hd).1)
    (fun d hd => hband d (Finset.mem_filter.mp hd).1)
    (fun d hd => (Finset.mem_filter.mp hd).2)
  have hN := original_separated_cap_count N rho w r p q (-n) hrho hrhow hwsmall hr hsep hp hq hneg
    (fun d hd => hgrid (Finset.mem_filter.mp hd).1)
    (fun d hd => hband d (Finset.mem_filter.mp hd).1)
    (fun d hd => (Finset.mem_filter.mp hd).2)
  have he : doubleCap S rho w n=P∪N := by
    ext d
    simp only [doubleCap,P,N,Finset.mem_filter,Finset.mem_union]
    tauto
  have hc : ((doubleCap S rho w n).card : ℝ)≤(P.card : ℝ)+N.card := by
    rw [he]
    exact_mod_cast Finset.card_union_le P N
  have hm := mul_le_mul_of_nonneg_right hc (show 0≤rho*r by positivity)
  nlinarith only [hP,hN,hm]

/-- Greedy extraction on the original good-direction labels gives many
actual heavy slab normals separated even after reversing their orientation. -/
theorem exists_original_unoriented_separated_labels
    (P : Finset Point3) (G : Finset Pair3) (rho H w r : ℝ) (z : Pair3)
    (hrho : 0<rho) (hrhow : rho≤w) (hwsmall : w≤1/10)
    (hr : 0<r) (hsep : r≤distance3 z.1 z.2)
    (hp : ∀ i, |z.1 i|≤1) (hq : ∀ i, |z.2 i|≤1)
    (hz : z∈retainedPairs P G rho H) :
    ∃ C : Finset DirectionLabel, C⊆goodDirections P rho H z ∧
      (∀ a∈C, ∀ b∈C, a≠b → w≤unorientedDistance rho a b) ∧
      r/(1440000*w)≤(C.card : ℝ) := by
  let S := goodDirections P rho H z
  have hw : 0<w := hrho.trans_le hrhow
  obtain ⟨C,hCS,hCsep,hcov⟩ := actual_unoriented_net S rho w hw
  have hS : S⊆pairBand rho z.1 z.2 := Finset.filter_subset _ _
  have hcover : S⊆C.biUnion (fun c => doubleCap S rho w (unitNormal rho c)) := by
    intro d hd
    obtain ⟨c,hc,hclose⟩ := hcov d hd
    refine Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_filter.mpr ⟨hd,?_⟩⟩
    exact hclose.imp le_of_lt le_of_lt
  have hlocal : ∀ c∈C, ((doubleCap S rho w (unitNormal rho c)).card : ℝ)*(rho*r)≤720000*w := by
    intro c _hc
    have hh := original_double_cap_count S rho w r z.1 z.2 (unitNormal rho c)
      hrho hrhow hwsmall hr hsep hp hq (original_unit_normal_square rho c) hS
    nlinarith only [hh]
  have htotal := weighted_cover_count S C (fun c => doubleCap S rho w (unitNormal rho c))
    (rho*r) (720000*w) (by positivity) hcover hlocal
  have hmass : 1≤2*rho*(S.card : ℝ) := (Finset.mem_filter.mp hz).2
  have hm := mul_le_mul_of_nonneg_right hmass hr.le
  refine ⟨C,hCS,hCsep,?_⟩
  apply (div_le_iff₀ (show 0<1440000*w by positivity)).mpr
  nlinarith only [htotal,hm]

/-- The separated labels retain literal original heavy slabs through both
endpoints, with their actual Euclidean unit normals and original point sets. -/
theorem exists_original_unoriented_heavy_normals
    (P : Finset Point3) (G : Finset Pair3) (rho H w r : ℝ) (z : Pair3)
    (hrho : 0<rho) (hrhow : rho≤w) (hwsmall : w≤1/10)
    (hr : 0<r) (hsep : r≤distance3 z.1 z.2)
    (hp : ∀ i, |z.1 i|≤1) (hq : ∀ i, |z.2 i|≤1)
    (hz : z∈retainedPairs P G rho H) :
    ∃ C : Finset DirectionLabel, C⊆goodDirections P rho H z ∧
      (∀ a∈C, ∀ b∈C, a≠b → w≤unorientedDistance rho a b) ∧
      r/(1440000*w)≤(C.card : ℝ) ∧
      ∀ d∈C, (∑ i, (unitNormal rho d i)^2)=1 ∧
        ∃ c : ℝ, ∃ Q : Finset Point3, Q⊆P ∧ H≤(Q.card : ℝ) ∧ z.1∈Q ∧ z.2∈Q ∧
          ∀ p∈Q, |(∑ i, unitNormal rho d i*p i)-c|≤3*rho := by
  obtain ⟨C,hCS,hsepC,hmass⟩ := exists_original_unoriented_separated_labels
    P G rho H w r z hrho hrhow hwsmall hr hsep hp hq hz
  refine ⟨C,hCS,hsepC,hmass,?_⟩
  intro d hd
  exact original_unit_normal_heavy_witness P rho H z (unitNormal rho d) hrho.le
    (Finset.mem_image_of_mem _ (hCS hd))

end OriginalThreeDimensionalSeparatedNormals
