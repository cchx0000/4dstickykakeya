import Theorems.Thm_StickyKakeya4_native_local_offset_count
import Theorems.Thm_StickyKakeya4_native_finite_image_weighted_choice

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeLocalOffsetSelection
open Classical Finset NativeMatrixHeightWholePoint NativeLocalOffsetCount
open NativeFiniteImageWeightedChoice
open scoped BigOperators

def physicalFiber {P T Cell : Type*} (S : Finset (P × T)) (physical : P → Cell) (c : Cell) :
    Finset (P × T) := S.filter (fun z => physical z.1=c)

lemma fiber_points_cell {P T Cell : Type*} (S : Finset (P × T)) (physical : P → Cell) (c : Cell)
    {p : P} (hp : p∈(physicalFiber S physical c).image Prod.fst) : physical p=c := by
  obtain ⟨z,hz,hzp⟩ := mem_image.mp hp
  have hh := (mem_filter.mp hz).2
  simpa only [hzp] using hh

lemma point_fiber_eq {P T Cell : Type*} (S : Finset (P × T)) (physical : P → Cell)
    (c : Cell) (p : P) (hp : physical p=c) :
    (physicalFiber S physical c).filter (fun z => z.1=p)=S.filter (fun z => z.1=p) := by
  ext z
  simp only [physicalFiber,mem_filter]
  constructor
  · exact fun hz => ⟨hz.1.1,hz.2⟩
  · rintro ⟨hz,he⟩
    exact ⟨⟨hz,by rw [he,hp]⟩,he⟩

lemma same_offset_coordinates {ell : ℕ} {w : ℝ} (hw : 0 < w) {x y : Fin ell → ℝ}
    (h : offsetCell w x=offsetCell w y) : ∀i,|x i-y i| < w := by
  intro i
  apply same_height_cell_close (shift:=0) hw
  simpa only [heightCell,sub_zero,offsetCell] using congrFun h i

/-- The offset-image cap is derived internally on each actual physical-cell
incidence fiber. Its per-point angular fibers are exactly the original ones. -/
theorem actual_cell_offset_cap {P T Angle Cell : Type*} {k ell : ℕ}
    (S : Finset (P × T)) (angle : T → Angle) (physical : P → Cell)
    (tangent : T → Fin k → ℝ) (normal : T → Fin ell → ℝ)
    (field : P → Fin ell → Fin k → ℝ) (xi : P → Fin ell → ℝ)
    (E M v A B lower upper : ℝ) (hk : k ≤ 2)
    (hE : 0 ≤ E) (hM : 0 < M) (hv : 0 ≤ v) (hA : 0 < A) (hB : 0 ≤ B)
    (hLowerPos : 0 < lower)
    (hT : ∀z∈S,∀j,|tangent z.2 j| ≤ B)
    (hF : ∀p∈S.image Prod.fst,∀i j,|field p i j| ≤ (1/4:ℝ))
    (hVar : ∀p∈S.image Prod.fst,∀q∈S.image Prod.fst,physical p=physical q →
      ∀i j,|field p i j-field q i j| ≤ v)
    (hAngle : ∀z∈S,∀u∈S,angle z.2=angle u.2 →
      (∀j,|tangent z.2 j-tangent u.2 j| ≤ A/M) ∧
      (∀i,|normal z.2 i-normal u.2 i| ≤ A/M))
    (hRes : ∀z∈S,∀i,|normal z.2 i-(∑j,field z.1 i j*tangent z.2 j)-xi z.1 i| ≤ E)
    (hLower : ∀p∈S.image Prod.fst,
      lower ≤ (((S.filter (fun z => z.1=p)).image (fun z => angle z.2)).card:ℝ))
    (hUpper : ∀c,(((physicalFiber S physical c).image (fun z => angle z.2)).card:ℝ) ≤ upper) :
    ∀c,((physicalFiber S physical c).image (fun z => offsetCell (2*E+2*A/M+2*B*v) (xi z.1))).card ≤
      ⌈((3:ℝ)^ell*upper)/lower⌉₊ := by
  intro c
  let Sc := physicalFiber S physical c
  have hSc : Sc⊆S := filter_subset _ _
  have hP : Sc.image Prod.fst⊆S.image Prod.fst := image_subset_image hSc
  have hL : ∀p∈Sc.image Prod.fst,
      lower ≤ (((Sc.filter (fun z => z.1=p)).image (fun z => angle z.2)).card:ℝ) := by
    intro p hp
    have heq := point_fiber_eq S physical c p (fiber_points_cell S physical c hp)
    rw [heq]
    exact hLower p (hP hp)
  have hh := actual_offset_count Sc angle tangent normal field xi E M v A B lower hk hE hM hv hA hB
    (fun z hz => hT z (hSc hz)) (fun p hp => hF p (hP hp))
    (fun p hp q hq => hVar p (hP hp) q (hP hq)
      ((fiber_points_cell S physical c hp).trans (fiber_points_cell S physical c hq).symm))
    (fun z hz u hu => hAngle z (hSc hz) u (hSc hu))
    (fun z hz => hRes z (hSc hz)) hL
  have hbound : (((Sc.image (fun z => offsetCell (2*E+2*A/M+2*B*v) (xi z.1))).card):ℝ) ≤
      ((3:ℝ)^ell*upper)/lower := by
    apply (le_div_iff₀ hLowerPos).mpr
    exact hh.trans (mul_le_mul_of_nonneg_left (hUpper c) (by positivity))
  exact Nat.cast_le.mp (hbound.trans (Nat.le_ceil _))

/-- Actual weighted offset selection, preserving whole original-point
incidence fibers. The label palette is the actual finite image, not an
assumed finite ambient type or a supplied offset-menu certificate. -/
theorem actual_weighted_offset_selection {P T Angle Cell : Type*} {k ell : ℕ}
    (S : Finset (P × T)) (angle : T → Angle) (physical : P → Cell)
    (tangent : T → Fin k → ℝ) (normal : T → Fin ell → ℝ)
    (field : P → Fin ell → Fin k → ℝ) (xi : P → Fin ell → ℝ)
    (E M v A B lower upper : ℝ) (hk : k ≤ 2)
    (hE : 0 ≤ E) (hM : 0 < M) (hv : 0 ≤ v) (hA : 0 < A) (hB : 0 ≤ B)
    (hLowerPos : 0 < lower)
    (hT : ∀z∈S,∀j,|tangent z.2 j| ≤ B)
    (hF : ∀p∈S.image Prod.fst,∀i j,|field p i j| ≤ (1/4:ℝ))
    (hVar : ∀p∈S.image Prod.fst,∀q∈S.image Prod.fst,physical p=physical q →
      ∀i j,|field p i j-field q i j| ≤ v)
    (hAngle : ∀z∈S,∀u∈S,angle z.2=angle u.2 →
      (∀j,|tangent z.2 j-tangent u.2 j| ≤ A/M) ∧
      (∀i,|normal z.2 i-normal u.2 i| ≤ A/M))
    (hRes : ∀z∈S,∀i,|normal z.2 i-(∑j,field z.1 i j*tangent z.2 j)-xi z.1 i| ≤ E)
    (hLower : ∀p∈S.image Prod.fst,
      lower ≤ (((S.filter (fun z => z.1=p)).image (fun z => angle z.2)).card:ℝ))
    (hUpper : ∀c,(((physicalFiber S physical c).image (fun z => angle z.2)).card:ℝ) ≤ upper)
    (weight : P → ℕ) :
    let w := 2*E+2*A/M+2*B*v
    let N := ⌈((3:ℝ)^ell*upper)/lower⌉₊
    (S.Nonempty → 0 < N) ∧
    ∃Bpoints⊆S.image Prod.fst,let Tkeep := edgeLift S Prod.fst Bpoints
      Tkeep⊆S ∧ mass (S.image Prod.fst) weight ≤ N*mass Bpoints weight ∧
      Bpoints.image physical=(S.image Prod.fst).image physical ∧
      (∀p∈Bpoints,Tkeep.filter (fun z => z.1=p)=S.filter (fun z => z.1=p)) ∧
      (S.Nonempty → Tkeep.Nonempty) ∧
      ∀z∈Tkeep,∀u∈Tkeep,physical z.1=physical u.1 → ∀i,|xi z.1 i-xi u.1 i| < w := by
  intro w N
  have hcap := actual_cell_offset_cap S angle physical tangent normal field xi E M v A B lower upper hk hE hM hv hA hB
    hLowerPos hT hF hVar hAngle hRes hLower hUpper
  have hN : S.Nonempty → 0 < N := by
    rintro ⟨z,hz⟩
    have hpos : 0 < ((physicalFiber S physical (physical z.1)).image
        (fun u => offsetCell w (xi u.1))).card :=
      card_pos.mpr ⟨offsetCell w (xi z.1),mem_image_of_mem _ (mem_filter.mpr ⟨hz,rfl⟩)⟩
    exact hpos.trans_le (hcap (physical z.1))
  have hpointCap (c : Cell) :
      (((S.image Prod.fst).filter (fun p => physical p=c)).image (fun p => offsetCell w (xi p))).card ≤ N := by
    rw [filter_image,image_image]
    exact hcap c
  obtain ⟨Bpoints,hBpoints,hret,hphysical,_hlocal,hcoh⟩ := select_per_cell (S.image Prod.fst)
    weight physical (fun p => offsetCell w (xi p)) N hpointCap
  refine ⟨hN,Bpoints,hBpoints,filter_subset _ _,hret,hphysical,
    fun p hp => edgeLift_fiber S Prod.fst Bpoints p hp,?_,?_⟩
  · rintro ⟨z,hz⟩
    have hc : physical z.1∈Bpoints.image physical := by
      rw [hphysical]
      exact mem_image_of_mem _ (mem_image_of_mem Prod.fst hz)
    obtain ⟨p,hp,_hpc⟩ := mem_image.mp hc
    obtain ⟨u,hu,hup⟩ := mem_image.mp (hBpoints hp)
    exact ⟨u,mem_filter.mpr ⟨hu,by simpa only [hup] using hp⟩⟩
  · intro z hz u hu hcell
    have hw : 0 < w := by dsimp [w]; positivity
    exact same_offset_coordinates hw
      (hcoh z.1 (mem_filter.mp hz).2 u.1 (mem_filter.mp hu).2 hcell)

/-- The actual ORIGINAL incidence-cardinality specialization. The weight
at each original point is computed from its exact old incidence fiber. -/
theorem actual_incidence_offset_selection {P T Angle Cell : Type*} {k ell : ℕ}
    (S : Finset (P × T)) (angle : T → Angle) (physical : P → Cell)
    (tangent : T → Fin k → ℝ) (normal : T → Fin ell → ℝ)
    (field : P → Fin ell → Fin k → ℝ) (xi : P → Fin ell → ℝ)
    (E M v A B lower upper : ℝ) (hk : k ≤ 2)
    (hE : 0 ≤ E) (hM : 0 < M) (hv : 0 ≤ v) (hA : 0 < A) (hB : 0 ≤ B)
    (hLowerPos : 0 < lower)
    (hT : ∀z∈S,∀j,|tangent z.2 j| ≤ B)
    (hF : ∀p∈S.image Prod.fst,∀i j,|field p i j| ≤ (1/4:ℝ))
    (hVar : ∀p∈S.image Prod.fst,∀q∈S.image Prod.fst,physical p=physical q →
      ∀i j,|field p i j-field q i j| ≤ v)
    (hAngle : ∀z∈S,∀u∈S,angle z.2=angle u.2 →
      (∀j,|tangent z.2 j-tangent u.2 j| ≤ A/M) ∧
      (∀i,|normal z.2 i-normal u.2 i| ≤ A/M))
    (hRes : ∀z∈S,∀i,|normal z.2 i-(∑j,field z.1 i j*tangent z.2 j)-xi z.1 i| ≤ E)
    (hLower : ∀p∈S.image Prod.fst,
      lower ≤ (((S.filter (fun z => z.1=p)).image (fun z => angle z.2)).card:ℝ))
    (hUpper : ∀c,(((physicalFiber S physical c).image (fun z => angle z.2)).card:ℝ) ≤ upper) :
    let w := 2*E+2*A/M+2*B*v
    let N := ⌈((3:ℝ)^ell*upper)/lower⌉₊
    (S.Nonempty → 0 < N) ∧
    ∃Bpoints⊆S.image Prod.fst,let Tkeep := edgeLift S Prod.fst Bpoints
      Tkeep⊆S ∧ S.card ≤ N*Tkeep.card ∧
      Bpoints.image physical=(S.image Prod.fst).image physical ∧
      (∀p∈Bpoints,Tkeep.filter (fun z => z.1=p)=S.filter (fun z => z.1=p)) ∧
      (S.Nonempty → Tkeep.Nonempty) ∧
      ∀z∈Tkeep,∀u∈Tkeep,physical z.1=physical u.1 → ∀i,|xi z.1 i-xi u.1 i| < w := by
  intro w N
  let weight := fun p => (S.filter (fun z => z.1=p)).card
  obtain ⟨hN,Bpoints,hBpoints,hsub,hret,hphysical,hfiber,hne,hcoh⟩ := actual_weighted_offset_selection S angle physical tangent normal field xi E M v A B lower upper hk hE hM hv hA hB
    hLowerPos hT hF hVar hAngle hRes hLower hUpper weight
  have hmass : mass (S.image Prod.fst) weight=S.card := (card_eq_sum_card_image Prod.fst S).symm
  rw [hmass,←edgeLift_card S Prod.fst Bpoints] at hret
  exact ⟨hN,Bpoints,hBpoints,hsub,hret,hphysical,hfiber,hne,hcoh⟩

end NativeLocalOffsetSelection
