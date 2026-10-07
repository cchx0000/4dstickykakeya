import Theorems.Thm_StickyKakeya4_native_cubical_diameter_count
import Theorems.Thm_StickyKakeya4_native_transverse_fiber_diameter

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

noncomputable section
namespace NativeApproximateFiberCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalDiameterCount NativeTransverseFiberDiameter
open scoped BigOperators

/-- A literal subset of the geometric vertices at the specified mesh, selected
by approximate membership of its actual center in an affine plane. Any map
from weighted original microcells to these vertices is a separate input to
the later application; this definition does not identify those populations. -/
def fiber (mesh : ℝ) (A : Finset Index) (P : Submodule ℝ E4) (x : E4) (h : ℝ) : Finset Index :=
  A.filter (fun k => Metric.infDist (cellCenter mesh k-x) (P:Set E4) ≤ h)

lemma infDist_sub_comm (P : Submodule ℝ E4) (x y : E4) :
    Metric.infDist (x-y) (P:Set E4)=Metric.infDist (y-x) (P:Set E4) := by
  have himage : (fun u : E4 => -u) '' (P:Set E4)=(P:Set E4) := by
    ext u
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact P.neg_mem hv
    · intro hu
      exact ⟨-u,P.neg_mem hu,neg_neg u⟩
  have hh := Metric.infDist_image (x:=x-y) (t:=(P:Set E4)) (isometry_neg : Isometry (fun u : E4 => -u))
  rw [himage] at hh
  simpa only [neg_sub] using hh.symm

/-- The overlap denominator is proved from transversality and the mesh. -/
theorem card_le_of_approximate_fibers (A : Finset Index) {mesh : ℝ} (hm : 0 < mesh)
    (P : Submodule ℝ E4) (v : E4) (q h bound : ℝ)
    (hq : 0 < q) (hh : 0 < h) (hbound : 0 ≤ bound)
    (htrans : q ≤ Metric.infDist v (P:Set E4)) (hv : ‖v‖ ≤ bound)
    (x z : E4)
    (hP : ∀k∈A,Metric.infDist (cellCenter mesh k-z) (P:Set E4) ≤ h)
    (hQ : ∀k∈A,Metric.infDist (cellCenter mesh k-x) (Submodule.span ℝ {v}:Set E4) ≤ h) :
    A.card ≤ capacity mesh (4*h+(8*h/q)*bound) := by
  apply card_le_of_center_diameter A hm _ (by positivity)
  intro k hk l hl
  exact approximate_fiber_diameter P v q h bound hq hh hbound htrans hv x z
    (cellCenter mesh k) (cellCenter mesh l) (hP k hk) (hP l hl) (hQ k hk) (hQ l hl)

theorem intersection_card_le (A : Finset Index) {mesh : ℝ} (hm : 0 < mesh)
    (P : Submodule ℝ E4) (v : E4) (q h bound : ℝ)
    (hq : 0 < q) (hh : 0 < h) (hbound : 0 ≤ bound)
    (htrans : q ≤ Metric.infDist v (P:Set E4)) (hv : ‖v‖ ≤ bound)
    (x z : E4) :
    (fiber mesh (fiber mesh A P z h) (Submodule.span ℝ {v}) x h).card ≤
      capacity mesh (4*h+(8*h/q)*bound) := by
  apply card_le_of_approximate_fibers _ hm P v q h bound hq hh hbound htrans hv x z
  · intro k hk
    exact (mem_filter.mp (mem_filter.mp hk).1).2
  · intro k hk
    exact (mem_filter.mp hk).2

/-- Explicit real bound when the fiber width is at most C mesh lengths and
the actual normalized slope vector has norm at most two. -/
lemma capacity_le_transverse_power {mesh h q C : ℝ}
    (hm : 0 < mesh) (hh : 0 < h) (hq : 0 < q) (hq1 : q ≤ 1)
    (hC : 1 ≤ C) (hwidth : h ≤ C*mesh) :
    (capacity mesh (4*h+(8*h/q)*2):ℝ) ≤ (41*C/q)^4 := by
  have hD : 0 ≤ 4*h+(8*h/q)*2 := by positivity
  have hR : (4*h+(8*h/q)*2)/mesh ≤ 20*C/q := by
    apply (div_le_div_iff₀ hm hq).mpr
    have hcancel : (8*h/q)*q=8*h := div_mul_cancel₀ _ hq.ne'
    have hsmall := mul_le_mul_of_nonneg_left hq1 (show 0 ≤ 4*h by positivity)
    nlinarith
  have hCq : 1 ≤ C/q := (le_div_iff₀ hq).mpr (by nlinarith)
  have hbase : 2*((4*h+(8*h/q)*2)/mesh)+1 ≤ 41*C/q := by
    calc
      _ ≤ 2*(20*C/q)+C/q := by linarith
      _ = _ := by ring
  exact (capacity_le_real hm hD).trans
    (pow_le_pow_left₀ (by positivity) hbase 4)

theorem intersection_card_le_transverse_power (A : Finset Index) {mesh : ℝ} (hm : 0 < mesh)
    (P : Submodule ℝ E4) (v : E4) (q h C : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hh : 0 < h) (hC : 1 ≤ C) (hwidth : h ≤ C*mesh)
    (htrans : q ≤ Metric.infDist v (P:Set E4)) (hv : ‖v‖ ≤ 2)
    (x z : E4) :
    ((fiber mesh (fiber mesh A P z h) (Submodule.span ℝ {v}) x h).card:ℝ) ≤ (41*C/q)^4 := by
  have hcount := intersection_card_le A hm P v q h 2 hq hh (by norm_num) htrans hv x z
  exact (show ((fiber mesh (fiber mesh A P z h) (Submodule.span ℝ {v}) x h).card:ℝ) ≤
    capacity mesh (4*h+(8*h/q)*2) by exact_mod_cast hcount).trans
    (capacity_le_transverse_power hm hh hq hq1 hC hwidth)

/-- Approximate affine membership is propagated through actual witnesses,
with its thickness explicitly enlarged. -/
lemma near_sup_of_two (P Q : Submodule ℝ E4) (x y a : E4) (h : ℝ) (hh : 0 < h)
    (ha : Metric.infDist (a-y) (P:Set E4) ≤ h)
    (hy : Metric.infDist (y-x) (Q:Set E4) ≤ h) :
    Metric.infDist (a-x) ((P⊔Q : Submodule ℝ E4):Set E4) ≤ 4*h := by
  obtain ⟨p,hp,hap⟩ := (Metric.infDist_lt_iff (show (P:Set E4).Nonempty from ⟨0,P.zero_mem⟩)).mp
    (ha.trans_lt (by linarith : h < 2*h))
  obtain ⟨q,hq,hyq⟩ := (Metric.infDist_lt_iff (show (Q:Set E4).Nonempty from ⟨0,Q.zero_mem⟩)).mp
    (hy.trans_lt (by linarith : h < 2*h))
  have hmem : p+q∈P⊔Q := (P⊔Q).add_mem ((show P ≤ P⊔Q from le_sup_left) hp)
    ((show Q ≤ P⊔Q from le_sup_right) hq)
  apply (Metric.infDist_le_dist_of_mem hmem).trans
  rw [dist_eq_norm] at hap hyq ⊢
  have he : (a-x)-(p+q)=((a-y)-p)+((y-x)-q) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

/-- The true predecessor incidences are counted with their geometrically
derived overlap. No predecessor count or overlap certificate is assumed. -/
theorem backward_fiber_sum_bound (A C : Finset Index) {mesh : ℝ} (hm : 0 < mesh)
    (P : Submodule ℝ E4) (v : E4) (q h bound : ℝ)
    (hq : 0 < q) (hh : 0 < h) (hbound : 0 ≤ bound)
    (htrans : q ≤ Metric.infDist v (P:Set E4)) (hv : ‖v‖ ≤ bound) (x : E4) :
    (∑y∈fiber mesh C (Submodule.span ℝ {v}) x h,(fiber mesh A P (cellCenter mesh y) h).card) ≤
      capacity mesh (4*h+(8*h/q)*bound)*(fiber mesh A (P⊔Submodule.span ℝ {v}) x (4*h)).card := by
  let B := fiber mesh C (Submodule.span ℝ {v}) x h
  let S := fiber mesh A (P⊔Submodule.span ℝ {v}) x (4*h)
  let F := fun y => fiber mesh A P (cellCenter mesh y) h
  have hsub : ∀y∈B,F y⊆S := by
    intro y hy a ha
    exact mem_filter.mpr ⟨(mem_filter.mp ha).1,near_sup_of_two P (Submodule.span ℝ {v}) x
      (cellCenter mesh y) (cellCenter mesh a) h hh (mem_filter.mp ha).2 (mem_filter.mp hy).2⟩
  have habove : ∀y∈B,S.bipartiteAbove (fun y a => a∈F y) y=F y := by
    intro y hy
    ext a
    constructor
    · intro ha
      exact (mem_filter.mp ha).2
    · intro ha
      exact mem_filter.mpr ⟨hsub y hy ha,ha⟩
  have hcount : ∀a∈S,(B.bipartiteBelow (fun y a => a∈F y) a).card ≤
      capacity mesh (4*h+(8*h/q)*bound) := by
    intro a _ha
    apply card_le_of_approximate_fibers _ hm P v q h bound hq hh hbound htrans hv x (cellCenter mesh a)
    · intro y hy
      have hnear := (mem_filter.mp (mem_filter.mp hy).2).2
      rwa [infDist_sub_comm] at hnear
    · intro y hy
      exact (mem_filter.mp (mem_filter.mp hy).1).2
  change (∑y∈B,(F y).card) ≤ capacity mesh (4*h+(8*h/q)*bound)*S.card
  calc
    _ = ∑y∈B,(S.bipartiteAbove (fun y a => a∈F y) y).card :=
      sum_congr rfl (fun y hy => congrArg card (habove y hy).symm)
    _ = ∑a∈S,(B.bipartiteBelow (fun y a => a∈F y) a).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun y a => a∈F y)
    _ ≤ ∑_a∈S,capacity mesh (4*h+(8*h/q)*bound) := sum_le_sum hcount
    _ = _ := by simp [Nat.mul_comm]

theorem backward_fiber_sum_bound_real (A C : Finset Index) {mesh : ℝ} (hm : 0 < mesh)
    (P : Submodule ℝ E4) (v : E4) (q h width : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hh : 0 < h) (hwidth : 1 ≤ width) (hmesh : h ≤ width*mesh)
    (htrans : q ≤ Metric.infDist v (P:Set E4)) (hv : ‖v‖ ≤ 2) (x : E4) :
    (∑y∈fiber mesh C (Submodule.span ℝ {v}) x h,((fiber mesh A P (cellCenter mesh y) h).card:ℝ)) ≤
      (41*width/q)^4*((fiber mesh A (P⊔Submodule.span ℝ {v}) x (4*h)).card:ℝ) := by
  have hn := backward_fiber_sum_bound A C hm P v q h 2 hq hh (by norm_num) htrans hv x
  have hreal : (∑y∈fiber mesh C (Submodule.span ℝ {v}) x h,((fiber mesh A P (cellCenter mesh y) h).card:ℝ)) ≤
      (capacity mesh (4*h+(8*h/q)*2):ℝ)*((fiber mesh A (P⊔Submodule.span ℝ {v}) x (4*h)).card:ℝ) := by
    exact_mod_cast hn
  exact hreal.trans (mul_le_mul_of_nonneg_right (capacity_le_transverse_power hm hh hq hq1 hwidth hmesh)
    (Nat.cast_nonneg _))

/-- This lower factor is computed from the actual predecessor fibers. -/
def minimumPredecessor (mesh : ℝ) (A B : Finset Index) (P : Submodule ℝ E4) (h : ℝ) : ℕ :=
  if hB : B.Nonempty then
    (B.image (fun y => (fiber mesh A P (cellCenter mesh y) h).card)).min' (hB.image _)
  else 0

lemma minimumPredecessor_le (mesh : ℝ) (A B : Finset Index) (P : Submodule ℝ E4) (h : ℝ)
    (y : Index) (hy : y∈B) :
    minimumPredecessor mesh A B P h ≤ (fiber mesh A P (cellCenter mesh y) h).card := by
  have hB : B.Nonempty := ⟨y,hy⟩
  simp only [minimumPredecessor,dif_pos hB]
  exact min'_le _ _ (mem_image_of_mem _ hy)

/-- An actual multiplication step, with a computed minimum predecessor size
and a proved overlap denominator, rather than supplied numerical certificates. -/
theorem backward_fiber_step (A C : Finset Index) {mesh : ℝ} (hm : 0 < mesh)
    (P : Submodule ℝ E4) (v : E4) (q h bound : ℝ)
    (hq : 0 < q) (hh : 0 < h) (hbound : 0 ≤ bound)
    (htrans : q ≤ Metric.infDist v (P:Set E4)) (hv : ‖v‖ ≤ bound) (x : E4) :
    (fiber mesh C (Submodule.span ℝ {v}) x h).card *
        minimumPredecessor mesh A (fiber mesh C (Submodule.span ℝ {v}) x h) P h ≤
      capacity mesh (4*h+(8*h/q)*bound)*(fiber mesh A (P⊔Submodule.span ℝ {v}) x (4*h)).card := by
  calc
    _ = ∑y∈fiber mesh C (Submodule.span ℝ {v}) x h,
        minimumPredecessor mesh A (fiber mesh C (Submodule.span ℝ {v}) x h) P h := by simp
    _ ≤ ∑y∈fiber mesh C (Submodule.span ℝ {v}) x h,(fiber mesh A P (cellCenter mesh y) h).card :=
      sum_le_sum (fun y hy => minimumPredecessor_le _ _ _ _ _ y hy)
    _ ≤ _ := backward_fiber_sum_bound A C hm P v q h bound hq hh hbound htrans hv x

end NativeApproximateFiberCount
