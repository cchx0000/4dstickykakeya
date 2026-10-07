import Theorems.Thm_StickyKakeya4_native_slice_count_comparison
import Theorems.Thm_StickyKakeya4_native_slice_grid_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeSliceClassBalls
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeAnisotropicSliceLabels NativeAnisotropicShortRowGeometry
open NativeSliceCountComparison
open scoped BigOperators

def preparedClass (P : Finset Index) (fine coarse : ℕ) (u : Index) : Finset Index :=
  P.filter (fun v => horizontalCoarsen fine coarse v=horizontalCoarsen fine coarse u)

def spatialBall (P : Finset Index) (R : ℕ) (u : Index) : Finset Index :=
  P.filter (fun v => v (3:Fin 4)=u (3:Fin 4) ∧
    ∀i : Fin 3,|v i.castSucc-u i.castSucc|≤(R:ℤ))

/-- Literal centers of horizontal grid cells, in the standard sup metric
on Fin3→R. Height remains a separate fixed integer label. -/
def realized (mu : ℝ) (u : Index) : Fin 3 → ℝ :=
  fun i => mu*((u i.castSucc:ℝ)+1/2)

def realizedSlice (P : Finset Index) (mu : ℝ) (height : ℤ) : Finset (Fin 3 → ℝ) :=
  (heightSlice P height).image (realized mu)

lemma realized_injective_on_height {mu : ℝ} (hmu : 0 < mu) {x y : Index}
    (hh : x (3:Fin 4)=y (3:Fin 4)) (he : realized mu x=realized mu y) : x=y := by
  funext i
  refine Fin.lastCases hh (fun j => ?_) i
  have hj := congrFun he j
  dsimp only [realized] at hj
  have hr : (x j.castSucc:ℝ)=(y j.castSucc:ℝ) := by nlinarith only [hj,hmu]
  exact_mod_cast hr

lemma realized_dist_iff {mu : ℝ} (hmu : 0 < mu) (R : ℕ) (x y : Index) :
    dist (realized mu x) (realized mu y) ≤ mu*(R:ℝ) ↔
      ∀i : Fin 3,|x i.castSucc-y i.castSucc|≤(R:ℤ) := by
  rw [dist_pi_le_iff (by positivity)]
  constructor
  · intro H i
    have hi := H i
    rw [Real.dist_eq] at hi
    have he : realized mu x i-realized mu y i=mu*((x i.castSucc:ℝ)-(y i.castSucc:ℝ)) := by
      dsimp [realized];ring
    rw [he,abs_mul,abs_of_pos hmu] at hi
    have hh := (mul_le_mul_iff_right₀ hmu).mp hi
    exact_mod_cast hh
  · intro H i
    rw [Real.dist_eq]
    have he : realized mu x i-realized mu y i=mu*((x i.castSucc:ℝ)-(y i.castSucc:ℝ)) := by
      dsimp [realized];ring
    rw [he,abs_mul,abs_of_pos hmu]
    apply mul_le_mul_of_nonneg_left _ hmu.le
    exact_mod_cast H i

lemma realized_ball_card (P : Finset Index) {mu : ℝ} (hmu : 0 < mu) (R : ℕ) (u : Index) :
    ((realizedSlice P mu (u (3:Fin 4))).filter
      (fun x => dist x (realized mu u) ≤ mu*(R:ℝ))).card=(spatialBall P R u).card := by
  have he : (realizedSlice P mu (u (3:Fin 4))).filter
      (fun x => dist x (realized mu u) ≤ mu*(R:ℝ))=
        (spatialBall P R u).image (realized mu) := by
    ext x
    simp only [realizedSlice,heightSlice,spatialBall,mem_filter,mem_image]
    constructor
    · rintro ⟨⟨v,⟨hv,hh⟩,rfl⟩,hd⟩
      exact ⟨v,⟨hv,hh,(realized_dist_iff hmu R v u).mp hd⟩,rfl⟩
    · rintro ⟨v,⟨hv,hh,hd⟩,rfl⟩
      exact ⟨⟨v,⟨hv,hh⟩,rfl⟩,(realized_dist_iff hmu R v u).mpr hd⟩
  rw [he]
  apply card_image_iff.mpr
  intro x hx y hy hxy
  exact realized_injective_on_height hmu
    ((mem_filter.mp hx).2.1.trans (mem_filter.mp hy).2.1.symm) hxy

lemma preparedClass_subset_ball (P : Finset Index) (fine coarse : ℕ) (u : Index) :
    preparedClass P fine coarse u⊆spatialBall P (2^(fine-coarse)) u := by
  intro v hv
  obtain ⟨hvP,he⟩ := mem_filter.mp hv
  refine mem_filter.mpr ⟨hvP,?_,?_⟩
  · simpa only [horizontalCoarsen_height] using congrFun he (3:Fin 4)
  · have hbox := GridQuotientAD.same_cell_close 0 (2^(fine-coarse))
      (fun i : Fin 3 => v i.castSucc) (fun i : Fin 3 => u i.castSucc)
      (by exact Nat.succ_le_of_lt (show 0 < (2:ℕ)^(fine-coarse) by positivity)) (by
        funext i
        have hi := congrFun he i.castSucc
        have hi3 : (i.castSucc:Fin 4)≠3 := Fin.castSucc_ne_last i
        simpa only [GridQuotientAD.cellKey,Nat.cast_zero,add_zero,horizontalCoarsen,hi3,if_false] using hi)
    exact (GridQuotientAD.mem_box_iff _ _ _).mp hbox

lemma ball_class_mem_halo (P : Finset Index) (fine coarse : ℕ) (u v : Index)
    (hv : v∈spatialBall P (2^(fine-coarse)) u) :
    horizontalCoarsen fine coarse v∈columnHalo 1 0 (horizontalCoarsen fine coarse u) := by
  obtain ⟨_hvP,hh,hspace⟩ := mem_filter.mp hv
  apply Fintype.mem_piFinset.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change v (3:Fin 4)∈Icc (u (3:Fin 4)-(0:ℤ)) (u (3:Fin 4)+0)
    simp only [sub_zero,add_zero,mem_Icc]
    exact ⟨hh.ge,hh.le⟩
  · have hclose := NativeSliceGridGeometry.abs_ediv_sub_ediv_le_one (2^(fine-coarse))
      (v j.castSucc) (u j.castSucc) (by positivity) (hspace j)
    have hj3 : (j.castSucc:Fin 4)≠3 := Fin.castSucc_ne_last j
    simp only [horizontalCoarsen,hj3,if_false,Nat.cast_one,mem_Icc]
    obtain ⟨hl,hu⟩ := abs_le.mp hclose
    constructor <;> omega

/-- A spatial ball at one prepared scale meets at most27 horizontal classes,
with the original height coordinate unchanged. -/
lemma ball_class_card_le (P : Finset Index) (fine coarse : ℕ) (u : Index) :
    ((spatialBall P (2^(fine-coarse)) u).image (horizontalCoarsen fine coarse)).card ≤ 27 := by
  have hs : (spatialBall P (2^(fine-coarse)) u).image (horizontalCoarsen fine coarse)⊆
      columnHalo 1 0 (horizontalCoarsen fine coarse u) := by
    intro q hq
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hq
    exact ball_class_mem_halo P fine coarse u v hv
  have hh := card_le_card hs
  rw [columnHalo_card] at hh
  norm_num at hh
  exact hh

/-- Actual occupied-class upper bounds control the prepared spatial ball;
there is no assumption about the center being away from grid boundaries. -/
theorem prepared_ball_upper (P : Finset Index) (fine coarse : ℕ) (u : Index)
    (U : ℝ) (hU : 0 ≤ U)
    (H : ∀v∈P,((preparedClass P fine coarse v).card:ℝ)≤U) :
    ((spatialBall P (2^(fine-coarse)) u).card:ℝ) ≤ 27*U := by
  let A := spatialBall P (2^(fine-coarse)) u
  have hc := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
    A id (horizontalCoarsen fine coarse) U (by
      intro c hc
      obtain ⟨v,hv,hvc⟩ := mem_image.mp hc
      rw [image_id]
      have hs : A.filter (fun x => horizontalCoarsen fine coarse x=c)⊆preparedClass P fine coarse v := by
        intro x hx
        obtain ⟨hxA,hxc⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨(mem_filter.mp hxA).1,hxc.trans hvc.symm⟩
      exact (Nat.cast_le.mpr (card_le_card hs)).trans (H v (mem_filter.mp hv).1))
  rw [image_id] at hc
  exact hc.trans (by
    calc
      U*((A.image (horizontalCoarsen fine coarse)).card:ℝ) ≤ U*27 :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (ball_class_card_le P fine coarse u)) hU
      _ = _ := mul_comm _ _)

/-- Physical horizontal cell centers inherit both prepared-scale ball counts
from the source-derived class bounds. The metric here is the sup metric. -/
theorem prepared_real_ball_bounds (P : Finset Index) {mu : ℝ} (hmu : 0 < mu)
    (fine coarse : ℕ) (u : Index) (hu : u∈P) (L U s : ℝ) (hU : 0 ≤ U)
    (Hlo : ∀v∈P,L*((2^(fine-coarse):ℕ):ℝ)^s ≤ (preparedClass P fine coarse v).card)
    (Hhi : ∀v∈P,((preparedClass P fine coarse v).card:ℝ) ≤ U*((2^(fine-coarse):ℕ):ℝ)^s) :
    L*((2^(fine-coarse):ℕ):ℝ)^s ≤
      ((realizedSlice P mu (u (3:Fin 4))).filter (fun x =>
        dist x (realized mu u) ≤ mu*((2^(fine-coarse):ℕ):ℝ))).card ∧
    (((realizedSlice P mu (u (3:Fin 4))).filter (fun x =>
        dist x (realized mu u) ≤ mu*((2^(fine-coarse):ℕ):ℝ))).card:ℝ) ≤
      27*U*((2^(fine-coarse):ℕ):ℝ)^s := by
  rw [realized_ball_card P hmu]
  constructor
  · exact (Hlo u hu).trans (Nat.cast_le.mpr (card_le_card (preparedClass_subset_ball P fine coarse u)))
  · have hh := prepared_ball_upper P fine coarse u (U*((2^(fine-coarse):ℕ):ℝ)^s) (by positivity) Hhi
    simpa only [mul_assoc] using hh

end NativeSliceClassBalls
